(* Theory value modules.  The first source load of a theory in a process
   saves what it built: the theory's signature and structure, and the
   decoded .dat data (TheoryReader.decoded).  A later load in any
   process started from the same saved state installs them and repeats
   only the registration, without compiling the generated ML or reading
   the .dat.  This relies on loaded theories' kernel ids being canonical
   (KernelSig.insert_sealed): saved terms and theorems then mean the
   same thing in every such process, whatever was loaded before. *)
structure TheoryModules =
struct

structure Save = PolyML.SaveState
structure Tags = Save.Tags
val namespace = PolyML.globalNameSpace

val hits = ref 0
val misses = ref 0
val writes = ref 0
fun statistics () = {hits = !hits, misses = !misses, writes = !writes}

fun read_text path =
  let val input = TextIO.openIn path
  in TextIO.inputAll input before TextIO.closeIn input end

fun write_text path text =
  let val output = TextIO.openOut path
  in TextIO.output (output, text) before TextIO.closeOut output end

fun digest text =
  let
    fun read (offset, count) =
      let val n = Int.min (count, String.size text - offset)
      in (Byte.stringToBytes (String.substring (text, offset, n)), offset+n)
      end
  in
    SHA1.sha1String read 0
  end

fun mkdir path =
  (if OS.FileSys.isDir path then ()
   else raise Fail ("not a directory: " ^ path))
  handle OS.SysErr _ =>
    (if OS.Path.dir path = path then () else mkdir (OS.Path.dir path);
     OS.FileSys.mkDir path
       handle e as OS.SysErr _ =>
         if OS.FileSys.isDir path then () else raise e)

val serial = ref 0
fun temporary directory =
  let
    val n = !serial before serial := !serial + 1
    val pid = SysWord.toString
                (Posix.Process.pidToWord (Posix.ProcEnv.getpid ()))
  in
    OS.Path.concat (directory, "tmp-" ^ pid ^ "-" ^ Int.toString n)
  end

fun remove path = OS.FileSys.remove path handle OS.SysErr _ => ()

(* The generated theory source refers to these structures; a source load
   uses whatever they are bound to now, so a module made with other
   bindings is not used. *)
val required_structures =
  ["General", "Globals", "TextIO", "OS", "Option", "Type", "Term", "Thm",
   "HOLFileSys", "TheoryReader", "Symtab", "Theory"]

fun core_bindings () =
  map (fn name =>
         case #lookupStruct namespace name of
             SOME value => value
           | NONE => raise Fail ("missing structure " ^ name))
      required_structures

fun same_bindings bindings =
  ListPair.allEq
    (fn (name, value) =>
       case #lookupStruct namespace name of
           SOME current => PolyML.pointerEq (current, value)
         | NONE => false)
    (required_structures, bindings)

(* The theory name and .dat hash a generated FooTheory.sml loads; the
   source loader identifies the theory by the same literals. *)
fun sml_header file =
  let
    val input = HOLFileSys.openIn file
    val text = TextIO.inputN (input, 4096) before HOLFileSys.closeIn input
    fun literal key =
      let
        val (_, rest) = Substring.position key (Substring.full text)
        val rest = Substring.triml (String.size key) rest
        val (value, close) = Substring.splitl (fn c => c <> #"\"") rest
      in
        if Substring.isEmpty close then NONE
        else SOME (Substring.string value)
      end
  in
    case (literal "thyname = \"", literal "hash = \"") of
        (SOME thy, SOME hash) => SOME (thy, hash)
      | _ => NONE
  end

(* A module's .ref file records the payload's SHA-1 and its file status
   when last checked: the payload is rehashed only when that status
   differs, or when it was modified within a second of the check. *)
fun file_status path =
  let
    val st = Posix.FileSys.stat path
  in
    String.concatWith " "
      [Position.toString (Posix.FileSys.ST.size st),
       LargeInt.toString (Time.toNanoseconds (Posix.FileSys.ST.mtime st)),
       LargeInt.toString (Time.toNanoseconds (Posix.FileSys.ST.ctime st)),
       SysWord.toString (Posix.FileSys.inoToWord (Posix.FileSys.ST.ino st))]
  end

fun racy path =
  Time.>= (Time.+ (Posix.FileSys.ST.mtime (Posix.FileSys.stat path),
                   Time.fromSeconds 1),
           Time.now ())

fun write_reference directory key hash payload =
  let
    val tmp = temporary directory
  in
    write_text tmp (hash ^ "\n" ^ file_status payload ^ "\n");
    OS.FileSys.rename {old = tmp,
                       new = OS.Path.concat (directory, key ^ ".ref")}
  end

fun verified_payload directory key =
  let
    val payload = OS.Path.concat (directory, key ^ ".pmo")
    val lines = String.tokens (fn c => c = #"\n")
                  (read_text (OS.Path.concat (directory, key ^ ".ref")))
  in
    case lines of
        [hash, status] =>
          if status = file_status payload andalso not (racy payload) then
            SOME payload
          else if SHA1.sha1_file {filename = payload} = hash then
            ((if racy payload then ()
              else write_reference directory key hash payload)
               handle IO.Io _ => () | OS.SysErr _ => ();
             SOME payload)
          else NONE
      | _ => NONE
  end
  handle IO.Io _ => NONE
       | OS.SysErr _ => NONE

fun read_module directory key name =
  case verified_payload directory key of
      NONE => NONE
    | SOME payload =>
      let
        val (roots, id) = Save.loadModuleBasic payload
        fun discard () = (Save.releaseModule id; NONE)
      in
        case roots of
            signature_root :: structure_root :: data_root :: guards =>
            if Universal.tagIs Tags.signatureTag signature_root andalso
               Universal.tagIs Tags.structureTag structure_root andalso
               Universal.tagIs TheoryReader.decoded_tag data_root andalso
               List.all (Universal.tagIs Tags.structureTag) guards
            then
              let
                val signature_value as (signature_name, _) =
                    Universal.tagProject Tags.signatureTag signature_root
                val structure_value as (structure_name, _) =
                    Universal.tagProject Tags.structureTag structure_root
              in
                if signature_name = name andalso structure_name = name then
                  SOME {signature_value = signature_value,
                        structure_value = structure_value,
                        data = Universal.tagProject TheoryReader.decoded_tag
                                                    data_root,
                        bindings = map (#2 o Universal.tagProject
                                               Tags.structureTag) guards}
                else discard ()
              end
            else discard ()
          | _ => discard ()
      end
      handle Fail _ => NONE

fun save_module directory key base_id roots =
  let
    val tmp = temporary directory
  in
    (ignore (Save.saveDependentModuleBasic (tmp, roots, [(base_id, "")]));
     let
       val hash = SHA1.sha1_file {filename = tmp}
       val payload = OS.Path.concat (directory, key ^ ".pmo")
     in
       OS.FileSys.rename {old = tmp, new = payload};
       write_reference directory key hash payload;
       writes := !writes + 1
     end)
    handle e => (remove tmp; PolyML.Exception.reraise e)
  end

fun theory_file file =
  case OS.Path.ext file of
      SOME "sml" => String.isSuffix "Theory.sml" file
    | SOME "sig" => String.isSuffix "Theory.sig" file
    | _ => false

fun eligible () =
  (Thm.kernelid = "stdknl" orelse Thm.kernelid = "expknl") andalso
  TheoryReader.default_loader ()

(* Modules whose signature has been installed, waiting for their
   structure's source file. *)
type module =
     {signature_value : string * PolyML.NameSpace.Signatures.signatureVal,
      structure_value : string * PolyML.NameSpace.Structures.structureVal,
      data : TheoryReader.decoded,
      bindings : PolyML.NameSpace.Structures.structureVal list}
val pending : (string * module) list ref = ref []

fun take_pending base =
  case List.partition (fn (b, _) => b = base) (!pending) of
      ([], _) => NONE
    | ((_, m) :: _, rest) => (pending := rest; SOME m)

fun module_key base_id file =
  Option.map
    (fn (thy, hash) =>
        (thy, digest ("hol-theory-values-v1\000" ^ Byte.bytesToString base_id ^
                      "\000" ^ thy ^ "\000" ^ hash)))
    (sml_header (OS.Path.base file ^ ".sml"))
  handle IO.Io _ => NONE
       | OS.SysErr _ => NONE

fun load_signature directory base_id use file =
  let
    val base = OS.Path.base file
    val name = OS.Path.file base
  in
    case module_key base_id file of
        NONE => use file
      | SOME (thy, key) =>
        case read_module directory key name of
            NONE => use file
          | SOME m =>
            (#enterSig namespace (#signature_value m);
             pending := (base, m) :: !pending)
  end

fun warm_load file thy ({structure_value, data, ...} : module) =
  let
    val name = #1 structure_value
    val path = OS.Path.base file ^ ".dat"
    val _ = if !Globals.print_thy_loads
            then TextIO.print ("Loading " ^ name ^ " ... ") else ()
    val _ = TheoryReader.register_decoded data
    val _ = Theory.record_metadata thy
              {timestamp = HOLFileSys.modTime path, path = path}
    val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
    val _ = Theory.load_complete thy
  in
    #enterStruct namespace structure_value;
    hits := !hits + 1
  end

fun cold_load directory base_id use file =
  let
    val name = OS.Path.file (OS.Path.base file)
    val bindings = core_bindings ()
    val _ = misses := !misses + 1
    val (_, data) = TheoryReader.capture_decoded use file
  in
    case (data, module_key base_id file,
          #lookupSig namespace name, #lookupStruct namespace name) of
        (SOME data, SOME (thy, key), SOME sigv, SOME strv) =>
        if TheoryReader.decoded_name data = thy andalso
           TheoryReader.is_canonical thy
        then
          save_module directory key base_id
            (Universal.tagInject Tags.signatureTag (name, sigv) ::
             Universal.tagInject Tags.structureTag (name, strv) ::
             Universal.tagInject TheoryReader.decoded_tag data ::
             map (fn b => Universal.tagInject Tags.structureTag ("", b))
                 bindings)
          handle IO.Io _ => () | OS.SysErr _ => () | Fail _ => ()
        else ()
      | _ => ()
  end

fun load_structure directory base_id use file =
  case take_pending (OS.Path.base file) of
      NONE => cold_load directory base_id use file
    | SOME (m as {data, bindings, ...} : module) =>
      let
        val thy = TheoryReader.decoded_name data
      in
        (* Checks before any registration; past them nothing is retried
           from source, since load hooks may already have run. *)
        if same_bindings bindings andalso
           List.all TheoryReader.is_canonical
                    (TheoryReader.decoded_parents data)
        then warm_load file thy m
        else cold_load directory base_id use file
      end

fun load_source directory base_id use file =
  if not (theory_file file) orelse not (eligible ()) then use file
  else if OS.Path.ext file = SOME "sig" then
    load_signature directory base_id use file
  else load_structure directory base_id use file

fun configure {directory, base_state} =
  let
    val _ = Meta.moduleSourceLoader := (fn use => use)
    val directory = OS.Path.mkAbsolute
                      {path = directory, relativeTo = OS.FileSys.getDir ()}
    fun same_state (_, path) =
      OS.FileSys.fullPath path = OS.FileSys.fullPath base_state
  in
    case List.find same_state (Save.showHierarchyWithIds ()) of
        NONE => false
      | SOME (base_id, _) =>
        (mkdir directory;
         Meta.moduleSourceLoader := load_source directory base_id;
         true)
  end
  handle IO.Io _ => false
       | OS.SysErr _ => false
       | Fail _ => false

val _ = Meta.moduleCacheConfigure := SOME configure

end
