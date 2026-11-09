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

(* A structure is a signature plus its record of values.  Modules save
   only the record's theorems, not the compiled structure (whose code,
   closures and mutable cells would make every module mutable and
   several times larger), and rebuild the structure on a warm load.
   Poly/ML builds structures from a signature and a record only in its
   debugger's name spaces; this mirrors the debugger's entry type to
   reach that.  The mirror must have the same constructors, in the same
   order and with the same arities, as Poly/ML's environEntry. *)
local
  type w = PolyML.CodeTree.machineWord
  datatype entry =
      EnvEndFunction of string * PolyML.location * w
    | EnvException of string * w * bool * unit list
    | EnvStartFunction of string * PolyML.location * w
    | EnvStructure of string * w * unit list
    | EnvTConstr of string * w
    | EnvTypeid of w * w
    | EnvVConstr of string * w * bool * int * unit list
    | EnvValue of string * w * unit list
  val nowhere = {file = "", startLine = 0, startPosition = 0,
                 endLine = 0, endPosition = 0}
in
fun make_structure (name, signature_value, record : w) =
  let
    val state : entry list * w list * PolyML.location =
        ([EnvStructure (name, RunCall.unsafeCast signature_value, [])],
         [record], nowhere)
    val space = PolyML.DebuggerInterface.debugNameSpace
                  (RunCall.unsafeCast state)
  in
    #lookupStruct space name
  end
end

(* A structure's values in the order of the record its signature
   describes, or NONE if one isn't a constant.  The compiled record can
   hold more than the signature's values (with an opaque signature that
   leaves no values, it can be the whole unascribed structure), so this
   reads each value out and finds its place by rebuilding the structure
   over a record of field numbers. *)
fun signature_values (name, signature_value, structure_value) =
  let
    fun value_of v =
      PolyML.CodeTree.evalue (PolyML.NameSpace.Values.code v)
    fun values_of s = #allVal (PolyML.NameSpace.Structures.contents s) ()
    val values = values_of structure_value
    val n = length values
    val numbers : int vector = Vector.tabulate (n, fn i => i)
    val record = Array.array (n, NONE)
    fun place (value_name, v) =
      case (value_of v,
            List.find (fn (m, _) => m = value_name) values) of
          (SOME w, SOME (_, original)) =>
          let val i : int = RunCall.unsafeCast w
          in
            if 0 <= i andalso i < n andalso
               not (Option.isSome (Array.sub (record, i)))
            then Array.update (record, i, value_of original)
            else raise Fail "field"
          end
        | _ => raise Fail "field"
  in
    case make_structure (name, signature_value, RunCall.unsafeCast numbers) of
        NONE => NONE
      | SOME numbered =>
        (List.app place (values_of numbered);
         SOME (Vector.tabulate (n, fn i => valOf (Array.sub (record, i)))))
  end
  handle Fail _ => NONE | Option => NONE

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
   uses whatever they are bound to now.  A warm load uses the ones bound
   when this file was compiled, so modules are used and saved only while
   the current bindings are those, and a module is used only with the
   bindings it was saved under. *)
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

val compiled_bindings = core_bindings ()
fun unchanged_bindings () = same_bindings compiled_bindings

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
  case TheoryReader.phase "verify_ref" (verified_payload directory) key of
      NONE => NONE
    | SOME payload =>
      let
        val (roots, id) = TheoryReader.phase "loadModule" Save.loadModuleBasic payload
        fun discard () = (Save.releaseModule id; NONE)
      in
        case roots of
            signature_root :: structure_root :: data_root :: guards =>
            if Universal.tagIs Tags.signatureTag signature_root andalso
               Universal.tagIs TheoryReader.values_tag structure_root andalso
               Universal.tagIs TheoryReader.decoded_tag data_root andalso
               List.all (Universal.tagIs Tags.structureTag) guards
            then
              let
                val signature_value as (signature_name, _) =
                    Universal.tagProject Tags.signatureTag signature_root
                val values as (structure_name, _) =
                    Universal.tagProject TheoryReader.values_tag
                                         structure_root
              in
                if signature_name = name andalso structure_name = name then
                  SOME {signature_value = signature_value,
                        values = values,
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

(* Modules waiting to be written.  Decoded terms come back without the
   sharing the .dat file had, and sharing them again makes modules
   several times smaller; but each sharing pass costs a full GC, so all
   the modules a process produces are shared in one pass and written
   together, by flush or at exit. *)
val unsaved : (string * string * Word8Vector.vector * Universal.universal list)
                list ref = ref []

fun flush () =
  let
    val modules = rev (!unsaved)
    val _ = unsaved := []
  in
    if null modules then ()
    else
      (PolyML.shareCommonData (map #4 modules);
       List.app (fn (directory, key, base_id, roots) =>
                    save_module directory key base_id roots
                    handle IO.Io _ => () | OS.SysErr _ => () | Fail _ => ())
                modules)
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
      values : string * Thm.thm vector,
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
            (TheoryReader.phase "enterSig" (#enterSig namespace) (#signature_value m);
             pending := (base, m) :: !pending)
  end

fun warm_load file thy ({signature_value, values, data, ...} : module) =
  let
    val name = #1 values
    val structure_value =
        case TheoryReader.phase "make_structure" make_structure (name, #2 signature_value,
                             RunCall.unsafeCast (#2 values)) of
            SOME s => s
          | NONE => raise Fail ("cannot rebuild structure " ^ name)
    val path = OS.Path.base file ^ ".dat"
    val _ = if !Globals.print_thy_loads
            then TextIO.print ("Loading " ^ name ^ " ... ") else ()
    val _ = TheoryReader.phase "register_decoded" TheoryReader.register_decoded data
    val _ = TheoryReader.phase "record_metadata" (Theory.record_metadata thy)
              {timestamp = HOLFileSys.modTime path, path = path}
    val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
    val _ = TheoryReader.phase "load_complete" Theory.load_complete thy
  in
    TheoryReader.phase "enterStruct" (#enterStruct namespace) (name, structure_value);
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
        (case signature_values (name, sigv, strv) of
           NONE => ()
         | SOME words =>
        let
          (* only theorems: generated theory signatures declare nothing
             else *)
          val values : Thm.thm vector = RunCall.unsafeCast words
        in
        if TheoryReader.decoded_name data = thy andalso
           TheoryReader.is_canonical thy andalso unchanged_bindings ()
        then
          unsaved :=
            (directory, key, base_id,
             Universal.tagInject Tags.signatureTag (name, sigv) ::
             Universal.tagInject TheoryReader.values_tag (name, values) ::
             Universal.tagInject TheoryReader.decoded_tag data ::
             map (fn b => Universal.tagInject Tags.structureTag ("", b))
                 bindings) :: !unsaved
        else ()
        end)
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
        if unchanged_bindings () andalso same_bindings bindings andalso
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

val _ = OS.Process.atExit flush

val _ = Meta.moduleCacheConfigure := SOME configure

end
