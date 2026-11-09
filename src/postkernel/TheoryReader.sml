(* ========================================================================== *)
(* FILE          : TheoryReader.sml                                           *)
(* DESCRIPTION   : Read theory data from disk                                 *)
(*                                                                            *)
(* AUTHOR        : Thibault Gauthier, University of Innsbruck                 *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure TheoryReader :> TheoryReader =
struct

type thm      = Thm.thm;
type term     = Term.term
type hol_type = Type.hol_type

open HolKernel SharingTables RawTheory_dtype RawTheoryReader

val phase_table : (string * (Time.time ref * Time.time ref * int ref)) list ref = ref []
fun phase name f x =
  let
    val t = Timer.startCPUTimer ()
    fun stop () =
      let
        val {nongc, gc} = Timer.checkCPUTimes t
        val (a, b, c) =
            case List.find (fn (n, _) => n = name) (!phase_table) of
                SOME (_, r) => r
              | NONE => let val r = (ref Time.zeroTime, ref Time.zeroTime, ref 0)
                        in phase_table := (name, r) :: !phase_table; r end
      in
        a := Time.+ (!a, Time.+ (#usr nongc, #sys nongc));
        b := Time.+ (!b, Time.+ (#usr gc, #sys gc));
        c := !c + 1
      end
  in
    (f x before stop ()) handle e => (stop (); raise e)
  end
fun phase_report () =
  map (fn (n, (a, b, c)) => (n, !a, !b, !c)) (rev (!phase_table))

fun temp_encoded_update (strings, terms) thyname {data,ty} =
    Theory.LoadableThyData.temp_encoded_update {
      thy = thyname,
      thydataty = ty,
      shared_readmaps = {strings = fn i => Vector.sub (strings, i),
                         terms = Term.read_raw terms},
      data = data
    }


(* A theory's data as decoded from its .dat file, with the values the
   source loader built: enough to repeat its registration without
   reading or decoding the file again: the shared strings and terms
   the theory data refers to, not the whole sharing table. *)
type decoded = {thyname : string, hash : string,
                parents : (string * string) list,
                new_types : (string * int) list,
                new_consts : (string * hol_type) list,
                strings : string vector, terms : term vector,
                theorems : (string * thm * DB_dtype.thminfo) list,
                thydata : {data : HOLsexp.t, ty : string} list}

val decoded_tag : decoded MLSYSPortable.persistent_tag =
    MLSYSPortable.new_persistent_tag ()
val values_tag : (string * thm vector) MLSYSPortable.persistent_tag =
    MLSYSPortable.new_persistent_tag ()

fun decoded_name ({thyname,...} : decoded) = thyname
fun decoded_parents ({parents,...} : decoded) = map #1 parents

(* Theories whose kernel ids are the same in every process sharing the
   saved state: those in it ("min" is built by the kernel itself) and
   theories loaded with canonical stamps whose parents are canonical. *)
val canonical_thys : string HOLset.set Sref.t =
    Sref.new (HOLset.singleton String.compare "min")
fun is_canonical thy = HOLset.member (Sref.value canonical_thys, thy)
fun note_load thyname parents stamps_canonical =
    if stamps_canonical andalso List.all (is_canonical o #1) parents then
      Sref.update canonical_thys (fn s => HOLset.add (s, thyname))
    else ()

(* The rest of a load, once the theory's types and constants exist. *)
fun bind_data ({thyname,strings,terms,theorems,thydata,...} : decoded) =
    (phase "DB.bindl" (DB.bindl thyname) theorems;
     phase "thydata_update" (app (temp_encoded_update (strings, terms) thyname)) thydata;
     theorems)

val capture = ref false
val captured : decoded option ref = ref NONE

fun load_thydata_from_dat (r as {thyname,path,hash}) =
    let
      open HOLsexp
      val rawthy as {parents,tables,exports,name=stored_name,...} =
            phase "read_dat" load_raw_thydata {path=path}
      fun mungename {thy,hash} = (thy,hash)
      val _ = thyname = stored_name orelse
              raise TheoryReader
                    ("reading at " ^ path ^ " for theory " ^ thyname ^
                     " and got theory called " ^ stored_name ^ " instead")
      val parents = map mungename parents
      val _ = phase "link_parents" (Theory.link_parents (thyname, hash)) parents
      val {types=new_types,consts=new_consts} = #newsig rawthy
      val stamps = ref true
      val consts = ref []
      fun before_types () =
          stamps := phase "incorporate" (Theory.incorporate_types thyname) new_types
      fun before_terms tyv =
          let
            val cs = map (fn (n,i) => (n,Vector.sub(tyv,i))) new_consts
          in
            consts := cs;
            stamps := (phase "incorporate" (Theory.incorporate_consts thyname) cs andalso !stamps)
          end
      val share_data =
            phase "dec_sdata" dec_sdata {
              before_types = before_types,
              before_terms = before_terms,
              tables = tables,
              exports = exports
            }
      val thydata =
          force "thydata" (
            Option.map (map (fn (ty,d) => {data=d,ty=ty})) o
            list_decode(pair_decode(string_decode, SOME))
          )
          (#thydata rawthy)
      val (strings, terms) = shared_vectors share_data
      val {theorems, ...} = export_from_sharing_data share_data
      val d = {thyname = thyname, hash = hash, parents = parents,
               new_types = new_types, new_consts = !consts,
               strings = strings, terms = terms, theorems = theorems,
               thydata = thydata}
      val named_thms = bind_data d
      val _ = note_load thyname parents (!stamps)
      val _ = if !capture then captured := SOME d else ()
  in
    List.foldl (fn ((n,th,i), D) => Symtab.update (n, (th,i)) D)
               Symtab.empty
               named_thms
  end handle Interrupt => raise Interrupt
           | e => raise TheoryReader ("Exception raised: " ^
                                      General.exnMessage e)

fun capture_decoded f x =
    let
      val _ = capture := true
      val _ = captured := NONE
      val result = (f x handle e => (capture := false; captured := NONE;
                                     raise e))
      val d = !captured
    in
      capture := false; captured := NONE; (result, d)
    end

(* Repeats load_thydata_from_dat's registration in the same order. The
   decoded values carry canonical stamps, so this theory's entries must
   get them again here. *)
fun register_decoded (d as {thyname,hash,parents,new_types,new_consts,...}
                      : decoded) =
    let
      val _ = phase "link_parents" (Theory.link_parents (thyname, hash)) parents
      val types_ok = phase "incorporate" (Theory.incorporate_types thyname) new_types
      val consts_ok = phase "incorporate" (Theory.incorporate_consts thyname) new_consts
      val _ = types_ok andalso consts_ok orelse
              raise TheoryReader ("theory " ^ thyname ^
                                  ": kernel entries not canonically stamped")
    in
      ignore (bind_data d);
      note_load thyname parents true
    end handle Interrupt => raise Interrupt
             | e as TheoryReader _ => raise e
             | e => raise TheoryReader ("Exception raised: " ^
                                        General.exnMessage e)

(* Hook for alternative theorem sources. Default is to read from .dat files. *)
val load_thydata_fn :
    ({thyname:string,path:string,hash:string} ->
     (Thm.thm * DB_dtype.thminfo) Symtab.table) ref
    = ref load_thydata_from_dat

fun load_thydata args = (!load_thydata_fn) args

fun default_loader () =
    MLSYSPortable.pointer_eq (!load_thydata_fn, load_thydata_from_dat)

end;  (* TheoryReader *)
