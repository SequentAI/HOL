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

fun temp_encoded_update sdata thyname {data,ty} =
    Theory.LoadableThyData.temp_encoded_update {
      thy = thyname,
      thydataty = ty,
      shared_readmaps = {strings = read_string sdata, terms = read_term sdata},
      data = data
    }


(* A theory's data as decoded from its .dat file, with the values the
   source loader built: enough to repeat its registration without
   reading or decoding the file again. *)
type decoded = {thyname : string, hash : string,
                parents : (string * string) list,
                new_types : (string * int) list,
                new_consts : (string * hol_type) list,
                sdata : sharing_data_out,
                thydata : {data : HOLsexp.t, ty : string} list}

val decoded_tag : decoded MLSYSPortable.persistent_tag =
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
fun bind_data ({thyname,sdata,thydata,...} : decoded) =
    let
      val {theorems = named_thms,...} = export_from_sharing_data sdata
    in
      DB.bindl thyname named_thms;
      app (temp_encoded_update sdata thyname) thydata;
      named_thms
    end

val capture = ref false
val captured : decoded option ref = ref NONE

fun load_thydata_from_dat (r as {thyname,path,hash}) =
    let
      open HOLsexp
      val rawthy as {parents,tables,exports,name=stored_name,...} =
            load_raw_thydata {path=path}
      fun mungename {thy,hash} = (thy,hash)
      val _ = thyname = stored_name orelse
              raise TheoryReader
                    ("reading at " ^ path ^ " for theory " ^ thyname ^
                     " and got theory called " ^ stored_name ^ " instead")
      val parents = map mungename parents
      val _ = Theory.link_parents (thyname, hash) parents
      val {types=new_types,consts=new_consts} = #newsig rawthy
      val stamps = ref true
      val consts = ref []
      fun before_types () =
          stamps := Theory.incorporate_types thyname new_types
      fun before_terms tyv =
          let
            val cs = map (fn (n,i) => (n,Vector.sub(tyv,i))) new_consts
          in
            consts := cs;
            stamps := (Theory.incorporate_consts thyname cs andalso !stamps)
          end
      val share_data =
            dec_sdata {
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
      val d = {thyname = thyname, hash = hash, parents = parents,
               new_types = new_types, new_consts = !consts,
               sdata = share_data, thydata = thydata}
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
      val _ = Theory.link_parents (thyname, hash) parents
      val types_ok = Theory.incorporate_types thyname new_types
      val consts_ok = Theory.incorporate_consts thyname new_consts
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
