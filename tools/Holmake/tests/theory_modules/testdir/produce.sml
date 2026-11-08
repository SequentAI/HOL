(* Produces the exported probe theory's module three times and records
   the writes each call made: the first writes it, the second finds it
   in the cache, and the third, with it hidden, finds the ids of the
   theory's constant no longer canonical.  Then whether the exporting
   process's own theory is canonical. *)
fun writes () = #writes (TheoryModules.statistics ());
fun pmos () =
  let
    val input = OS.FileSys.openDir "modules"
    fun loop () =
      case OS.FileSys.readDir input of
          NONE => []
        | SOME name => if String.isSuffix ".pmo" name then name :: loop ()
                       else loop ()
  in
    loop () before OS.FileSys.closeDir input
  end;
fun produce () =
  let val w = writes ()
  in Meta.produceTheoryModule "moduleProbeTheory.sml"; writes () - w end;
val existing = pmos ();
val first = produce ();
val second = produce ();
val added = List.filter (fn f => not (Lib.mem f existing)) (pmos ());
fun hide (old, new) =
  app (fn f => OS.FileSys.rename {old = OS.Path.concat ("modules", f ^ old),
                                  new = OS.Path.concat ("modules", f ^ new)})
      added;
val _ = hide ("", ".hidden");
val third = produce ();
val _ = hide (".hidden", "");
val out = TextIO.openOut "module-stats";
val _ = TextIO.output
          (out, String.concatWith " "
                  (map Int.toString
                     [first, second, third,
                      if TheoryReader.is_canonical "moduleProbe" then 1
                      else 0]));
val _ = TextIO.closeOut out;
