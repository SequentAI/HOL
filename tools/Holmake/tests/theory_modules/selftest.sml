open testutils;

val _ = OS.FileSys.chDir "testdir";
val hol = OS.Path.concat (Systeml.HOLDIR, "bin/hol");
val holmake = OS.Path.concat (Systeml.HOLDIR, "bin/Holmake");

fun command args =
  if OS.Process.isSuccess (Systeml.systeml args) then ()
  else die (String.concatWith " " args);
fun read path =
  let val input = HOLFileSys.openIn path
  in HOLFileSys.inputAll input before HOLFileSys.closeIn input end;
fun remove path = OS.FileSys.remove path handle OS.SysErr _ => ();
fun children directory =
  let
    val input = OS.FileSys.openDir directory
    fun loop () =
      case OS.FileSys.readDir input of
          NONE => []
        | SOME name => name :: loop ()
  in
    loop () before OS.FileSys.closeDir input
  end;
fun clear directory =
  (app (fn name => remove (OS.Path.concat (directory, name)))
       (children directory);
   OS.FileSys.rmDir directory) handle OS.SysErr _ => ();
fun probe args =
  (remove "module-stats";
   command ["/usr/bin/env", "PROBE_ARGS=" ^ String.concatWith " " args,
            hol, "run", "--noconfig", "probe.sml"]);
fun outputs () = map (read o (fn ext => "moduleProbeTheory." ^ ext))
                     ["dat", "sig", "sml"];
fun stats () = List.mapPartial Int.fromString
                (String.tokens Char.isSpace (read "module-stats"));
fun modules () = List.filter (String.isSuffix ".pmo") (children "modules");
val reference = ref [] : string list ref;
fun expect what (want : int list) =
  if stats () = want andalso outputs () = !reference then OK ()
  else die (what ^ ": stats " ^
            String.concatWith " " (map Int.toString (stats ())));

val _ = command [holmake, "--no-cache", "cleanAll"];
val _ = command [holmake, "--no-cache", "moduleDTheory.uo"];
val _ = clear "modules";
val _ = tprint "source loads in both orders agree";
val _ = probe ["abcd", "nocache"];
val _ = reference := outputs ();
val _ = probe ["cbda", "nocache"];
val _ = if outputs () = !reference then OK ()
        else die "load order changed theory outputs";

val supported = (probe ["abcd"]; OS.FileSys.access ("module-stats", []));
val _ = if not supported then () else
  let
    val _ = tprint "first load saves a module per theory"
    val _ = expect "cold" [0, 5, 5]
    val _ = tprint "modules load in another order"
    val _ = probe ["cbda"]
    val _ = expect "warm, reversed diamond" [5, 0, 0]
    val _ = tprint "modules load in the original order"
    val _ = probe ["dcba"]
    val _ = expect "warm" [5, 0, 0]
    val _ = tprint "a missing module is rebuilt beside warm ones"
    val pmos = modules ()
    val _ = remove (OS.Path.concat ("modules", hd pmos))
    val _ = probe ["bcad"]
    val _ = expect "mixed" [4, 1, 1]
    val _ = tprint "a corrupt module is rejected and replaced"
    val victim = OS.Path.concat ("modules", hd (modules ()))
    val output = BinIO.openOut victim
    val _ = BinIO.output (output, Byte.stringToBytes "corrupt")
            before BinIO.closeOut output
    val _ = probe ["abcd"]
    val _ = expect "corrupt" [4, 1, 1]
    val _ = tprint "a rebound structure forces source loads"
    val _ = probe ["abcd", "shadow"]
    val _ = expect "shadowed" [0, 5, 0]
    val _ = tprint "a custom theorem source bypasses modules"
    val _ = probe ["abcd", "customloader"]
    val _ = expect "custom loader" [0, 0, 0]
    val _ = tprint "the exporter writes its theory's module once"
    val _ = probe ["abcd", "produce"]
    val _ = expect "produce" [1, 0, 0, 0]
    val _ = tprint "the exporter's module loads warm"
    val _ = probe ["abcd", "loadprobe"]
    val _ = expect "exporter's module" [6, 0, 0]
    val exported = read "probe-fingerprint"
    val _ = tprint "a loader writes the module the exporter didn't"
    val _ = clear "modules"
    val _ = probe ["abcd", "loadprobe"]
    val _ = expect "loader cold" [0, 6, 6]
    val _ = tprint "the loader's module loads as the exporter's did"
    val _ = probe ["abcd", "loadprobe"]
    val _ = if read "probe-fingerprint" = exported then
              expect "loader's module" [6, 0, 0]
            else die "exporter's and loader's modules differ"
  in
    ()
  end;
val _ = clear "modules";
val _ = remove "module-stats";
val _ = remove "probe-fingerprint";
val _ = command [holmake, "--no-cache", "cleanAll"];
