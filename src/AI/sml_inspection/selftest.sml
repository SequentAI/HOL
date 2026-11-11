open HolKernel boolLib
local open smlExecute smlInfix smlLexer smlOpen smlParser smlPrettify
  smlRedirect smlTimeout smlParallel in end

(*
local open smlParallel in
  val l1 = List.tabulate (10,I);
  val _ = parmap_queue_extern 2 examplespec () l1;
end
*)

local open aiLib smlTimeout in
  fun f () = 5;
  val (_,t1) = add_time (timeout 1.0 f) ();
  fun loop () = loop ();
  fun g () = (timeout 0.01 loop ()) handle FunctionTimeout => ();
  val (_,t2) = add_time g ();

  val cleanup_done = ref false;
  fun cleanup_worker () =
    (loop () handle Interrupt =>
      (OS.Process.sleep (Time.fromReal 0.05);
       cleanup_done := true;
       raise Interrupt));
  val _ = (timeout 0.01 cleanup_worker () handle FunctionTimeout => ());
  val _ = if !cleanup_done then ()
          else raise Fail "timeout interrupted worker cleanup";
end

(* The timeout worker is a fresh thread, so it must be handed the caller's
   context pin.  A context is told apart by the value of a data slot. *)
val smlTimeoutPinSlot = Context.Data.new
  {name = "smlTimeout selftest", empty = "none", pp = fn s => s}
local
  open smlTimeout
  val slot = smlTimeoutPinSlot
  fun cur () = Context.Data.get slot (Context.snapshot ())
  fun set_thy s = Context.Data.write slot s
  fun check msg b = if b then () else raise Fail ("smlTimeout pin: " ^ msg)
  val c0 = Context.snapshot ()
  val _ = set_thy "pinA"
  val cA = Context.snapshot ()
  val _ = set_thy "pinB"
  val cB = Context.snapshot ()
  val _ = Context.restore c0
  fun seen () = (Context.is_pinned (), cur ())
  fun spin () = spin ()
in
  (* unpinned callers read the live cell, as before *)
  val _ = check "unpinned" (timeout 1.0 seen () = (false, cur ()))
  val _ = (set_thy "pinB";
           check "unpinned live" (timeout 1.0 seen () = (false, "pinB"));
           Context.restore c0)

  (* the pinned caller's context is what the worker sees, not the live cell *)
  val _ = check "pinned"
    (Context.with_context cA (fn () => timeout 1.0 seen ()) ()
       = (true, "pinA"))
  val _ = check "live untouched" (cur () = Context.Data.get slot c0)

  (* ... also when the live cell is restored from outside while it runs *)
  val _ =
    let
      val started = ref false
      val restored = ref false
      fun wait r = if !r then () else (OS.Process.sleep (Time.fromReal 0.01);
                                       wait r)
      fun worker () =
        (started := true; wait restored; seen ())
      fun outside () = (wait started; Context.restore cB; restored := true)
      val _ = Thread.fork (outside, [])
      val r = Context.with_context cA (fn () => timeout 5.0 worker ()) ()
      val _ = check "live restored" (cur () = "pinB")
      val _ = Context.restore c0
    in
      check "pinned after live restore" (r = (true, "pinA"))
    end

  (* app_stac replays a candidate tactic on the timeout worker *)
  val stac = "(fn g => fn ctxt => (smlExecute.sml_string_glob := \
    \(Context.Data.get smlTimeoutPinSlot (Context.snapshot ())); Tactical.ALL_TAC g ctxt))"
  val _ =
    let
      val g = ([], boolSyntax.T)
      val _ = smlExecute.sml_string_glob := ""
      val r = Context.with_context cA
                (fn () => smlExecute.app_stac 5.0 stac g) ()
    in
      check "app_stac ran" (case r of SOME [_] => true | _ => false);
      check "app_stac pinned" (!smlExecute.sml_string_glob = "pinA")
    end

  (* the pin does not leak into later unpinned calls, and a timeout of a
     pinned caller's worker still releases the worker's pin *)
  val _ = (Context.with_context cA
             (fn () => timeout 0.01 (fn () => spin ()) () handle
                FunctionTimeout => ()) ())
  val _ = check "unpinned after" (timeout 1.0 seen () = (false, cur ()))
  val _ = check "main unpinned" (not (Context.is_pinned ()))
end
