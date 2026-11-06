(* ===================================================================== *)
(* FILE          : hhReconstruct.sml                                     *)
(* DESCRIPTION   : Reconstruct a proof from the lemmas given by an ATP   *)
(*                 and optionally minimize them.                         *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2015                                                  *)
(* ===================================================================== *)

structure hhReconstruct :> hhReconstruct =
struct

open HolKernel Dep Tag boolLib aiLib smlExecute smlTimeout smlRedirect
  mlThmData psMinimize

val ERR = mk_HOL_ERR "hhReconstruct"

(* --------------------------------------------------------------------------
   Settings
   -------------------------------------------------------------------------- *)

val reconstruct_flag = ref true
val minimization_timeout = ref 1.0
val reconstruction_timeout = ref 1.0

val _ = hhConfig.register_reconstruction_timeouts
  (fn (preplay, minimize) =>
    (reconstruction_timeout := preplay;
     minimization_timeout := minimize))

(*----------------------------------------------------------------------------
   Minimization and pretty-printing
 -----------------------------------------------------------------------------*)

val TC_OFF = trace ("show_typecheck_errors", 0)
(* the trace setting, the timeout and the handler all have to span the
   context application, which is when the tactic does its work *)
fun timeout_tactic t tac g =
  let val ctxt = Context.snapshot() in
    SOME (fst (timeout t (TC_OFF (Lib.C tac ctxt)) g))
  end
  handle Interrupt => raise Interrupt | _ => NONE

(*----------------------------------------------------------------------------
   Preplay ladder: each method is tried on the ATP's facts under the preplay
   budget, the fastest one that closes the goal wins, and only the winner is
   minimized.  A method's budget shrinks to the best time found so far,
   since a slower success could not win.
 -----------------------------------------------------------------------------*)

type preplay = {stac : string, tac : tactic, method : string, time : real}

fun fact_list lemmas =
  "[" ^ String.concatWith " , " (map dbfetch_of_thmid lemmas) ^ "]"

fun ladder lemmas =
  let val facts = fact_list lemmas in
    [("metis", "bossLib.metis_tac " ^ facts),
     ("simp", "bossLib.simp " ^ facts),
     ("fs", "bossLib.fs " ^ facts),
     ("gvs", "bossLib.gvs " ^ facts),
     ("rw", "bossLib.rw " ^ facts),
     ("meson", "mesonLib.MESON_TAC " ^ facts),
     ("decide", "bossLib.DECIDE_TAC")]
  end

(* the time of a successful run of [stac] that closes [g] *)
fun preplay_time t stac g =
  let
    val tac = tactic_of_sml t stac
    val (result, time) = add_time (timeout_tactic t tac) g
  in
    case result of SOME [] => SOME (tac, time) | _ => NONE
  end
  handle Interrupt => raise Interrupt | _ => NONE

fun best_method t lemmas g =
  let
    fun try ((method, stac), best) =
      let val budget = case best of NONE => t | SOME (_, _, _, b) => b in
        case preplay_time budget stac g of
          SOME (tac, time) =>
            if time < budget then SOME (method, stac, tac, time) else best
        | NONE => best
      end
  in
    foldl try NONE (ladder lemmas)
  end

fun preplay minimize lemmas g =
  if not (!reconstruct_flag)
  then (print_endline (mk_metis_call lemmas);
        raise ERR "preplay" "reconstruction off")
  else
    case best_method (!reconstruction_timeout) lemmas g of
      NONE => raise ERR "preplay" "no method replays the proof"
    | SOME (method, stac, tac, time) =>
      let
        val pretty = psMinimize.unsafe_prettify_stac stac
        val unminimized =
          {stac = pretty, tac = tac, method = method, time = time}
        val mini =
          if minimize
          then psMinimize.minimize_stac (!minimization_timeout) stac g []
          else pretty
      in
        if mini = pretty then unminimized
        else
          case preplay_time (!reconstruction_timeout) mini g of
            SOME (minitac, minitime) =>
              {stac = mini, tac = minitac, method = method, time = minitime}
          | NONE => unminimized
      end

fun hh_reconstruct_with minimize lemmas g =
  let val {stac, tac, ...} = preplay minimize lemmas g in (stac, tac) end

fun hh_reconstruct lemmas = hh_reconstruct_with true lemmas

end
