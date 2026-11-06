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

fun hh_reconstruct_with minimize lemmas g =
  if not (!reconstruct_flag)
  then (print_endline (mk_metis_call lemmas);
        raise ERR "hh_minimize" "reconstruction off")
  else
    let
      val stac = mk_metis_call lemmas
      val t1 = !minimization_timeout
      val t2 = !reconstruction_timeout
      val newstac =
        if minimize then psMinimize.minimize_stac t1 stac g [] else stac
      val tac = tactic_of_sml 1.0 newstac
    in
      case timeout_tactic t2 tac g of
        SOME _ => (newstac,tac)
      | NONE   => raise ERR "hh_reconstruct" "reconstruction failed"
    end

fun hh_reconstruct lemmas = hh_reconstruct_with true lemmas

end
