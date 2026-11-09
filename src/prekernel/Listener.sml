structure Listener :> Listener =
struct

open Unsynchronized Feedback

type 'a t = (string * ('a -> unit)) list ref

fun new_listener () : 'a t = ref []

fun add_listener (r:'a t) (sf as (s,f)) =
    let
      val t = !r
    in
      case List.find (fn (s', _) => s' = s) t of
        NONE => r := sf :: t
      | SOME _ =>
        if !Globals.interactive then
          r := sf :: List.filter (fn (s', _) => s' <> s) t
        else
          raise mk_HOL_ERR "Listener" "add_listener"
            ("duplicate listener registration: "^s)
    end

fun remove_listener (r:'a t) s =
    let
      val t = !r
      val (fopt, rest) =
          Portable.trypluck' (fn (s',f) => if s' = s then SOME f else NONE) t
    in
      r := rest;
      fopt
    end

fun listeners (t:'a t) = (!t)


val hook_table : (string * (Time.time ref * Time.time ref * int ref)) list ref = ref []
fun hook_phase name f x =
  let
    val t = Timer.startCPUTimer ()
    fun stop () =
      let
        val {nongc, gc} = Timer.checkCPUTimes t
        val (a, b, c) =
            case List.find (fn (n, _) => n = name) (!hook_table) of
                SOME (_, r) => r
              | NONE => let val r = (ref Time.zeroTime, ref Time.zeroTime, ref 0)
                        in hook_table := (name, r) :: !hook_table; r end
      in
        a := Time.+ (!a, Time.+ (#usr nongc, #sys nongc));
        b := Time.+ (!b, Time.+ (#usr gc, #sys gc));
        c := !c + 1
      end
  in
    (f x before stop ()) handle e => (stop (); raise e)
  end
fun hook_report () =
  map (fn (n, (a, b, c)) => (n, !a, !b, !c)) (rev (!hook_table))
fun call_listener (t:'a t) v =
    let
      fun foldthis (kf as (k,f), A) =
          case Exn.capture (hook_phase k f) v of
              Exn.Res () => A
            | Exn.Exn e => (k,f,e) :: A
    in
      List.foldr foldthis [] (!t)
    end

fun without_one (r:'a t) s f x =
    let
      val t = !r
      val (_, t') =
          Portable.trypluck' (fn (s',f) => if s' = s then SOME () else NONE) t
    in
      setmp r t' f x
    end

fun without_all r f x = setmp r [] f x

end (* struct *)
