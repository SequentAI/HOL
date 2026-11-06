signature hhReconstruct =
sig

  include Abbrev

  (* Settings *)
  val reconstruct_flag : bool ref
  val minimization_timeout : real ref
  val reconstruction_timeout : real ref

  (* Reconstruction: the fastest preplay method on the ATP's facts *)
  type preplay = {stac : string, tac : tactic, method : string, time : real}
  val preplay : bool -> string list -> goal -> preplay
  val hh_reconstruct_with : bool -> string list -> goal -> (string * tactic)
  val hh_reconstruct : string list -> goal -> (string * tactic)

end
