signature hhConfig =
sig
  type hh_options =
    {timeout : int,
     max_proofs : int,
     provers : string list,
     slices : int,
     cores : int,
     filter : string,
     max_facts : int option,
     format : string,
     type_enc : string,
     lam_trans : string,
     mono_iters : int,
     mono_instances : int option,
     minimize : bool,
     preplay_timeout : real,
     minimize_timeout : real,
     cache : bool,
     cache_dir : string,
     cache_max_entries : int,
     debug_dir : string option}

  (* Small filesystem and string helpers, shared with hhProver and hhEval. *)
  val is_dir : string -> bool
  val ensure_dir : string -> unit
  val directory_names : string -> string list
  val trim : string -> string
  val trim_left : string -> string
  val first_some : ('a -> 'b option) -> 'a list -> 'b option
  val valid_filter : string -> bool

  val state_dir : unit -> string

  val get : string -> string option
  val get_int : string -> int option
  val get_bool : string -> bool option
  val get_path : string -> string option
  val dump : unit -> (string * string) list

  val hh_set : string * string -> unit
  val hh_unset : string -> unit
  val hh_get : string -> string
  val hh_params : unit -> (string * string * string) list
  val print_params : unit -> unit
  val snapshot : unit -> hh_options

  (* Initialisation hooks break dependency cycles with these later modules. *)
  val register_prover_validator : (string -> bool) -> unit
  val register_reconstruction_timeouts :
    (real * real -> unit) -> unit

  val platform : unit -> string
  (* numeric-aware comparison of version strings such as 5.0.1 *)
  val version_compare : string * string -> order
  val find_exec_with_env : string -> string -> string list -> string option
  val find_exec : string -> string list -> string option
end
