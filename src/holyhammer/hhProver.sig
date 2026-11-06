signature hhProver =
sig
  datatype szs =
      SzsTheorem
    | SzsCounterSat
    | SzsSatisfiable
    | SzsGaveUp
    | SzsTimeout
    | SzsResourceOut
    | SzsInappropriate
    | SzsUnknown of string
    | RunFailure of string

  type slice =
    {prover : string, format : string, type_enc : string,
     lam_trans : string, nfacts : int, filter : string,
     extra_opts : string list, slice_size : int}

  type run_request =
    {timeout : int, format : string, problem : string, extra : string list,
     debug_dir : string option}

  type run_result =
    {szs : szs, used_axioms : string list option, time : real,
     version : string option, output_file : string}

  type running =
    {kill : unit -> unit,
     wait : unit -> run_result}

  type prover_config =
    {name : string,
     exec_names : string list,
     env_var : string,
     version_args : string list,
     parse_version : string -> string option,
     tested_versions : string list,
     supported_formats : string list,
     (* the executable's path and probed version *)
     mk_command : string -> string option -> run_request ->
       string * string list,
     parse_output : string list -> szs * string list option,
     mono_instances : int option,
     slices : unit -> slice list,
     legacy : bool}

  val same_slice : slice -> slice -> bool

  val all : unit -> prover_config list
  val lookup : string -> prover_config option
  val register : prover_config -> unit
  val default_provers : unit -> string list

  (* Human-readable rendering, for progress output.  Not a wire format:
     hhCache keeps its own round-trippable encoding. *)
  val szs_name : szs -> string
  val szs_of_line : string -> szs option
  val axioms_from_tstp : string list -> string list

  (* Executable discovery, version probing and a timed run of one problem. *)
  val find_exec : prover_config -> string option
  val probe : prover_config ->
    {path : string, version : string option, tested : bool} option
  (* Shared with the scheduler: lock discipline must have one definition. *)
  val with_mutex : Mutex.mutex -> (unit -> 'a) -> 'a
  val elapsed : Time.time -> real

  (* Test hook: counts every successful fork, including version probes. *)
  val spawn_count : unit -> int
  val reset_spawn_count : unit -> unit
  val run_async : prover_config -> run_request -> running
  val run : prover_config -> run_request -> run_result
end
