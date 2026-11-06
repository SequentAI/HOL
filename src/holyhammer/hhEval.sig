signature hhEval =
sig
  datatype regime = Bushy | Chainy
  datatype selector =
      Deps
    | Knn of int
    | Mepo of int
    | Mash of int
    | Mesh of int
    | PerSlice
  datatype engine =
      Prover of string
    | Sched of {provers : string list, slices : int,
                cores : int, max_proofs : int}

  type condition =
    {cond_id : string, regime : regime, selector : selector,
     engine : engine, timeout : int, reconstruct : bool}

  type journal_slice =
    {slice : hhProver.slice, szs : string, time : real, cached : bool}

  type journal_entry =
    {run : string, thy : string, thm : string, goal_id : string,
     cond : string, regime : regime, selector : selector,
     engine : engine, ho : bool option, fresh : bool option, prover : string,
     prover_version : string option, nfacts : int,
     timeout : int, szs : string, t_prover : real,
     axioms_used : string list option, recon_ok : bool option,
     recon_method : string option, t_recon : real option,
     stac : string option, error : string option, stop : string option,
     t_total : real option, winner : hhProver.slice option,
     slices : journal_slice list}

  type corpus_coverage =
    {srcfiles : string list, dat_theories : string list,
     added_from_dat : string list}

  type corpus_entry =
    {thy : string, theorem_count : int, dep_stamp : string}

  type prover_identity =
    {name : string, path : string option, version : string option,
     sha256 : string option}

  type run_header =
    {expname : string, date : string, host : string, hol_commit : string,
     provers : prover_identity list, corpus : corpus_entry list,
     added_from_dat : string list, conditions : condition list, sample : int}

  type completed

  val string_of_regime : regime -> string
  val string_of_selector : selector -> string
  val is_higher_order_goal : Term.term -> bool
  val is_fresh_goal : string -> Term.term -> bool
  val validate_condition : condition -> unit
  val encode_condition : condition -> string
  val parse_condition : string -> condition

  val theories_from_srcfile_lines : string list -> string list
  val theories_from_srcfiles : string -> string list
  val coverage_check :
    {srcfiles : string list, dat_theories : string list} -> string list
  val stdlib_coverage : unit -> corpus_coverage
  val stdlib_theories : unit -> string list

  val eval_dir : unit -> string
  val experiment_dir : string -> string
  val journal_path : string -> string -> string

  val encode_journal_line : journal_entry -> string
  val parse_journal_line : string -> journal_entry
  val append_journal : string -> journal_entry -> unit
  val read_journal : string -> journal_entry list

  val read_completed : string -> completed
  val cell_completed : completed -> string * string -> bool
  val journal_complete : string -> (string * string) list -> bool

  val report : string -> unit

  val restrict_features_to_pool :
    string list -> (string * 'a) list -> (string * 'a) list

  val loaded_corpus_entry : string -> corpus_entry
  val current_prover_identities : condition list -> prover_identity list
  val new_run_header :
    {expname : string, corpus : corpus_entry list,
     added_from_dat : string list, conditions : condition list,
     sample : int} -> run_header
  val write_run_header : string -> run_header -> unit
  val validate_run_header : string -> run_header -> unit

  val sample_goal : int -> string -> bool
  val goal_partition : {part : int, parts : int} -> string -> bool

  val set_worker_settings : {conditions : condition list, sample : int} -> unit
  val set_worker_goal_ids : string list -> unit
  val set_worker_partition : {part : int, parts : int} -> unit
  val worker_theory_complete : string -> string -> bool
  val write_evalscript : string -> string -> condition list -> int -> string
  val journal_theory_error : string -> string -> string -> unit
  val eval_thy : string -> string -> unit
  val run_eval :
    {expname : string, ncore : int, thyl : string list,
     conditions : condition list} -> unit

  val smoke_goals : (string * string * string) list
  val run_smoke : {expdir : string, timeout : int} -> journal_entry list
end
