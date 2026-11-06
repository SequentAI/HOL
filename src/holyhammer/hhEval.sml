(* ========================================================================= *)
(* FILE          : hhEval.sml                                                *)
(* DESCRIPTION   : HolyHammer evaluation corpus and durable journal          *)
(*
   Schedule cells own [cores] prover processes apiece.  Callers of run_eval
   therefore size ncore to machine_cores div cores_per_cell; the predictable
   peak load is ncore * cores_per_cell, as in the Phase 0 prover-cell driver.
*)
(* ========================================================================= *)

structure hhEval :> hhEval =
struct

open HolKernel boolLib aiLib

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

val same_slice = hhProver.same_slice

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

type completed = (string * string) Binaryset.set

fun cell_key_compare ((goal1, cond1), (goal2, cond2)) =
  case String.compare (goal1, goal2) of
      EQUAL => String.compare (cond1, cond2)
    | order => order

fun join left right = OS.Path.concat (left, right)

val is_dir = hhConfig.is_dir
val ensure_dir = hhConfig.ensure_dir
val trim = hhConfig.trim

val sorted_unique = mk_string_set

fun string_of_regime Bushy = "bushy"
  | string_of_regime Chainy = "chainy"

fun string_of_selector Deps = "deps"
  | string_of_selector (Knn count) = "knn" ^ Int.toString count
  | string_of_selector (Mepo count) = "mepo" ^ Int.toString count
  | string_of_selector (Mash count) = "mash" ^ Int.toString count
  | string_of_selector (Mesh count) = "mesh" ^ Int.toString count
  | string_of_selector PerSlice = "perslice"

fun filter_of_selector Deps = "deps"
  | filter_of_selector (Knn _) = "knn"
  | filter_of_selector (Mepo _) = "mepo"
  | filter_of_selector (Mash _) = "mash"
  | filter_of_selector (Mesh _) = "mesh"
  | filter_of_selector PerSlice = "per-slice"

fun regime_of_string "bushy" = Bushy
  | regime_of_string "chainy" = Chainy
  | regime_of_string text = raise Fail ("unknown evaluation regime: " ^ text)

fun selector_of_string "deps" = Deps
  | selector_of_string "perslice" = PerSlice
  | selector_of_string text =
      let
        fun counted prefix make =
          if String.isPrefix prefix text then
            let
              val digits = String.extract (text, String.size prefix, NONE)
            in
              if digits <> "" andalso
                 List.all Char.isDigit (String.explode digits) then
                (case Int.fromString digits of
                     SOME count => SOME (make count)
                   | NONE => raise Fail
                       ("bad evaluation selector: " ^ text))
              else raise Fail ("bad evaluation selector: " ^ text)
            end
          else NONE
      in
        case counted "knn" Knn of
            SOME selector => selector
          | NONE =>
              (case counted "mepo" Mepo of
                   SOME selector => selector
                 | NONE =>
                     (case counted "mash" Mash of
                          SOME selector => selector
                        | NONE =>
                            (case counted "mesh" Mesh of
                                 SOME selector => selector
                               | NONE => raise Fail
                                   ("unknown evaluation selector: " ^ text))))
      end

(* This deliberately examines only the normalized goal, never a translation.
   Quantifier abstractions are consumed by their binder representation;
   every other abstraction has survived in term position. *)
fun is_higher_order_goal tm =
  let
    fun is_fun_type ty =
      (ignore (dom_rng ty); true) handle HOL_ERR _ => false

    fun member_bound bound tm =
      List.exists (fn var => aconv var tm) bound

    fun scan bound formula tm =
      if is_forall tm then
        if formula then
          let val (var, body) = dest_forall tm in
            scan (var :: bound) true body
          end
        else true
      else if is_exists tm then
        if formula then
          let val (var, body) = dest_exists tm in
            scan (var :: bound) true body
          end
        else true
      else if is_neg tm then
        if formula then scan bound true (dest_neg tm) else true
      else if is_conj tm then
        if formula then
          let val (left, right) = dest_conj tm in
            scan bound true left orelse scan bound true right
          end
        else true
      else if is_disj tm then
        if formula then
          let val (left, right) = dest_disj tm in
            scan bound true left orelse scan bound true right
          end
        else true
      else if is_imp_only tm then
        if formula then
          let val (left, right) = dest_imp tm in
            scan bound true left orelse scan bound true right
          end
        else true
      else if is_eq tm then
        if formula then
          let val (left, right) = dest_eq tm in
            scan bound false left orelse scan bound false right
          end
        else true
      else if is_abs tm then true
      else if is_comb tm then
        let
          val (head, args) = strip_comb tm
          val applied_bound_function =
            not (null args) andalso member_bound bound head andalso
            is_fun_type (type_of head)
        in
          applied_bound_function orelse
          List.exists (scan bound false) (head :: args)
        end
      else false
  in
    scan [] true (hhProblemGen.beta_eta_contract false tm)
  end

(* [thy] is explicit so this classifier is pure and usable on a recorded
   theorem independently of Theory.current_theory().  Contracting first
   matches the normalized statement inspected by the other goal classifier. *)
fun is_fresh_goal thy tm =
  List.exists (fn constant => #Thy (dest_thy_const constant) = thy)
    (find_terms is_const (hhProblemGen.beta_eta_contract false tm))

fun validate_condition (condition : condition) =
  case (#selector condition, #engine condition, #reconstruct condition) of
      (PerSlice, Prover _, _) => raise Fail
        "invalid hhEval Prover condition: perslice requires Sched"
    | (Mepo _, Sched _, _) => raise Fail
        "invalid hhEval Sched condition: mepo selectors require Prover"
    | (Mash _, Sched _, _) => raise Fail
        "invalid hhEval Sched condition: mash selectors require Prover"
    | (Mesh _, Sched _, _) => raise Fail
        "invalid hhEval Sched condition: mesh selectors require Prover"
    | (_, Sched _, false) => raise Fail
        "invalid hhEval Sched condition: reconstruct must be true"
    | (_, Sched {provers, slices, cores, max_proofs}, _) =>
        if null provers then raise Fail
          "invalid hhEval Sched condition: provers must not be empty"
        else if slices < 1 then raise Fail
          "invalid hhEval Sched condition: slices must be positive"
        else if cores < 1 then raise Fail
          "invalid hhEval Sched condition: cores must be positive"
        else if max_proofs < 1 then raise Fail
          "invalid hhEval Sched condition: max_proofs must be positive"
        else ()
    | _ => ()

fun json_condition condition =
  let
    val _ = validate_condition condition
    val common =
      [("cond_id", JSON.STRING (#cond_id condition)),
       ("regime", JSON.STRING (string_of_regime (#regime condition))),
       ("selector", JSON.STRING (string_of_selector (#selector condition)))]
    val engine_fields =
      case #engine condition of
          Prover prover =>
            [("engine", JSON.STRING "prover"),
             ("prover", JSON.STRING prover)]
        | Sched {provers, slices, cores, max_proofs} =>
            [("engine", JSON.STRING "sched"),
             ("provers", JSON.ARRAY (map JSON.STRING provers)),
             ("slices", JSON.INT (IntInf.fromInt slices)),
             ("cores", JSON.INT (IntInf.fromInt cores)),
             ("max_proofs", JSON.INT (IntInf.fromInt max_proofs))]
  in
    JSON.OBJECT (common @ engine_fields @
      [("timeout", JSON.INT (IntInf.fromInt (#timeout condition))),
       ("reconstruct", JSON.BOOL (#reconstruct condition))])
  end

fun parse_json text =
  let
    val source = JSONParser.openString text
    val value = JSONParser.parse source
    val _ = JSONParser.close source
  in
    value
  end

fun field name value = JSONUtil.lookupField value name

fun optional_field name (JSON.OBJECT fields) =
      (case List.find (fn (label, _) => label = name) fields of
           SOME (_, value) => SOME value
         | NONE => NONE)
  | optional_field _ _ = NONE

fun string_field name value = JSONUtil.asString (field name value)
fun int_field name value = JSONUtil.asInt (field name value)
fun real_field name value = JSONUtil.asNumber (field name value)
fun bool_field name value = JSONUtil.asBool (field name value)

fun option_field decoder name value =
  case field name value of JSON.NULL => NONE | item => SOME (decoder item)

fun string_list value = JSONUtil.arrayMap JSONUtil.asString value

fun parse_engine value =
  case optional_field "engine" value of
      NONE => Prover (string_field "prover" value)
    | SOME engine_value =>
        (case JSONUtil.asString engine_value of
             "prover" => Prover (string_field "prover" value)
           | "sched" => Sched
               {provers = string_list (field "provers" value),
                slices = int_field "slices" value,
                cores = int_field "cores" value,
                max_proofs = int_field "max_proofs" value}
           | name => raise Fail ("unknown evaluation engine: " ^ name))

fun parse_condition_value value : condition =
  let
    val condition =
      {cond_id = string_field "cond_id" value,
       regime = regime_of_string (string_field "regime" value),
       selector = selector_of_string (string_field "selector" value),
       engine = parse_engine value,
       timeout = int_field "timeout" value,
       reconstruct = bool_field "reconstruct" value}
    val _ = validate_condition condition
  in
    condition
  end

fun encode_condition condition =
  JSONPrinter.valueToString (json_condition condition)

fun parse_condition text = parse_condition_value (parse_json text)

fun theory_of_srcfile line =
  let
    val path = trim line
    val file = OS.Path.file path
    val name = String.substring (file, 0, String.size file - 6)
  in
    if String.isSubstring "/src/" path andalso
       String.isSuffix "Theory" file andalso name <> ""
    then SOME name else NONE
  end
  handle Subscript => NONE

fun theories_from_srcfile_lines lines =
  sorted_unique (List.mapPartial theory_of_srcfile lines)

val read_lines = bare_readl

fun theories_from_srcfiles path = theories_from_srcfile_lines (read_lines path)

val directory_names = hhConfig.directory_names

fun dat_paths_under root =
  let
    fun walk directory =
      List.concat (map (fn name =>
        let val path = join directory name in
          if is_dir path then walk path
          else if String.isSuffix "Theory.dat" name then [path]
          else []
        end) (directory_names directory))
  in
    walk root
  end

fun dat_theories_under root =
  sorted_unique (map (fn path =>
    let val name = OS.Path.file path in
      String.substring (name, 0, String.size name - 10)
    end) (dat_paths_under root))

fun coverage_check {srcfiles, dat_theories} =
  List.filter (fn theory => not (mem theory srcfiles)) dat_theories

fun holdir () =
  case OS.Process.getEnv "HOLDIR" of
      SOME directory => directory
    | NONE => Globals.HOLDIR

fun stdlib_coverage () =
  let
    val root = holdir ()
    val srcfiles = theories_from_srcfiles (join (join root "sigobj") "SRCFILES")
    val dat_theories = dat_theories_under (join root "src")
    val added_from_dat = coverage_check
      {srcfiles = srcfiles, dat_theories = dat_theories}
  in
    {srcfiles = srcfiles, dat_theories = dat_theories,
     added_from_dat = added_from_dat}
  end

fun stdlib_theories () =
  let
    val {srcfiles, added_from_dat, ...} = stdlib_coverage ()
    val _ =
      if null added_from_dat then ()
      else TextIO.output (TextIO.stdErr,
        "hhEval: adding " ^ Int.toString (length added_from_dat) ^
        " theories absent from sigobj/SRCFILES\n")
  in
    sorted_unique (srcfiles @ added_from_dat)
  end

fun eval_dir () =
  case hhConfig.get_path "eval.dir" of
      SOME directory => directory
    | NONE => join (join (join (holdir ()) "src") "holyhammer") "eval"

fun experiment_dir expname = join (eval_dir ()) expname
fun journal_path expdir theory =
  join (join expdir "journal") (theory ^ ".jsonl")

fun json_string_option NONE = JSON.NULL
  | json_string_option (SOME text) = JSON.STRING text

fun json_real_option NONE = JSON.NULL
  | json_real_option (SOME number) = JSON.FLOAT number

fun json_bool_option NONE = JSON.NULL
  | json_bool_option (SOME truth) = JSON.BOOL truth

fun json_string_list_option NONE = JSON.NULL
  | json_string_list_option (SOME items) = JSON.ARRAY (map JSON.STRING items)

fun json_slice
    {prover, format, type_enc, lam_trans, nfacts, filter, extra_opts,
     slice_size} =
  JSON.OBJECT
    [("prover", JSON.STRING prover), ("format", JSON.STRING format),
     ("type_enc", JSON.STRING type_enc),
     ("lam_trans", JSON.STRING lam_trans),
     ("nfacts", JSON.INT (IntInf.fromInt nfacts)),
     ("filter", JSON.STRING filter),
     ("extra_opts", JSON.ARRAY (map JSON.STRING extra_opts)),
     ("slice_size", JSON.INT (IntInf.fromInt slice_size))]

fun json_journal_slice {slice, szs, time, cached} =
  JSON.OBJECT
    [("slice", json_slice slice), ("szs", JSON.STRING szs),
     ("time", JSON.FLOAT time), ("cached", JSON.BOOL cached)]

fun json_engine_params {provers, slices, cores, max_proofs} =
  JSON.OBJECT
    [("provers", JSON.ARRAY (map JSON.STRING provers)),
     ("slices", JSON.INT (IntInf.fromInt slices)),
     ("cores", JSON.INT (IntInf.fromInt cores)),
     ("max_proofs", JSON.INT (IntInf.fromInt max_proofs))]

fun journal_json
    {run, thy, thm, goal_id, cond, regime, selector, engine, ho, fresh, prover,
     prover_version, nfacts, timeout, szs, t_prover, axioms_used,
     recon_ok, recon_method, t_recon, stac, error, stop, t_total, winner,
     slices} =
  let
    val common =
      [("run", JSON.STRING run), ("thy", JSON.STRING thy),
       ("thm", JSON.STRING thm), ("goal_id", JSON.STRING goal_id),
       ("cond", JSON.STRING cond),
       ("regime", JSON.STRING (string_of_regime regime)),
       ("selector", JSON.STRING (string_of_selector selector)),
       (* A missing flag is only possible after parsing an old journal;
          rewrites still produce a valid boolean cell field. *)
       ("ho", JSON.BOOL (case ho of SOME value => value | NONE => false)),
       (* Likewise, parsing v1--v3 preserves the missing v4 classification
          internally, while any newly written line has the v4 bool field. *)
       ("fresh", JSON.BOOL
          (case fresh of SOME value => value | NONE => false))]
    val winning =
      [("prover", JSON.STRING prover),
       ("prover_version", json_string_option prover_version),
       ("nfacts", JSON.INT (IntInf.fromInt nfacts)),
       ("timeout", JSON.INT (IntInf.fromInt timeout)),
       ("szs", JSON.STRING szs), ("t_prover", JSON.FLOAT t_prover),
       ("axioms_used", json_string_list_option axioms_used),
       ("recon_ok", json_bool_option recon_ok),
       ("recon_method", json_string_option recon_method),
       ("t_recon", json_real_option t_recon),
       ("stac", json_string_option stac),
       ("error", json_string_option error)]
    val engine_fields =
      case engine of
          Prover name =>
            if name = prover then [("engine", JSON.STRING "prover")]
            else raise Fail
              "invalid hhEval Prover journal entry: engine/prover mismatch"
        | Sched parameters =>
            (case (stop, t_total) of
                 (SOME reason, SOME total) =>
                   [("engine", JSON.STRING "sched"),
                    ("engine_params", json_engine_params parameters)] @
                   winning @
                   [("stop", JSON.STRING reason),
                    ("t_total", JSON.FLOAT total),
                    ("winner", case winner of
                         NONE => JSON.NULL
                       | SOME slice => json_slice slice),
                    ("slices", JSON.ARRAY (map json_journal_slice slices))]
               | _ => raise Fail
                   ("invalid hhEval Sched journal entry: stop and " ^
                    "t_total are required"))
  in
    case engine of
        Prover _ => JSON.OBJECT (common @ engine_fields @ winning)
      | Sched _ => JSON.OBJECT (common @ engine_fields)
  end

fun parse_slice value : hhProver.slice =
  {prover = string_field "prover" value,
   format = string_field "format" value,
   type_enc = string_field "type_enc" value,
   lam_trans = string_field "lam_trans" value,
   nfacts = int_field "nfacts" value,
   filter = string_field "filter" value,
   extra_opts = string_list (field "extra_opts" value),
   slice_size = int_field "slice_size" value}

fun parse_journal_slice value : journal_slice =
  {slice = parse_slice (field "slice" value),
   szs = string_field "szs" value,
   time = real_field "time" value,
   cached = bool_field "cached" value}

fun parse_journal_engine value prover =
  case optional_field "engine" value of
      NONE => Prover prover
    | SOME engine_value =>
        (case JSONUtil.asString engine_value of
             "prover" => Prover prover
           | "sched" =>
               let val parameters = field "engine_params" value in
                 Sched
                   {provers = string_list (field "provers" parameters),
                    slices = int_field "slices" parameters,
                    cores = int_field "cores" parameters,
                    max_proofs = int_field "max_proofs" parameters}
               end
           | name => raise Fail ("unknown journal engine: " ^ name))

fun nullable_optional decoder name value =
  case optional_field name value of
      NONE => NONE
    | SOME JSON.NULL => NONE
    | SOME item => SOME (decoder item)

fun array_or_empty decoder name value =
  case optional_field name value of
      NONE => []
    | SOME items => JSONUtil.arrayMap decoder items

fun parse_journal_value value : journal_entry =
  let
    val prover = string_field "prover" value
    val engine = parse_journal_engine value prover
    val slices = array_or_empty parse_journal_slice "slices" value
    val stored_winner = nullable_optional parse_slice "winner" value
    val winner =
      case (engine, stored_winner) of
          (_, SOME slice) => SOME slice
        | (Prover _, NONE) => NONE
        | (Sched _, NONE) =>
            (* Older journals did not persist the winning translation.
               Recover it only when their abbreviated identity is unique. *)
            (case List.filter (fn {slice, szs, ...} : journal_slice =>
               szs = "Theorem" andalso #prover slice = prover andalso
               #nfacts slice = int_field "nfacts" value) slices of
                 [{slice, ...}] => SOME slice
               | _ => NONE)
  in
    {run = string_field "run" value, thy = string_field "thy" value,
     thm = string_field "thm" value, goal_id = string_field "goal_id" value,
     cond = string_field "cond" value,
     regime = regime_of_string (string_field "regime" value),
     selector = selector_of_string (string_field "selector" value),
     engine = engine,
     ho = nullable_optional JSONUtil.asBool "ho" value,
     fresh = nullable_optional JSONUtil.asBool "fresh" value,
     prover = prover,
     prover_version = option_field JSONUtil.asString "prover_version" value,
     nfacts = int_field "nfacts" value, timeout = int_field "timeout" value,
     szs = string_field "szs" value, t_prover = real_field "t_prover" value,
     axioms_used = option_field string_list "axioms_used" value,
     recon_ok = option_field JSONUtil.asBool "recon_ok" value,
     recon_method = option_field JSONUtil.asString "recon_method" value,
     t_recon = option_field JSONUtil.asNumber "t_recon" value,
     stac = option_field JSONUtil.asString "stac" value,
     error = option_field JSONUtil.asString "error" value,
     stop = nullable_optional JSONUtil.asString "stop" value,
     t_total = nullable_optional JSONUtil.asNumber "t_total" value,
     winner = winner, slices = slices}
  end

fun encode_journal_line entry = JSONPrinter.valueToString (journal_json entry)
fun parse_journal_line text = parse_journal_value (parse_json text)

fun append_journal path entry =
  let
    val _ = ensure_dir (OS.Path.dir path)
    val output = TextIO.openAppend path
    val _ = TextIO.output (output, encode_journal_line entry ^ "\n")
    val _ = TextIO.flushOut output
    val _ = TextIO.closeOut output
  in
    ()
  end

fun read_journal path =
  if OS.FileSys.access (path, [OS.FileSys.A_READ]) then
    let
      (* A torn line can appear anywhere, not just at the end: a resume
         appends past the truncated tail left by an interrupted worker.
         Skip whatever fails to parse rather than losing the journal. *)
      fun parse line =
        (SOME (parse_journal_line line)
         handle Interrupt => raise Interrupt | _ => NONE)
    in
      List.mapPartial parse
        (List.filter (fn line => trim line <> "") (read_lines path))
    end
  else []
  handle OS.SysErr _ => [] | IO.Io _ => []

(* Environment-level failures (no prover binary, prover would not start)
   say nothing about the cell, so they must not mark it done: otherwise a
   sweep started before the provers were installed can never be resumed. *)
fun retryable_szs szs = szs = "Error" orelse szs = "RunFailure"

fun add_completed entry pairs =
  if retryable_szs (#szs entry) then pairs
  else Binaryset.add (pairs, (#goal_id entry, #cond entry))

fun read_completed path =
  List.foldl (fn (entry, pairs) => add_completed entry pairs)
    (Binaryset.empty cell_key_compare) (read_journal path)

fun cell_completed pairs pair = Binaryset.member (pairs, pair)

fun journal_complete path cells =
  let val pairs = read_completed path in
    List.all (cell_completed pairs) cells
  end

fun read_command path arguments =
  let
    val process = Unix.execute (path, arguments)
    val (input, output) = Unix.streamsOf process
    val _ = TextIO.closeOut output
    val text = TextIO.inputAll input
    val _ = TextIO.closeIn input
    val _ = Unix.reap process
  in
    SOME text
  end
  handle OS.SysErr _ => NONE | IO.Io _ => NONE

fun first_word text =
  case String.tokens Char.isSpace text of [] => NONE | word :: _ => SOME word

fun sha256 path =
  let
    fun digest executable arguments =
      case read_command executable arguments of
          NONE => NONE
        | SOME output => first_word output
  in
    if OS.FileSys.access (path, [OS.FileSys.A_READ]) then
      case digest "/usr/bin/sha256sum" [path] of
          SOME hash => SOME hash
        | NONE => digest "/usr/bin/shasum" ["-a", "256", path]
    else NONE
  end
  handle OS.SysErr _ => NONE

val distinct_names = mk_sameorder_set String.compare

fun prover_identity name =
  case hhProver.lookup name of
      NONE => {name = name, path = NONE, version = NONE, sha256 = NONE}
    | SOME config =>
        (case hhProver.probe config of
             NONE => {name = name, path = NONE, version = NONE, sha256 = NONE}
           | SOME {path, version, ...} =>
               {name = name, path = SOME path, version = version,
                sha256 = sha256 path})

fun engine_provers (Prover name) = [name]
  | engine_provers (Sched {provers, ...}) = provers

fun current_prover_identities (conditions : condition list) =
  map prover_identity
    (distinct_names (List.concat (map (engine_provers o #engine) conditions)))

fun host_name () =
  case List.find (fn (name, _) => name = "nodename")
                 (Posix.ProcEnv.uname ()) of
      SOME (_, host) => host
    | NONE => "unknown"

fun hol_commit () =
  case read_command "/usr/bin/git" ["rev-parse", "HEAD"] of
      SOME output =>
        (case first_word output of SOME hash => hash | NONE => "unknown")
    | NONE => "unknown"

fun loaded_corpus_entry thy =
  {thy = thy, theorem_count = length (DB.theorems thy),
   dep_stamp = Theory.hash thy}

fun new_run_header
    {expname, corpus, added_from_dat, conditions, sample} =
  {expname = expname, date = Date.toString (Date.fromTimeLocal (Time.now ())),
   host = host_name (), hol_commit = hol_commit (),
   provers = current_prover_identities conditions, corpus = corpus,
   added_from_dat = added_from_dat, conditions = conditions, sample = sample}

fun json_prover {name, path, version, sha256} =
  JSON.OBJECT
    [("name", JSON.STRING name), ("path", json_string_option path),
     ("version", json_string_option version),
     ("sha256", json_string_option sha256)]

fun json_corpus_entry {thy, theorem_count, dep_stamp} =
  JSON.OBJECT
    [("thy", JSON.STRING thy),
     ("theorem_count", JSON.INT (IntInf.fromInt theorem_count)),
     ("dep_stamp", JSON.STRING dep_stamp)]

(* Preserve effective values across fresh worker processes.  The default
   mono_instances value is special: setting it would impose an explicit cap
   instead of allowing each prover's own cap. *)
fun eval_hammer_options () =
  List.mapPartial (fn (key, value, source) =>
    if key = "mono_instances" andalso source = "default" then NONE
    else SOME (key, value)) (hhConfig.hh_params ())

fun json_hammer_options () =
  JSON.OBJECT (map (fn (key, value) => (key, JSON.STRING value))
    (eval_hammer_options ()))

fun header_json
    {expname, date, host, hol_commit, provers, corpus, added_from_dat,
     conditions, sample} =
  JSON.OBJECT
    [("schema", JSON.INT 4),
     ("expname", JSON.STRING expname), ("date", JSON.STRING date),
     ("host", JSON.STRING host), ("hol_commit", JSON.STRING hol_commit),
     ("provers", JSON.ARRAY (map json_prover provers)),
     ("corpus", JSON.ARRAY (map json_corpus_entry corpus)),
     ("added_from_dat", JSON.ARRAY (map JSON.STRING added_from_dat)),
     ("conditions", JSON.ARRAY (map json_condition conditions)),
     ("sample", JSON.INT (IntInf.fromInt sample)),
     ("hammer_options", json_hammer_options ())]

fun write_run_header expdir header =
  let
    val _ = ensure_dir expdir
    val output = TextIO.openOut (join expdir "run.json")
    val _ = JSONPrinter.printFmt (output, header_json header)
    val _ = TextIO.output (output, "\n")
    val _ = TextIO.flushOut output
    val _ = TextIO.closeOut output
  in
    ()
  end

fun validate_run_header expdir header =
  let
    val saved = JSONParser.parseFile (join expdir "run.json")
    val requested = header_json header
    fun check name =
      case optional_field name saved of
          NONE => raise Fail ("cannot resume evaluation: run.json lacks " ^
            name ^ "; use a new experiment name")
        | SOME value =>
            if JSONPrinter.valueToString value =
               JSONPrinter.valueToString (field name requested) then ()
            else raise Fail ("cannot resume evaluation: " ^ name ^
              " differs from run.json; use a new experiment name")
  in
    app check ["schema", "expname", "conditions", "sample", "corpus",
      "hammer_options"]
  end

fun sample_hash text =
  let
    val modulus = IntInf.fromInt 2147483647
    fun step (character, value) =
      IntInf.mod (value * 65599 + IntInf.fromInt (Char.ord character), modulus)
  in
    List.foldl step 0 (String.explode text)
  end

fun sample_goal factor goal_id =
  if factor < 1 then raise Fail "--sample must be a positive integer"
  else IntInf.mod (sample_hash goal_id, IntInf.fromInt factor) = 0

fun goal_partition {part, parts} goal_id =
  if parts < 1 then raise Fail "partition count must be positive"
  else if part < 0 orelse part >= parts then
    raise Fail "partition index is outside its partition count"
  else IntInf.mod (sample_hash goal_id, IntInf.fromInt parts) =
    IntInf.fromInt part

(* -------------------------------------------------------------------------
   Experiment reports
   ------------------------------------------------------------------------- *)

type metrics =
  {goals : int, attempted : int, proved : int, reconstructed : int,
   proved_pct : real option, reconstructed_pct : real option,
   p50 : real option, p90 : real option, maximum : real option}

fun journal_files expdir =
  let
    val directory = join expdir "journal"
    fun is_journal name = String.isSuffix ".jsonl" name
  in
    dict_sort String.compare
      (List.filter is_journal (directory_names directory))
  end

fun cell_key entry = (#goal_id entry, #cond entry)

fun latest_cells entries =
  let
    fun add_latest (entry, (seen, cells)) =
      let val key = cell_key entry in
        if Binaryset.member (seen, key) then (seen, cells)
        else (Binaryset.add (seen, key), entry :: cells)
      end
    val (_, cells) = List.foldr add_latest
      (Binaryset.empty cell_key_compare, []) entries
  in
    List.rev cells
  end

fun regular_cell entry =
  #cond entry <> "__load__" andalso #thm entry <> "__load__"

fun prover_cell entry =
  case #engine entry of Prover _ => true | Sched _ => false

fun sched_cell entry = not (prover_cell entry)

fun goal_ids entries predicate =
  sorted_unique (map #goal_id (List.filter predicate entries))

fun proven_cell entry = #szs entry = "Theorem"
fun reconstructed_cell entry = #recon_ok entry = SOME true
fun attempted_cell entry = #szs entry <> "BrokenDeps"

fun quantiles values =
  case dict_sort Real.compare values of
      [] => (NONE, NONE, NONE)
    | ordered =>
        let
          val sorted = Vector.fromList ordered
          val count = Vector.length sorted
          val p50_index = (count + 1) div 2 - 1
          val p90_index = (9 * count + 9) div 10 - 1
        in
          (SOME (Vector.sub (sorted, p50_index)),
           SOME (Vector.sub (sorted, p90_index)),
           SOME (Vector.sub (sorted, count - 1)))
        end

fun percentage numerator denominator =
  if denominator = 0 then NONE
  else SOME (100.0 * Real.fromInt numerator / Real.fromInt denominator)

fun make_metrics entries : metrics =
  let
    val goals = length (goal_ids entries (fn _ => true))
    val attempted = length (goal_ids entries attempted_cell)
    val proved = length (goal_ids entries proven_cell)
    val reconstructed = length (goal_ids entries reconstructed_cell)
    fun cell_time entry =
      case #engine entry of
          Prover _ => #t_prover entry
        | Sched _ =>
            (case #t_total entry of
                 SOME total => total
               | NONE => #t_prover entry)
    val times = map cell_time (List.filter proven_cell entries)
    val (p50, p90, maximum) = quantiles times
  in
    {goals = goals, attempted = attempted, proved = proved,
     reconstructed = reconstructed, proved_pct = percentage proved attempted,
     reconstructed_pct = percentage reconstructed attempted, p50 = p50,
     p90 = p90, maximum = maximum}
  end

fun json_int number = JSON.INT (IntInf.fromInt number)

fun json_metrics
    {goals, attempted, proved, reconstructed, proved_pct, reconstructed_pct,
     p50, p90, maximum} =
  JSON.OBJECT
    [("goals", json_int goals), ("attempted", json_int attempted),
     ("proved", json_int proved),
     ("proved_pct", json_real_option proved_pct),
     ("reconstructed", json_int reconstructed),
     ("reconstructed_pct", json_real_option reconstructed_pct),
     ("t_prover_p50", json_real_option p50),
     ("t_prover_p90", json_real_option p90),
     ("t_prover_max", json_real_option maximum)]

fun entries_for_condition name entries =
  List.filter (fn entry => #cond entry = name) entries

fun subset_metrics want entries =
  if List.exists (fn entry => #ho entry = NONE) entries then NONE
  else SOME (make_metrics (List.filter (fn entry => #ho entry = SOME want)
    entries))

fun fresh_subset_metrics want entries =
  if List.exists (fn entry => #fresh entry = NONE) entries then NONE
  else SOME (make_metrics (List.filter
    (fn entry => #fresh entry = SOME want) entries))

fun subset_json label metrics =
  JSON.OBJECT
    [("subset", JSON.STRING label),
     ("metrics", case metrics of NONE => JSON.NULL | SOME value =>
       json_metrics value)]

fun condition_json name entries =
  let
    val first = hd entries
    val schedule_fields =
      case #engine first of
          Prover _ => []
        | Sched {provers, slices, cores, max_proofs} =>
            [("engine", JSON.STRING "sched"),
             ("provers", JSON.ARRAY (map JSON.STRING provers)),
             ("requested_slices", json_int slices),
             ("cores", json_int cores), ("max_proofs", json_int max_proofs)]
  in
    JSON.OBJECT
       ([("cond", JSON.STRING name), ("regime",
        JSON.STRING (string_of_regime (#regime first))),
       ("selector", JSON.STRING (string_of_selector (#selector first))),
       ("filter", JSON.STRING (filter_of_selector (#selector first))),
       ("prover", JSON.STRING (#prover first)),
       ("timeout", json_int (#timeout first)),
       ("metrics", json_metrics (make_metrics entries)),
       ("subsets", JSON.ARRAY
         [subset_json "HO" (subset_metrics true entries),
          subset_json "non-HO" (subset_metrics false entries)]),
       ("fresh_subsets", JSON.ARRAY
         [subset_json "seen" (fresh_subset_metrics false entries),
          subset_json "fresh" (fresh_subset_metrics true entries)])] @
       schedule_fields)
  end

type slice_contribution =
  {format : string, type_enc : string, lam_trans : string, prover : string,
   filter : string, nfacts : int, wins : int, reconstructed : int}

fun winning_slice_fields entry =
  case #engine entry of
      Prover _ => SOME ("fof", "", "", #prover entry,
        filter_of_selector (#selector entry), #nfacts entry)
    | Sched _ =>
        (case #winner entry of
             NONE => NONE
           | SOME slice =>
               SOME (#format slice, #type_enc slice, #lam_trans slice,
                 #prover slice, #filter slice, #nfacts slice))

fun slice_contributions entries : slice_contribution list =
  let
    fun add entry rows =
      case winning_slice_fields entry of
          NONE => rows
        | SOME (format, type_enc, lam_trans, prover, filter, nfacts) =>
            let
              fun same {format = old_format, type_enc = old_enc,
                        lam_trans = old_lam, prover = old_prover,
                        filter = old_filter, nfacts = old_nfacts, ...} =
                format = old_format andalso type_enc = old_enc andalso
                lam_trans = old_lam andalso prover = old_prover andalso
                filter = old_filter andalso
                nfacts = old_nfacts
              val reconstructed = if reconstructed_cell entry then 1 else 0
            in
              case List.partition same rows of
                  ([], rest) =>
                    {format = format, type_enc = type_enc,
                     lam_trans = lam_trans, prover = prover, filter = filter,
                     nfacts = nfacts,
                     wins = 1, reconstructed = reconstructed} :: rest
                | (old :: _, rest) =>
                    {format = #format old, type_enc = #type_enc old,
                     lam_trans = #lam_trans old, prover = #prover old,
                     filter = #filter old, nfacts = #nfacts old,
                     wins = #wins old + 1,
                     reconstructed = #reconstructed old + reconstructed} :: rest
            end
    fun key row =
      #format row ^ "\000" ^ #type_enc row ^ "\000" ^ #lam_trans row ^
      "\000" ^ #prover row ^ "\000" ^ #filter row ^ "\000" ^
      Int.toString (#nfacts row)
  in
    dict_sort (fn (left, right) => String.compare (key left, key right))
      (List.foldl (fn (entry, rows) => add entry rows) []
        (List.filter proven_cell entries))
  end

fun contribution_json row =
  JSON.OBJECT
    [("format", JSON.STRING (#format row)),
     ("type_enc", JSON.STRING (#type_enc row)),
     ("lam_trans", JSON.STRING (#lam_trans row)),
     ("prover", JSON.STRING (#prover row)), ("nfacts", json_int (#nfacts row)),
     ("filter", JSON.STRING (#filter row)),
     ("wins", json_int (#wins row)),
     ("reconstructed", json_int (#reconstructed row))]

fun encoding_text "" = "legacy"
  | encoding_text text = text

fun contribution_markdown row =
  "| " ^ #format row ^ " | " ^ encoding_text (#type_enc row) ^ " | " ^
  (if #lam_trans row = "" then "legacy" else #lam_trans row) ^ " | " ^
  #prover row ^ " | " ^ #filter row ^ " | " ^
  Int.toString (#nfacts row) ^ " | " ^
  Int.toString (#wins row) ^ " | " ^ Int.toString (#reconstructed row) ^
  " |\n"

fun portfolio_key entry =
  string_of_regime (#regime entry) ^ "/" ^
  Int.toString (#timeout entry) ^ "s"

fun entries_for_key key entries =
  List.filter (fn entry => portfolio_key entry = key) entries

fun proof_ids entries = goal_ids entries proven_cell
fun reconstruction_ids entries = goal_ids entries reconstructed_cell

fun unique_count prover ids_of entries =
  let
    val own = ids_of (List.filter (fn entry => #prover entry = prover) entries)
    val others = Binaryset.addList (Binaryset.empty String.compare,
      ids_of (List.filter (fn entry => #prover entry <> prover) entries))
  in
    length (List.filter (fn goal => not (Binaryset.member (others, goal))) own)
  end

fun portfolio_prover_json prover entries =
  JSON.OBJECT
    [("prover", JSON.STRING prover),
     ("unique_proved", json_int (unique_count prover proof_ids entries)),
     ("unique_reconstructed",
      json_int (unique_count prover reconstruction_ids entries))]

fun portfolio_json key entries =
  let
    val first = hd entries
    val provers = sorted_unique (map #prover entries)
  in
    JSON.OBJECT
      [("key", JSON.STRING key), ("regime",
        JSON.STRING (string_of_regime (#regime first))),
       ("selectors", JSON.ARRAY (map JSON.STRING
        (sorted_unique (map (string_of_selector o #selector) entries)))),
       ("timeout", json_int (#timeout first)),
       ("condition_ids", JSON.ARRAY
        (map JSON.STRING (sorted_unique (map #cond entries)))),
       ("metrics", json_metrics (make_metrics entries)),
       ("provers", JSON.ARRAY
        (map (fn prover => portfolio_prover_json prover entries) provers))]
  end

fun theory_json theory entries =
  let
    val in_theory = List.filter (fn entry => #thy entry = theory) entries
    val conditions = sorted_unique (map #cond in_theory)
  in
    JSON.OBJECT
      [("theory", JSON.STRING theory), ("conditions", JSON.ARRAY
        (map (fn name => condition_json name
          (entries_for_condition name in_theory)) conditions))]
  end

fun count value values =
  length (List.filter (fn other => other = value) values)

fun schedule_distribution_json name entries =
  let
    val slice_counts = map (length o #slices) entries
    val stops = sorted_unique (List.mapPartial #stop entries)
    val slice_values =
      Portable.sort (fn left => fn right => left <= right)
        (mk_sameorder_set Int.compare slice_counts)
  in
    JSON.OBJECT
      [("cond", JSON.STRING name),
       ("slices_run", JSON.ARRAY (map (fn value => JSON.OBJECT
          [("value", json_int value),
           ("count", json_int (count value slice_counts))]) slice_values)),
       ("stop_reasons", JSON.ARRAY (map (fn value => JSON.OBJECT
          [("value", JSON.STRING value),
           ("count", json_int (count value
             (List.mapPartial #stop entries)))]) stops))]
  end

fun comparison_json name key schedule_entries union_entries =
  let
    val schedule_metrics = make_metrics schedule_entries
    val union_metrics = make_metrics union_entries
  in
    JSON.OBJECT
      [("condition", JSON.STRING name), ("portfolio", JSON.STRING key),
       ("schedule", json_metrics schedule_metrics),
       ("union", json_metrics union_metrics),
       ("proved_delta", json_int
          (#proved schedule_metrics - #proved union_metrics)),
       ("reconstructed_delta", json_int
          (#reconstructed schedule_metrics - #reconstructed union_metrics))]
  end

fun option_text NONE = "-"
  | option_text (SOME number) = Real.fmt (StringCvt.FIX (SOME 2)) number

fun metrics_markdown metrics =
  Int.toString (#goals metrics) ^ " | " ^
  Int.toString (#attempted metrics) ^ " | " ^
  Int.toString (#proved metrics) ^ " | " ^
  option_text (#proved_pct metrics) ^ " | " ^
  Int.toString (#reconstructed metrics) ^ " | " ^
  option_text (#reconstructed_pct metrics) ^ " | " ^
  option_text (#p50 metrics) ^ " | " ^ option_text (#p90 metrics) ^
  " | " ^ option_text (#maximum metrics)

fun subset_markdown condition label metrics =
  case metrics of
      NONE => "| " ^ condition ^ " | " ^ label ^ " | n/a |\n"
    | SOME value => "| " ^ condition ^ " | " ^ label ^ " | " ^
        metrics_markdown value ^ " |\n"

fun condition_markdown name entries =
  let
    val first = hd entries
    val engine =
      case #engine first of Prover _ => #prover first | Sched _ => "schedule"
  in
    "| " ^ name ^ " | " ^ engine ^ " | " ^
    filter_of_selector (#selector first) ^ " | " ^
    metrics_markdown (make_metrics entries) ^ " |\n"
  end

fun portfolio_markdown key entries =
  "| " ^ key ^ " | " ^ metrics_markdown (make_metrics entries) ^ " |\n"

fun theory_markdown theory name entries =
  "| " ^ theory ^ " | " ^ name ^ " | " ^
  metrics_markdown (make_metrics entries) ^ " |\n"

fun int_distribution values =
  let
    val distinct = Portable.sort (fn left => fn right => left <= right)
      (mk_sameorder_set Int.compare values)
  in
    if null distinct then "-"
    else String.concatWith ", " (map (fn value =>
      Int.toString value ^ ":" ^ Int.toString (count value values)) distinct)
  end

fun string_distribution values =
  let val distinct = sorted_unique values in
    if null distinct then "-"
    else String.concatWith ", " (map (fn value =>
      value ^ ":" ^ Int.toString (count value values)) distinct)
  end

fun schedule_distribution_markdown name entries =
  "| " ^ name ^ " | " ^ int_distribution (map (length o #slices) entries) ^
  " | " ^ string_distribution (List.mapPartial #stop entries) ^ " |\n"

fun comparison_markdown name key schedule_entries union_entries =
  let
    val schedule = make_metrics schedule_entries
    val union = make_metrics union_entries
    fun signed number =
      if number < 0 then "-" ^ Int.toString (~number)
      else Int.toString number
  in
    "| " ^ name ^ " | " ^ key ^ " | " ^
    Int.toString (#proved schedule) ^ " | " ^ Int.toString (#proved union) ^
    " | " ^ signed (#proved schedule - #proved union) ^ " | " ^
    Int.toString (#reconstructed schedule) ^ " | " ^
    Int.toString (#reconstructed union) ^ " | " ^
    signed (#reconstructed schedule - #reconstructed union) ^ " |\n"
  end

fun write_report_markdown expdir entries =
  let
    val conditions = sorted_unique (map #cond entries)
    val prover_entries = List.filter prover_cell entries
    val schedule_entries = List.filter sched_cell entries
    val schedule_conditions = sorted_unique (map #cond schedule_entries)
    val portfolios = sorted_unique (map portfolio_key prover_entries)
    val theories = sorted_unique (map #thy entries)
    fun comparison name =
      let
        val cells = entries_for_condition name schedule_entries
        val key = portfolio_key (hd cells)
        val union = entries_for_key key prover_entries
      in
        if null union then NONE else SOME (name, key, cells, union)
      end
    val comparisons = List.mapPartial comparison schedule_conditions
    val contributions = slice_contributions entries
    val output = TextIO.openOut (join expdir "report.md")
    val _ = TextIO.output (output, "# hhEval report\n\n")
    val _ = TextIO.output (output,
      "Partial journals are reported as observed cells only. For schedule " ^
      "runs, size `ncore` to `machine_cores div cores_per_cell`; peak prover " ^
      "load is `ncore × cores_per_cell`.\n\n")
    val _ = TextIO.output (output,
      "## Conditions\n\n| condition | prover | filter | G | A | P | P% | " ^
      "R | R% | p50 | p90 | max |\n|---|---|---|---:|---:|---:|" ^
      "---:|---:|---:|---:|---:|---:|\n")
    val _ = app (fn name => TextIO.output (output,
      condition_markdown name (entries_for_condition name entries))) conditions
    val _ = TextIO.output (output,
      "\n## HO subsets\n\n| condition | subset | G | A | P | P% | R | R% | " ^
      "p50 | p90 | max |\n|---|---|---:|---:|---:|---:|---:|---:|" ^
      "---:|---:|---:|\n")
    val _ = app (fn name =>
      let val cells = entries_for_condition name entries in
        TextIO.output (output, subset_markdown name "HO"
          (subset_metrics true cells));
        TextIO.output (output, subset_markdown name "non-HO"
          (subset_metrics false cells))
      end) conditions
    val _ = TextIO.output (output,
      "\n## Seen/fresh subsets\n\n| condition | filter | subset | G | A | " ^
      "P | P% | R | R% | p50 | p90 | max |\n|---|---|---|---:|---:|" ^
      "---:|---:|---:|---:|---:|---:|---:|\n")
    val _ = app (fn name =>
      let
        val cells = entries_for_condition name entries
        val filter = filter_of_selector (#selector (hd cells))
        fun row label metrics =
          case metrics of
              NONE => "| " ^ name ^ " | " ^ filter ^ " | " ^ label ^
                " | n/a |\n"
            | SOME value => "| " ^ name ^ " | " ^ filter ^ " | " ^
                label ^ " | " ^ metrics_markdown value ^ " |\n"
      in
        TextIO.output (output, row "seen" (fresh_subset_metrics false cells));
        TextIO.output (output, row "fresh" (fresh_subset_metrics true cells))
      end) conditions
    val _ = TextIO.output (output,
      "\n## Slice contributions\n\n| format | encoding | lambda | prover | " ^
      "filter | facts | wins | reconstructed |\n" ^
      "|---|---|---|---|---|---:|---:|---:|\n")
    val _ = app (fn row => TextIO.output (output, contribution_markdown row))
      contributions
    val _ = TextIO.output (output,
      "\n## Portfolio unions\n\n| portfolio | G | A | P | P% | R | R% | " ^
      "p50 | p90 | max |\n|---|---:|---:|---:|---:|---:|---:|---:|" ^
      "---:|---:|\n")
    val _ = app (fn key => TextIO.output (output,
      portfolio_markdown key (entries_for_key key prover_entries))) portfolios
    val _ = TextIO.output (output,
      "\n## Unique solves\n\n| portfolio | prover | proved | " ^
      "reconstructed |\n|---|---|---:|---:|\n")
    fun unique_rows key =
      let
        val cells = entries_for_key key prover_entries
        fun row prover = TextIO.output (output,
          "| " ^ key ^ " | " ^ prover ^ " | " ^
          Int.toString (unique_count prover proof_ids cells) ^ " | " ^
          Int.toString (unique_count prover reconstruction_ids cells) ^
          " |\n")
      in
        app row (sorted_unique (map #prover cells))
      end
    val _ = app unique_rows portfolios
    val _ =
      if null schedule_conditions then ()
      else
        (TextIO.output (output,
           "\n## Schedule distributions\n\n| condition | slices run " ^
           "(value:count) | stop reasons (value:count) |\n" ^
           "|---|---|---|\n");
         app (fn name => TextIO.output (output,
           schedule_distribution_markdown name
             (entries_for_condition name schedule_entries)))
           schedule_conditions)
    val _ =
      if null comparisons then ()
      else
        (TextIO.output (output,
           "\n## Schedule vs portfolio union\n\n| schedule | portfolio | " ^
           "S P | U P | ΔP | S R | U R | ΔR |\n" ^
           "|---|---|---:|---:|---:|---:|---:|---:|\n");
         app (fn (name, key, schedule, union) => TextIO.output (output,
           comparison_markdown name key schedule union)) comparisons)
    val _ = TextIO.output (output,
      "\n## Theories\n\n| theory | condition | G | A | P | P% | R | R% | " ^
      "p50 | p90 | max |\n|---|---|---:|---:|---:|---:|---:|---:|" ^
      "---:|---:|---:|\n")
    fun theory_rows theory =
      let
        val cells = List.filter (fn entry => #thy entry = theory) entries
        fun row name = TextIO.output (output,
          theory_markdown theory name (entries_for_condition name cells))
      in
        app row (sorted_unique (map #cond cells))
      end
    val _ = app theory_rows theories
    val _ = TextIO.closeOut output
  in
    ()
  end

fun write_summary expdir entries =
  let
    val conditions = sorted_unique (map #cond entries)
    val prover_entries = List.filter prover_cell entries
    val schedule_entries = List.filter sched_cell entries
    val schedule_conditions = sorted_unique (map #cond schedule_entries)
    val portfolios = sorted_unique (map portfolio_key prover_entries)
    val theories = sorted_unique (map #thy entries)
    val contributions = slice_contributions entries
    fun comparison name =
      let
        val cells = entries_for_condition name schedule_entries
        val key = portfolio_key (hd cells)
        val union = entries_for_key key prover_entries
      in
        if null union then NONE
        else SOME (comparison_json name key cells union)
      end
    val base =
      [("schema", JSON.STRING "hhEval-summary-v1"),
       ("conditions", JSON.ARRAY (map (fn name => condition_json name
         (entries_for_condition name entries)) conditions)),
       ("portfolios", JSON.ARRAY (map (fn key => portfolio_json key
         (entries_for_key key prover_entries)) portfolios)),
       ("slice_contributions", JSON.ARRAY
         (map contribution_json contributions)),
       ("theories", JSON.ARRAY (map (fn theory => theory_json theory entries)
         theories))]
    val schedule_fields =
      if null schedule_conditions then []
      else
        [("schedule_distributions", JSON.ARRAY (map (fn name =>
            schedule_distribution_json name
              (entries_for_condition name schedule_entries))
            schedule_conditions)),
         ("schedule_vs_union", JSON.ARRAY
            (List.mapPartial comparison schedule_conditions))]
    val summary = JSON.OBJECT (base @ schedule_fields)
    val output = TextIO.openOut (join expdir "summary.json")
    val _ = JSONPrinter.printFmt (output, summary)
    val _ = TextIO.output (output, "\n")
    val _ = TextIO.flushOut output
    val _ = TextIO.closeOut output
  in
    ()
  end

fun report expdir =
  let
    val paths = map (join (join expdir "journal")) (journal_files expdir)
    val entries = List.filter regular_cell
      (latest_cells (List.concat (map read_journal paths)))
    val _ = ensure_dir expdir
    val _ = write_report_markdown expdir entries
  in
    write_summary expdir entries
  end

(* -------------------------------------------------------------------------
   Evaluation driver and per-theory workers
   ------------------------------------------------------------------------- *)

val worker_conditions = ref ([] : condition list)
val worker_sample = ref 1
val worker_partition = ref (NONE : {part : int, parts : int} option)
val worker_goal_ids = ref (NONE : string Binaryset.set option)

fun set_worker_settings {conditions, sample} =
  if sample < 1 then raise Fail "eval.sample must be a positive integer"
  else
    (app validate_condition conditions;
     worker_conditions := conditions;
     worker_sample := sample;
     worker_partition := NONE;
     worker_goal_ids := NONE)

fun set_worker_goal_ids ids =
  let
    val goals = Binaryset.addList (Binaryset.empty String.compare, ids)
  in
    if null ids then raise Fail "worker goal inventory must be nonempty"
    else if Binaryset.numItems goals <> length ids then
      raise Fail "worker goal inventory contains duplicates"
    else worker_goal_ids := SOME goals
  end

fun set_worker_partition partition =
  (ignore (goal_partition partition "");
   worker_partition := SOME partition)

fun worker_selects goal_id =
  sample_goal (!worker_sample) goal_id andalso
  (case !worker_goal_ids of
       NONE => true
     | SOME goals => Binaryset.member (goals, goal_id)) andalso
  (case !worker_partition of
       NONE => true
     | SOME partition => goal_partition partition goal_id)

fun worker_journal_path expdir thy =
  case !worker_partition of
      NONE => journal_path expdir thy
    | SOME {part, parts} =>
        journal_path expdir
          (thy ^ ".part-" ^ Int.toString part ^ "-of-" ^
           Int.toString parts)

fun run_name expdir = OS.Path.file expdir

fun safe_component text =
  String.map (fn character =>
    if Char.isAlphaNum character orelse character = #"_" orelse
       character = #"-" then character else #"_") text

fun goal_id thy name = thy ^ "." ^ name

fun szs_name hhProver.SzsTheorem = "Theorem"
  | szs_name hhProver.SzsCounterSat = "CounterSatisfiable"
  | szs_name hhProver.SzsSatisfiable = "Satisfiable"
  | szs_name hhProver.SzsGaveUp = "GaveUp"
  | szs_name hhProver.SzsTimeout = "Timeout"
  | szs_name hhProver.SzsResourceOut = "ResourceOut"
  | szs_name hhProver.SzsInappropriate = "Inappropriate"
  | szs_name (hhProver.SzsUnknown name) = name
  | szs_name (hhProver.RunFailure _) = "RunFailure"

fun run_failure_error (hhProver.RunFailure message) = SOME message
  | run_failure_error _ = NONE

(* The tail of a journal entry, i.e. everything only known once the prover
   has run.  Keeping it a separate record means the entry is built in one
   place: adding a journal field touches base_entry and nothing else. *)
type outcome =
  {recon_ok : bool option, recon_method : string option,
   t_recon : real option, stac : string option, error : string option}

val no_outcome : outcome =
  {recon_ok = NONE, recon_method = NONE, t_recon = NONE, stac = NONE,
   error = NONE}

fun failed message : outcome =
  {recon_ok = NONE, recon_method = NONE, t_recon = NONE, stac = NONE,
   error = SOME message}

fun base_entry expdir thy name condition ho fresh nfacts szs t_prover axioms
    version (outcome : outcome) =
  {run = run_name expdir, thy = thy, thm = name, goal_id = goal_id thy name,
   cond = #cond_id condition, regime = #regime condition,
   selector = #selector condition, engine = #engine condition, ho = ho,
   fresh = fresh,
   prover = (case #engine condition of Prover name => name | Sched _ => ""),
   prover_version = version, nfacts = nfacts, timeout = #timeout condition,
   szs = szs, t_prover = t_prover, axioms_used = axioms,
   recon_ok = #recon_ok outcome, recon_method = #recon_method outcome,
   t_recon = #t_recon outcome, stac = #stac outcome,
   error = #error outcome,
   stop = (case #engine condition of
                Prover _ => NONE
              | Sched _ => SOME "Unavailable"),
   t_total = (case #engine condition of
                  Prover _ => NONE
                | Sched _ => SOME 0.0),
   winner = NONE, slices = []} : journal_entry

fun append_theory_error path expdir thy message =
  let
    val condition : condition =
      {cond_id = "__load__", regime = Bushy, selector = Deps,
       engine = Prover "", timeout = 0, reconstruct = false}
  in
    append_journal path
      (base_entry expdir thy "__load__" condition NONE NONE 0 "LoadFailure"
         0.0 NONE NONE (failed message))
  end

fun journal_theory_error expdir thy message =
  append_theory_error (journal_path expdir thy) expdir thy message

fun pool_ids (thyl, thmidl) =
  map (fn (theory, name) => theory ^ "Theory." ^ name)
    (List.concat (map hhExportLib.thmidl_in_thy thyl) @ thmidl)

fun chainy_pools thy =
  let
    val order = hhExportLib.sorted_ancestry [thy]
    val earlier_theories =
      if List.exists (fn name => name = thy) order then
        hhExportLib.before_elem thy order
      else order
    fun one (name, thm) =
      let
        val earlier_theorems =
          List.filter (hhExportLib.older_than thm) (DB.thms thy)
        val current_ids = map (fn (other, _) => (thy, other)) earlier_theorems
      in
        (name, pool_ids (earlier_theories, current_ids))
      end
  in
    map one (DB.theorems thy)
  end

fun lookup_pool name pools =
  case List.find (fn (other, _) => other = name) pools of
      SOME (_, pool) => pool
    | NONE => []

fun restrict_features_to_pool pool features =
  let val permitted = Redblackset.fromList String.compare pool in
    List.filter (fn (name, _) => Redblackset.member (permitted, name))
      features
  end

fun select_knn thy pool count goal =
  let
    val (weights, features) = hhLearn.create_thmdata_for thy
    val permitted = restrict_features_to_pool pool features
  in
    mlNearestNeighbor.thmknn_wdep (weights, permitted) count
      (mlFeature.fea_of_goal true goal)
  end

fun select_filter thy filter pool count goal =
  let
    val thmdata = hhLearn.create_thmdata_for thy
    val context = hhLearn.create_context_for thy thmdata
  in
    hhLearn.rank context
      {filter = filter, pool = SOME pool, goal = goal, n = count}
  end

fun selected_premises_at thy condition pool thm goal knn_count =
  case #selector condition of
      Deps =>
        let val dependencies = #2 (mlThmData.intactdep_of_thm thm) in
          case #regime condition of
              Bushy => dependencies
            | Chainy => List.filter (fn name =>
                List.exists (fn allowed => allowed = name) pool) dependencies
        end
    | Knn count => select_knn thy pool
        (case knn_count of NONE => count | SOME maximum => maximum) goal
    | Mepo count => select_filter thy "mepo" pool count goal
    | Mash count => select_filter thy "mash" pool count goal
    | Mesh count => select_filter thy "mesh" pool count goal
    | PerSlice => raise Fail
        "invalid hhEval premise selection: perslice requires Sched"

fun selected_premises thy condition pool thm goal =
  selected_premises_at thy condition pool thm goal NONE

fun json_string_list values =
  JSONPrinter.valueToString (JSON.ARRAY (map JSON.STRING values))

fun reconstruct condition result goal =
  if not (#reconstruct condition) orelse
     #szs result <> hhProver.SzsTheorem then
    (NONE, NONE, NONE, NONE)
  else
    case #used_axioms result of
        NONE => (NONE, NONE, NONE, NONE)
      | SOME axioms =>
          ((let
              val ({stac, method, ...}, elapsed) =
                add_time (hhReconstruct.preplay true axioms) goal
            in
              (SOME true, SOME method, SOME elapsed, SOME stac)
            end)
           handle Interrupt => raise Interrupt
                | error =>
                    (SOME false, NONE, NONE,
                     SOME (General.exnMessage error)))

fun schedule_stop_name hhSchedule.MaxProofs = "MaxProofs"
  | schedule_stop_name hhSchedule.Timeout = "Timeout"
  | schedule_stop_name hhSchedule.Exhausted = "Exhausted"
  | schedule_stop_name hhSchedule.Interrupted = "Interrupted"

fun schedule_options condition
    {provers, slices, cores, max_proofs} : hhConfig.hh_options =
  let val snapshot = hhConfig.snapshot () in
    {timeout = #timeout condition, max_proofs = max_proofs,
     provers = provers, slices = slices, cores = cores,
     filter = #filter snapshot, max_facts = #max_facts snapshot,
     format = #format snapshot, type_enc = #type_enc snapshot,
     lam_trans = #lam_trans snapshot, mono_iters = #mono_iters snapshot,
     mono_instances = #mono_instances snapshot, minimize = #minimize snapshot,
     preplay_timeout = #preplay_timeout snapshot,
     minimize_timeout = #minimize_timeout snapshot,
     cache = true, cache_dir = #cache_dir snapshot,
     cache_max_entries = #cache_max_entries snapshot, debug_dir = NONE}
  end

fun max_schedule_facts schedule =
  foldl Int.max 0 (map (#nfacts o #2) schedule)

fun rankings_for_schedule schedule premises =
  let
    fun add ((_, slice), rankings) =
      if List.exists (fn (filter, _) => filter = #filter slice) rankings then
        rankings
      else
        rankings @ [(#filter slice, premises)]
  in
    foldl add [] schedule
  end

fun filter_maxima schedule =
  let
    fun add slice [] = [(#filter slice, #nfacts slice)]
      | add slice ((filter, maximum) :: rest) =
          if #filter slice = filter then
            (filter, Int.max (maximum, #nfacts slice)) :: rest
          else
            (filter, maximum) :: add slice rest
  in
    foldl (fn ((_, slice), maxima) => add slice maxima) [] schedule
  end

fun per_slice_rankings thy schedule pool goal =
  let
    val context = hhLearn.create_context_for thy
      (hhLearn.create_thmdata_for thy)
    fun rank (filter, maximum) =
      (filter, hhLearn.rank context
        {filter = filter, pool = SOME pool, goal = goal, n = maximum})
  in
    map rank (filter_maxima schedule)
  end

fun version_of_prover name =
  case hhProver.lookup name of
      NONE => NONE
    | SOME config =>
        (case hhProver.probe config of
             NONE => NONE
           | SOME {version, ...} => version)

fun schedule_cell_entry expdir thy (name, thm) pool condition parameters =
  let
    val goal = dest_thm thm
    val options = schedule_options condition parameters
    val schedule = hhSlice.mk_schedule options
    val maximum = max_schedule_facts schedule
    val rankings =
      case #selector condition of
          PerSlice => per_slice_rankings thy schedule pool goal
        | _ =>
            let
              (* Legacy schedule selectors share one longest-first ranking.
                 In particular, chainy kNN uses the schedule maximum. *)
              val premises = selected_premises_at thy condition pool thm
                goal (SOME maximum)
            in
              rankings_for_schedule schedule premises
            end
    val proofs = ref
      ([] : (hhProver.slice * string list) list)
    fun progress (hhSchedule.ProofFound proof) = proofs := !proofs @ [proof]
      | progress _ = ()
    val result = hhSchedule.run
      {options = options, goal = goal,
       rankings = rankings,
       progress = SOME progress}
    val slices = map (fn (slice, status, elapsed, cached) =>
      {slice = slice, szs = szs_name status, time = elapsed,
       cached = cached} : journal_slice) (#slices_run result)
    fun slice_result wanted =
      List.find (fn (slice, _, _, _) =>
        same_slice slice wanted) (#slices_run result)
    fun finish winner prover nfacts szs t_prover axioms recon_ok
        recon_method t_recon stac error =
      {run = run_name expdir, thy = thy, thm = name,
       goal_id = goal_id thy name, cond = #cond_id condition,
       regime = #regime condition, selector = #selector condition,
       engine = #engine condition,
       ho = SOME (is_higher_order_goal (list_mk_imp goal)),
       fresh = SOME (is_fresh_goal thy (list_mk_imp goal)),
       prover = prover, prover_version = version_of_prover prover,
       nfacts = nfacts,
       timeout = #timeout condition, szs = szs, t_prover = t_prover,
       axioms_used = axioms, recon_ok = recon_ok,
       recon_method = recon_method, t_recon = t_recon, stac = stac,
       error = error, stop = SOME (schedule_stop_name (#stopped result)),
       t_total = SOME (#t_total result), winner = winner,
       slices = slices} : journal_entry
  in
    case #suggestions result of
        suggestion :: _ =>
          finish (SOME (#slice suggestion)) (#prover suggestion)
            (#nfacts (#slice suggestion)) "Theorem" (#t_prover suggestion)
            (SOME (#lemmas suggestion)) (SOME true)
            (SOME (#method suggestion))
            (SOME (#t_recon suggestion)) (SOME (#stac suggestion)) NONE
      | [] =>
          (case !proofs of
               (slice, lemmas) :: _ =>
                 let
                   val elapsed =
                     case slice_result slice of
                         SOME (_, _, time, _) => time
                       | NONE => 0.0
                 in
                   finish (SOME slice) (#prover slice) (#nfacts slice)
                     "Theorem" elapsed (SOME lemmas) (SOME false)
                     NONE NONE NONE
                     (SOME "ATP proof found but reconstruction failed")
                 end
             | [] =>
                 (case #slices_run result of
                      (slice, status, elapsed, _) :: _ =>
                        finish NONE (#prover slice) (#nfacts slice)
                          (szs_name status) elapsed NONE NONE NONE NONE NONE
                          (run_failure_error status)
                    | [] => finish NONE "" maximum "RunFailure" 0.0 NONE
                        NONE NONE NONE NONE
                        (SOME "schedule contained no runnable slices")))
  end

fun prover_cell_entry expdir thy (name, thm) pool condition prover_name =
  let
    val goal = dest_thm thm
    val premises = selected_premises thy condition pool thm goal
    val named_premises = mlThmData.thml_of_namel premises
    val nfacts = length named_premises
    val directory = join (join (join expdir "pb") (safe_component thy))
      (safe_component (name ^ "-" ^ #cond_id condition))
    val _ = ensure_dir directory
    val _ = hhExportFof.fof_export_pb directory
      (list_mk_imp goal, named_premises)
  in
    case hhProver.lookup prover_name of
        NONE => base_entry expdir thy name condition
          (SOME (is_higher_order_goal (list_mk_imp goal)))
          (SOME (is_fresh_goal thy (list_mk_imp goal))) nfacts
          "RunFailure" 0.0 NONE
          NONE (failed ("unknown HolyHammer prover: " ^ prover_name))
      | SOME prover =>
          let
            val result = hhProver.run prover
              {timeout = #timeout condition, format = "fof",
               problem = join directory "atp_in", extra = [],
               debug_dir = SOME (join expdir "out")}
            val (recon_ok, recon_method, t_recon, stac_or_error) =
              reconstruct condition result goal
            val (stac, recon_error) =
              case recon_ok of
                  SOME false => (NONE, stac_or_error)
                | _ => (stac_or_error, NONE)
            val outcome : outcome =
              {recon_ok = recon_ok, recon_method = recon_method,
               t_recon = t_recon, stac = stac,
               error = case recon_error of
                           SOME message => SOME message
                         | NONE => run_failure_error (#szs result)}
          in
            base_entry expdir thy name condition
              (SOME (is_higher_order_goal (list_mk_imp goal)))
              (SOME (is_fresh_goal thy (list_mk_imp goal))) nfacts
              (szs_name (#szs result)) (#time result)
              (#used_axioms result) (#version result) outcome
          end
  end

fun run_cell expdir thy theorem pool condition =
  let
    val entry =
      case #engine condition of
          Sched parameters =>
            schedule_cell_entry expdir thy theorem pool condition parameters
        | Prover prover_name =>
            prover_cell_entry expdir thy theorem pool condition prover_name
  in
    append_journal (worker_journal_path expdir thy) entry
  end
  handle Interrupt => raise Interrupt
       | error =>
           append_journal (worker_journal_path expdir thy)
             (base_entry expdir thy (#1 theorem) condition
                (SOME (is_higher_order_goal
                  (list_mk_imp (dest_thm (#2 theorem)))))
                (SOME (is_fresh_goal thy
                  (list_mk_imp (dest_thm (#2 theorem)))))
                0 "Error" 0.0 NONE NONE (failed (General.exnMessage error)))

fun broken_deps_cell expdir thy name goal condition =
  append_journal (worker_journal_path expdir thy)
    (base_entry expdir thy name condition (SOME (is_higher_order_goal goal))
       (SOME (is_fresh_goal thy goal)) 0 "BrokenDeps" 0.0 NONE NONE
       no_outcome)

fun evaluation_error_cell expdir thy name goal condition message =
  append_journal (worker_journal_path expdir thy)
    (base_entry expdir thy name condition (SOME (is_higher_order_goal goal))
       (SOME (is_fresh_goal thy goal)) 0 "Error" 0.0 NONE NONE
       (failed message))

fun eval_loaded_theory expdir thy =
  let
    val completed = read_completed (worker_journal_path expdir thy)
    val pools =
      if List.exists (fn condition => #regime condition = Chainy)
         (!worker_conditions)
      then SOME (chainy_pools thy)
           handle Interrupt => raise Interrupt | error => NONE
      else SOME []
    fun evaluate (name, thm) =
      let
        val id = goal_id thy name
        val (dependencies_ok, intact_deps) =
          mlThmData.intactdep_of_thm thm
        fun one condition =
          if cell_completed completed (id, #cond_id condition) then ()
          else
            case pools of
                NONE => evaluation_error_cell expdir thy name
                  (list_mk_imp (dest_thm thm)) condition
                  "could not construct the chainy premise pool"
              | SOME pool_map =>
                  let val pool = lookup_pool name pool_map in
                    if #regime condition = Bushy andalso not dependencies_ok
                    then broken_deps_cell expdir thy name
                      (list_mk_imp (dest_thm thm)) condition
                    else run_cell expdir thy (name, thm)
                      (case #regime condition of
                           Bushy => intact_deps
                         | Chainy => pool)
                      condition
                  end
      in
        if worker_selects id then app one (!worker_conditions)
        else ()
      end
  in
    app evaluate (DB.theorems thy)
  end

fun eval_thy expdir thy =
  (eval_loaded_theory expdir thy
   handle Interrupt => raise Interrupt
        | error => append_theory_error (worker_journal_path expdir thy)
            expdir thy (General.exnMessage error))

fun worker_theory_complete expdir thy =
  let
    fun cells (name, _) =
      let val id = goal_id thy name in
        if worker_selects id then
          map (fn condition => (id, #cond_id condition)) (!worker_conditions)
        else []
      end
    val expected =
      case !worker_goal_ids of
          NONE => List.concat (map cells (DB.theorems thy))
        | SOME goals =>
            List.concat
              (map (fn id =>
                 if worker_selects id then
                   map (fn condition => (id, #cond_id condition))
                     (!worker_conditions)
                 else [])
               (Binaryset.listItems goals))
  in
    journal_complete (worker_journal_path expdir thy)
      expected
  end

fun condition_text condition =
  "hhEval.parse_condition " ^ Portable.mlquote (encode_condition condition)

val source_script_directories = ref (NONE : (string * string) list option)

fun source_script_directory thy =
  let
    fun source_entry line =
      let
        val path = trim line
        val file = OS.Path.file path
      in
        if String.isSuffix "Theory" file then
          SOME (String.substring (file, 0, String.size file - 6),
                OS.Path.dir path)
        else NONE
      end
    fun dat_entry path =
      let val file = OS.Path.file path in
        if String.isSuffix "Theory.dat" file then
          SOME (String.substring (file, 0, String.size file - 10),
                OS.Path.dir (OS.Path.dir (OS.Path.dir path)))
        else NONE
      end
    fun directories () =
      case !source_script_directories of
          SOME result => result
        | NONE =>
            let
              val root = holdir ()
              val srcfiles = read_lines
                (join (join root "sigobj") "SRCFILES")
              val result = List.mapPartial source_entry srcfiles @
                List.mapPartial dat_entry (dat_paths_under (join root "src"))
              val _ = source_script_directories := SOME result
            in
              result
            end
  in
    case List.find (fn (name, _) => name = thy) (directories ()) of
        SOME (_, directory) => directory
      | NONE => raise Fail ("no source directory for theory " ^ thy)
  end

fun load_theory thy =
  let
    val old_directory = OS.FileSys.getDir ()
    fun restore () = OS.FileSys.chDir old_directory
    val _ = OS.FileSys.chDir (source_script_directory thy)
  in
    (load (thy ^ "Theory") before restore ())
    handle error => (restore (); raise error)
  end

fun write_evalscript expdir thy conditions sample =
  let
    (* A theory UI is found relative to its source directory.  In
       particular, a script in <expdir>/scripts run from hol.state cannot
       load theories outside the default heap. *)
    val scripts = source_script_directory thy
    val path = join scripts
      (".hheval_" ^ safe_component (OS.Path.file expdir) ^ "_" ^
       safe_component thy ^ ".sml")
    val conditions_text = String.concatWith ", " (map condition_text conditions)
    val hammer_settings = String.concat (map (fn (key, value) =>
      "val _ = hhConfig.hh_set (" ^ Portable.mlquote key ^ ", " ^
      Portable.mlquote value ^ ");\n") (eval_hammer_options ()))
    val settings =
      "val _ = hhEval.set_worker_settings {conditions = [" ^
      conditions_text ^ "], sample = " ^ Int.toString sample ^ "};"
    val action = "val _ = hhEval.eval_thy " ^ Portable.mlquote expdir ^
      " " ^ Portable.mlquote thy ^ ";"
    val worker_theory = "hheval_worker_" ^ safe_component thy
    val output = TextIO.openOut path
    val _ = TextIO.output (output,
      "load \"BasicProvers\";\n" ^
      "load " ^ Portable.mlquote (thy ^ "Theory") ^ ";\n" ^
      "val _ = Feedback.quiet_messages Theory.new_theory " ^
      Portable.mlquote worker_theory ^ ";\n" ^
      "load \"hhEval\";\n" ^ hammer_settings ^ settings ^ "\n" ^
      action ^ "\n")
    val _ = TextIO.closeOut output
  in
    path
  end

fun configured_sample () =
  case hhConfig.get_int "eval.sample" of
      NONE => 1
    | SOME sample =>
        if sample < 1 then raise Fail "eval.sample must be a positive integer"
        else sample

fun theory_cells thy conditions sample =
  let
    val _ = load_theory thy
    fun cells (name, _) =
      let val id = goal_id thy name in
        if sample_goal sample id then map (fn condition =>
          (id, #cond_id condition)) conditions
        else []
      end
  in
    SOME (List.concat (map cells (DB.theorems thy)))
  end
  handle Interrupt => raise Interrupt | _ => NONE

fun run_eval {expname, ncore, thyl, conditions} =
  if ncore < 1 then raise Fail "run_eval requires at least one worker"
  else
    let
      val _ = app validate_condition conditions
      val sample = configured_sample ()
      val expdir = experiment_dir expname
      val _ = ensure_dir expdir
      val _ = ensure_dir (join expdir "journal")
      val _ = ensure_dir (join expdir "out")
      val _ = ensure_dir (join expdir "pb")
      val _ = ensure_dir (join expdir "scripts")
      val {added_from_dat, ...} = stdlib_coverage ()
      val included_from_dat = List.filter (fn name =>
        List.exists (fn thy => thy = name) thyl) added_from_dat
      fun corpus_entry thy =
        ((load_theory thy; loaded_corpus_entry thy)
         handle Interrupt => raise Interrupt
              | _ => {thy = thy, theorem_count = 0, dep_stamp = ""})
      val header =
        new_run_header {expname = expname, corpus = map corpus_entry thyl,
            added_from_dat = included_from_dat,
            conditions = conditions, sample = sample}
      val _ =
        if exists_file (join expdir "run.json") then
          validate_run_header expdir header
        else write_run_header expdir header
      val states = map (fn thy =>
        (thy, theory_cells thy conditions sample)) thyl
      fun pending (thy, NONE) =
            (journal_theory_error expdir thy
               "theory could not be loaded by the evaluation driver";
             false)
        | pending (thy, SOME cells) =
            not (journal_complete (journal_path expdir thy) cells)
      val pending_states = List.filter pending states
      fun work_size (_, NONE) = 0
        | work_size (_, SOME cells) = length cells
      (* Largest theories first, so the long poles start on a free core
         before the short ones fill it up. *)
      val queued_names =
        map (#1 o #2) (dict_sort (fn ((a, _), (b, _)) => Int.compare (b, a))
          (map (fn state => (work_size state, state)) pending_states))
      val queued = map (fn thy =>
        (thy, write_evalscript expdir thy conditions sample)) queued_names
      fun cleanup_scripts () = app (fn (_, script) =>
        OS.FileSys.remove script handle OS.SysErr _ => ()) queued
      fun run_workers () =
        ((smlParallel.parapp_queue ncore
            (fn (_, script) => smlExecScripts.exec_script script) queued;
          cleanup_scripts ())
         handle error => (cleanup_scripts (); raise error))
      val _ = with_flag (aiLib.scratch_dir, join expdir "out")
        run_workers ()
      fun note_unfinished (thy, NONE) = ()
        | note_unfinished (thy, SOME cells) =
            if journal_complete (journal_path expdir thy) cells then ()
            else journal_theory_error expdir thy
              "evaluation worker ended before completing its journal"
      val _ = app note_unfinished pending_states
    in
      ()
    end

(* -------------------------------------------------------------------------
   Fixed end-to-end smoke suite
   ------------------------------------------------------------------------- *)

val smoke_goals =
  [("pair", "FST_SWAP", "e"),
   ("pair", "SND_SWAP", "vampire"),
   ("pair", "PAIR_FST_SND_EQ", "zipperposition"),
   ("option", "NOT_SOME_NONE", "e"),
   ("option", "OPTION_MAP_id", "vampire"),
   ("option", "OPTION_MAP_EQ_NONE_both_ways", "zipperposition"),
   ("arithmetic", "ADD_COMM", "e"),
   ("arithmetic", "SUC_ONE_ADD", "vampire"),
   ("arithmetic", "MULT_COMM", "zipperposition"),
   ("pair", "CLOSED_PAIR_EQ", "e"),
   ("arithmetic", "SUC_NOT_ZERO", "vampire"),
   ("arithmetic", "SUC_ADD_SYM", "zipperposition"),
   ("arithmetic", "ADD1", "sched"),
   ("bool", "TRUTH", "mepo"),
   ("bool", "EQ_REFL", "mash"),
   ("bool", "IMP_CLAUSES", "mesh")]

fun smoke_condition timeout "sched" : condition =
      {cond_id = "smoke-sched", regime = Bushy, selector = Deps,
       engine = Sched
         {provers = ["e", "vampire", "zipperposition"], slices = 3,
          cores = 3, max_proofs = 1},
       timeout = timeout, reconstruct = true}
  | smoke_condition timeout "mepo" =
      {cond_id = "smoke-mepo", regime = Chainy, selector = Mepo 96,
       engine = Prover "e", timeout = timeout, reconstruct = true}
  | smoke_condition timeout "mash" =
      {cond_id = "smoke-mash", regime = Chainy, selector = Mash 96,
       engine = Prover "vampire", timeout = timeout, reconstruct = true}
  | smoke_condition timeout "mesh" =
      {cond_id = "smoke-mesh", regime = Chainy, selector = Mesh 128,
       engine = Prover "zipperposition", timeout = timeout,
       reconstruct = true}
  | smoke_condition timeout prover =
      {cond_id = "smoke-" ^ prover, regime = Bushy, selector = Deps,
       engine = Prover prover, timeout = timeout, reconstruct = true}

fun smoke_goal_id (thy, name, _) = goal_id thy name

(* The table is smoke-gated before it is used for the long evaluation runs.
   Each row below uses the actual scheduler exporter, the row's real prover
   command, TSTP parse-back, and Metis reconstruction from a named premise. *)
fun smoke_options expdir timeout : hhConfig.hh_options =
  let val snapshot = hhConfig.snapshot () in
    {timeout = timeout, max_proofs = 1,
     provers = ["e", "vampire", "zipperposition"], slices = 16, cores = 16,
     filter = "none", max_facts = NONE, format = "", type_enc = "",
     lam_trans = "", mono_iters = #mono_iters snapshot,
     mono_instances = NONE, minimize = #minimize snapshot,
     preplay_timeout = #preplay_timeout snapshot,
     minimize_timeout = #minimize_timeout snapshot, cache = false,
     cache_dir = "", cache_max_entries = #cache_max_entries snapshot,
     debug_dir = SOME (join expdir "out")}
  end

(* The format smoke test validates the typed slices.  Select them by
   encoding, not position: the rotation is tuning data and reorders. *)
fun phase2_smoke_slices options =
  List.filter (fn (_, slice) => #type_enc slice <> "")
    (hhSlice.mk_schedule options)

fun run_format_smoke expdir timeout options (config, slice) =
  let
    val theorem = DB.fetch "arithmetic" "ADD1"
    val goal = ([], Thm.concl theorem)
    val premises = ["arithmeticTheory.ADD1"]
    val condition : condition =
      {cond_id = "smoke-format-" ^ #prover slice, regime = Bushy,
       selector = Deps, engine = Prover (#prover slice), timeout = timeout,
       reconstruct = true}
    val root = hhSchedule.new_problem_dir
      (join (hhConfig.state_dir ()) "problems")
    val _ = hhSchedule.export_problems root options goal
      [(#filter slice, premises)] [(config, slice)]
    val result = hhProver.run config
      {timeout = timeout, format = #format slice,
       problem = hhSchedule.problem_path root slice, extra = #extra_opts slice,
       debug_dir = #debug_dir options}
    val (recon_ok, _, _, recon_detail) = reconstruct condition result goal
    val parsed_axioms =
      case #used_axioms result of
          SOME axioms => not (null axioms)
        | NONE => false
  in
    if #szs result = hhProver.SzsTheorem andalso parsed_axioms andalso
       recon_ok = SOME true then ()
    else raise Fail
      ("HolyHammer format smoke failed for " ^ #prover slice ^ "/" ^
       #format slice ^ "/" ^ #type_enc slice ^ "/" ^ #lam_trans slice ^
       ": status=" ^ szs_name (#szs result) ^ ", axioms=" ^
       (case #used_axioms result of
            NONE => "none"
          | SOME axioms => json_string_list axioms) ^ ", recon=" ^
       (case recon_ok of
            NONE => "none"
          | SOME value => Bool.toString value) ^ ", detail=" ^
       (case recon_detail of NONE => "none" | SOME text => text))
  end

fun pigeonhole_fixture name count =
  let
    val variables = List.tabulate (count, fn n =>
      mk_var ("pigeonhole_" ^ Int.toString n, Type.bool))
    fun unequal left right = mk_neg (mk_eq (left, right))
    fun pairs [] = []
      | pairs (item :: rest) = map (unequal item) rest @ pairs rest
  in
    (name, list_mk_exists (variables, list_mk_conj (pairs variables)))
  end

val soundness_fixtures =
  [pigeonhole_fixture "bool-three-pigeonhole" 3,
   pigeonhole_fixture "bool-four-pigeonhole" 4]

fun soundness_schedule options goal =
  let val schedule = hhSlice.mk_schedule options in
    hhSchedule.run
      {options = options, goal = ([], goal),
       rankings = rankings_for_schedule schedule [], progress = NONE}
  end

fun has_theorem (_, status, _, _) = status = hhProver.SzsTheorem

(* The complete Phase 2 encoding matrix.  The final three rows deliberately
   retain the parser-rejected table triples: a substitution removes a slice
   from the schedule, but must not remove its encoding from soundness checks. *)
fun soundness_slice prover format type_enc lam_trans nfacts : hhProver.slice =
  {prover = prover, format = format, type_enc = type_enc,
   lam_trans = lam_trans, nfacts = nfacts, filter = "none", extra_opts = [],
   slice_size = 1}

fun soundness_config name =
  case hhProver.lookup name of
      SOME config => config
    | NONE => raise Fail ("soundness smoke has no prover " ^ name)

val soundness_cases =
  [(soundness_config "vampire",
    soundness_slice "vampire" "tx0" "mono_native_fool" "lifting" 96),
   (soundness_config "zipperposition",
    soundness_slice "zipperposition" "th1" "mono_native_higher_fool"
      "keep_lams" 128),
   (soundness_config "e",
    soundness_slice "e" "th0" "mono_native_higher" "keep_lams" 512),
   (soundness_config "e",
    soundness_slice "e" "tx0-" "mono_native_fool" "combs_and_lifting"
      1024),
   (soundness_config "vampire",
    soundness_slice "vampire" "tf1" "poly_native" "lifting" 512),
   (soundness_config "e",
    soundness_slice "e" "tf0" "mono_native" "combs_and_lifting" 1024),
   (soundness_config "vampire",
    soundness_slice "vampire" "tx0" "mono_native_fool" "combs" 512),
   (soundness_config "zipperposition",
    soundness_slice "zipperposition" "fof" "mono_guards??" "lifting" 32)]

fun soundness_case options timeout goal (config, slice) =
  let
    (* A short query is enough to catch an unsound immediate theorem while
       keeping the deliberately parser-rejected candidates smoke-friendly. *)
    val query_timeout = Int.min (timeout, 3)
    val root = hhSchedule.new_problem_dir
      (join (hhConfig.state_dir ()) "problems")
    val _ = hhSchedule.export_problems root options ([], goal)
      [(#filter slice, [])] [(config, slice)]
    val result = hhProver.run config
      {timeout = query_timeout, format = #format slice,
       problem = hhSchedule.problem_path root slice, extra = #extra_opts slice,
       debug_dir = #debug_dir options}
  in
    #szs result <> hhProver.SzsTheorem
  end

fun with_smoke_hh_options timeout action =
  let
    val settings =
      [("timeout", Int.toString timeout),
       ("provers", "e vampire zipperposition"), ("slices", "16"),
       ("cores", "16"), ("filter", "none"), ("cache", "false"),
       ("format", ""), ("type_enc", ""), ("lam_trans", "")]
    fun saved key =
      case List.find (fn (name, _, source) => name = key andalso source = "set")
          (hhConfig.hh_params ()) of
          SOME (_, value, _) => SOME (key, value)
        | NONE => NONE
    val previous = List.mapPartial (saved o #1) settings
    fun restore () =
      (List.app (hhConfig.hh_unset o #1) settings;
       List.app hhConfig.hh_set previous)
    val _ = List.app hhConfig.hh_set settings
  in
    (action () before restore ()) handle error => (restore (); raise error)
  end

fun run_soundness_smoke expdir timeout options =
  let
    fun one (name, goal) =
      let
        val result = soundness_schedule options goal
        val matrix_ok = List.all (soundness_case options timeout goal)
          soundness_cases
        val no_theorem =
          length (#slices_run result) = 16 andalso
          not (List.exists has_theorem (#slices_run result)) andalso
          matrix_ok andalso null (#suggestions result)
        val public_result = with_smoke_hh_options timeout (fn () =>
          holyHammer.main_hh_lemmas expdir mlThmData.empty_thmdata
            ([], goal))
      in
        if no_theorem andalso public_result = NONE then ()
        else raise Fail ("HolyHammer soundness smoke failed for " ^ name)
      end
  in
    List.app one soundness_fixtures
  end

fun run_smoke {expdir, timeout} =
  if timeout < 1 then raise Fail "smoke timeout must be positive"
  else
    let
      val theories = sorted_unique (map #1 smoke_goals)
      val conditions = map (smoke_condition timeout)
        ["e", "vampire", "zipperposition", "sched", "mepo", "mash",
         "mesh"]
      val journals = map (journal_path expdir) theories
      val _ =
        if List.exists exists_file journals then
          raise Fail ("smoke output directory already has a journal: " ^
            expdir)
        else ()
      val _ = ensure_dir (join expdir "journal")
      val _ = ensure_dir (join expdir "out")
      val _ = ensure_dir (join expdir "pb")
      val _ = app load_theory theories
      val options = smoke_options expdir timeout
      val _ = app (run_format_smoke expdir timeout options)
        (phase2_smoke_slices options)
      val corpus = map loaded_corpus_entry theories
      val _ = write_run_header expdir
        (new_run_header {expname = OS.Path.file expdir, corpus = corpus,
          added_from_dat = [], conditions = conditions, sample = 1})
      fun run_one (thy, name, prover) =
        let
          val thm = DB.fetch thy name
          val (dependencies_ok, dependencies) =
            mlThmData.intactdep_of_thm thm
          val condition = smoke_condition timeout prover
        in
          if dependencies_ok then
            run_cell expdir thy (name, thm) dependencies condition
          else broken_deps_cell expdir thy name
            (list_mk_imp (dest_thm thm)) condition
        end
      val _ = app run_one smoke_goals
      val (sched_thy, sched_name, _) =
        case List.find (fn (_, _, engine) => engine = "sched") smoke_goals of
            SOME item => item
          | NONE => raise Fail "smoke suite has no schedule cell"
      val sched_thm = DB.fetch sched_thy sched_name
      val (_, sched_dependencies) = mlThmData.intactdep_of_thm sched_thm
      val sched_condition = smoke_condition timeout "sched"
      val sched_parameters =
        case #engine sched_condition of
            Sched parameters => parameters
          | Prover _ => raise Fail "smoke schedule condition is a prover cell"
      (* The first successful schedule cancels its remaining slices, whose
         results must not enter the cache.  Prime the entire schedule with
         an unreachable proof limit before testing a process-free replay. *)
      val primed = schedule_cell_entry expdir sched_thy
        (sched_name, sched_thm) sched_dependencies sched_condition
        {provers = #provers sched_parameters,
         slices = #slices sched_parameters, cores = #cores sched_parameters,
         max_proofs = #slices sched_parameters + 1}
      val _ =
        if #stop primed = SOME "Exhausted" andalso
           length (#slices primed) = #slices sched_parameters then ()
        else raise Fail "HolyHammer schedule cache priming did not finish"
      val _ = hhProver.reset_spawn_count ()
      val repeated = schedule_cell_entry expdir sched_thy
        (sched_name, sched_thm) sched_dependencies sched_condition
        sched_parameters
      val repeat_spawns = hhProver.spawn_count ()
      val _ =
        if not (null (#slices repeated)) andalso
           List.all #cached (#slices repeated) andalso repeat_spawns = 0 andalso
           #szs repeated = "Theorem" andalso
           #recon_ok repeated = SOME true andalso
           #stop repeated = SOME "MaxProofs"
        then ()
        else raise Fail
          ("HolyHammer schedule cache repeat failed: " ^
           Int.toString repeat_spawns ^ " spawned processes and " ^
           Int.toString (length (List.filter (not o #cached)
             (#slices repeated))) ^ " uncached slices")
      val entries = List.concat (map read_journal journals)
      fun expected entry = List.exists (fn item =>
        smoke_goal_id item = #goal_id entry) smoke_goals
      val results = List.filter expected entries
      fun succeeded entry =
        #szs entry = "Theorem" andalso #recon_ok entry = SOME true andalso
        #error entry = NONE andalso
        (case #engine entry of
             Prover _ => true
           | Sched _ => #stop entry = SOME "MaxProofs" andalso
               not (null (#slices entry)))
      val failed = List.filter (not o succeeded) results
      val _ =
        if length results = length smoke_goals andalso null failed then ()
        else raise Fail
          ("HolyHammer smoke failed: " ^ Int.toString (length failed) ^
           " failed and " ^
           Int.toString (length smoke_goals - length results) ^
           " missing; output: " ^ expdir)
      val _ = run_soundness_smoke expdir timeout options
    in
      results
    end

end
