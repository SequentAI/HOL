Theory lazyAncE[bare]
Ancestors
  lazyAncC lazyAncO
Libs
  HolKernel lazyAncestryLib

(* lazyAncC records no deltas and has two parents, so loading it may leave
   its value to be made on first read.  Save the context, change the live
   one, read lazyAncC's value for the first time through the saved context,
   then restore it and read again: the value is the merge of its parents',
   each delta applied once, in order, and the restored global value is the
   saved one *)
val _ = !applied = 0 orelse raise Fail "lazyAnc: values not lazy"
fun db thy = #DB anc {thyname = thy}
val saved = Context.snapshot ()
val _ = record "e"
val _ = check "live global" ["a1", "a2", "b1", "b2", "e", "o"]
              (SOME (#get_global_value anc ()))
val _ = check "saved lazyAncC" ["a1", "a2", "b1", "b2"]
              (#DB_of anc saved {thyname = "lazyAncC"})
val _ = !applied = 4 orelse raise Fail "lazyAnc: lazyAncC applied wrongly"
val _ = OS.Process.getEnv "HOL_SPARSE_ANC" = SOME "0" orelse
        !AncestryData.sparse_made > 0 orelse
        raise Fail "lazyAnc: lazyAncC's value was stored at load"
val _ = rev (!trace) = ["a1", "a2", "b1", "b2"] orelse
        raise Fail "lazyAnc: deltas applied out of order"
val _ = Context.restore saved
val _ = check "restored lazyAncC" ["a1", "a2", "b1", "b2"] (db "lazyAncC")
val _ = !applied = 4 orelse raise Fail "lazyAnc: lazyAncC computed twice"
val _ = check "restored global" ["a1", "a2", "b1", "b2", "o"]
              (SOME (#get_global_value anc ()))
