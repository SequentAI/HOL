(* =====================================================================
 * DESCRIPTION  : Implementation of term nets, from GTT.
 * MODIFIED     : Donald Syme, 1995, to add local constants
 *
 * MODIFIED    : Donald Syme, November 1995, to be keyed up to
 *               higher order matching, based on JRH's code from GTT.
 * ===================================================================== *)

signature Ho_Net =
sig
 type 'a net
 type term = Term.term

 val empty      : 'a net
 val enter      : term list * term * 'a -> 'a net -> 'a net
 val lookup     : term -> 'a net -> 'a list
 val merge_nets : 'a net * 'a net -> 'a net
 val fold'      : ('a -> 'b -> 'b) -> 'a net -> 'b -> 'b
 val vfilter    : ('a -> bool) -> 'a net -> 'a net

 type key
 val key_compare : key * key -> order
 val entry_key  : term list * term -> key option
 val lookup_keys : term -> key list

end
