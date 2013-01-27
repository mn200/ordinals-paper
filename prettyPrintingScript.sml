(* ------------------------------------------------------------------------- *)
(* Pretty-Printing - for HTEX processing.                                    *)
(* ------------------------------------------------------------------------- *)

open HolKernel boolLib Parse bossLib

(* open dependent theories *)
open ordinalTheory
open ordNotationSemanticsTheory

val _ = new_theory "prettyPrinting"
val _ = ParseExtras.tight_equality()

(* theorems recast for inclusion in paper *)
val divmod_unique = let
  val ordDIV_UNIQUE0 = ordDIV_UNIQUE |> SPEC_ALL |> UNDISCH_ALL |> SYM
  val ordMOD_UNIQUE0 = ordMOD_UNIQUE |> SPEC_ALL |> UNDISCH_ALL |> SYM
in
  save_thm("divmod_unique", CONJ ordDIV_UNIQUE0 ordMOD_UNIQUE0 |> DISCH_ALL)
end

val _ = overload_on("(NIL)", ``list$NIL``)

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Closefix,
                  term_name = "LENGTH",
                  pp_elements = [TOK "BarLeft|", TM, TOK "|BarRight"]}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Closefix,
                  term_name = "CARD",
                  pp_elements = [TOK "BarLeft|", TM, TOK "|BarRight"]}

val _ = remove_termtok { tok = "=", term_name = "="}
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Infix(NONASSOC, 450),
                  term_name = "=",
                  pp_elements = [HardSpace 1, TOK "=", BreakSpace(1,6)]}

val _ = remove_termtok { tok = "==>", term_name = "⇒"}
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Infixr 200,
                  term_name = "==>",
                  pp_elements = [HardSpace 1, TOK "⇒", BreakSpace(1,6)]}

val _ = remove_termtok { tok = "⇔", term_name = "<=>"}
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Infix(NONASSOC, 100),
                  term_name = "<=>",
                  pp_elements = [HardSpace 1, TOK "⇔", BreakSpace(1,6)]}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Suffix 750,
                  term_name = "**",
                  pp_elements = [TOK "(BSUP)", TM, TOK "(ESUP)"]}

val _ = set_fixity "orderiso" (Infix(NONASSOC, 450))
val _ = set_fixity "orderlt" (Infix(NONASSOC, 450))
val _ = overload_on("fld", ``elsOf : 'a wellorder -> 'a set``)
val _ = clear_overloads_on "WIN"

val _ = overload_on("strictWO", ``λw. strict (destWO w)``)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Suffix 2100,
                  term_name = "strictWO",
                  pp_elements = [TOK "(STRICT)"]}

val _ = overload_on ("'", ``IMAGE``)
val _ = set_fixity "'" (Infixl 2000);

val _ = disable_tyabbrev_printing "cord"

val _ = export_theory()

(*===========================================================================*)
