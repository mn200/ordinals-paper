(* ------------------------------------------------------------------------- *)
(* Pretty-Printing - for HTEX processing.                                    *)
(* ------------------------------------------------------------------------- *)

open HolKernel boolLib Parse bossLib

(* open dependent theories *)
open ordinalTheory

val foo = ``(foo:num -> num) bar``

val _ = new_theory "prettyPrinting"

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
                  pp_elements = [HardSpace 1, TOK "=", BreakSpace(1,2)]}

val _ = remove_termtok { tok = "==>", term_name = "⇒"}
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Infixr 200,
                  term_name = "==>",
                  pp_elements = [HardSpace 1, TOK "⇒", BreakSpace(1,2)]}

val _ = remove_termtok { tok = "⇔", term_name = "<=>"}
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Infix(NONASSOC, 100),
                  term_name = "<=>",
                  pp_elements = [HardSpace 1, TOK "⇔", BreakSpace(1,2)]}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  fixity = Suffix 750,
                  term_name = "**",
                  pp_elements = [TOK "(BSUP)", TM, TOK "(ESUP)"]}

val _ = set_fixity "orderiso" (Infix(NONASSOC, 450))
val _ = set_fixity "orderlt" (Infix(NONASSOC, 450))
val _ = overload_on("fld", ``elsOf : 'a wellorder -> 'a set``)
val _ = overload_on("IN", ``λp w. p IN strict (destWO w)``)

val _ = export_theory()

(*===========================================================================*)