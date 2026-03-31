import Lean
import HeytingLean.LeanCP.Annotations.Language

/-!
# LeanCP Annotation Syntax

Pure syntax declarations for the Phase 7 annotation DSL.
-/

namespace HeytingLean.LeanCP

syntax (name := leancpLocalBinding) "temp " ident " := " term : term
syntax (name := leancpAnnotatedParam) "param " ident " : " term : term

syntax (name := leancpAssertion) "assertion%[" "PROP[" sepBy(term, ",") "]"
    " LOCAL[" sepBy(term, ",") "]"
    " SEP[" sepBy(term, ",") "]" "]" : term

syntax (name := leancpPartialAssertion) "partial_assertion%[" "MODIFIES[" sepBy(ident, ",") "]"
    " PROP[" sepBy(term, ",") "]"
    " LOCAL[" sepBy(term, ",") "]"
    " SEP[" sepBy(term, ",") "]" "]" : term

syntax (name := leancpFuncAnnotation) "func_annotation%[" "name" " := " str ";" 
    "params" " := " "[" sepBy(term, ",") "]" ";"
    "ret" " := " term ";"
    "requires" " := " term ";"
    "ensures" ident " => " term ";"
    "body" " := " term
    (";" "modifies" " := " "[" sepBy(ident, ",") "]")? "]" : term

syntax (name := leancpLoopAnnotation) "loop_annotation%[" "path" " := " "[" sepBy(num, ",") "]" ";"
    "fuel" " := " num ";"
    "invariant" " := " term
    (";" "variant" " := " term)? "]" : term

end HeytingLean.LeanCP
