import HeytingLean.LeanCP.Annotations.Elaborate

/-!
# LeanCP Annotation Smoke

Build-time smoke tests for the Phase 7 structured annotation layer.
-/

namespace HeytingLean.LeanCP

def annotationSmokeAssertion : Assertion :=
  assertion%[
    PROP[True, (1 : Nat) = 1]
    LOCAL[temp x := CExpr.intLit 7, temp p := CExpr.null]
    SEP[SProp.emp, HProp.emp]
  ]

def annotationSmokePatch : PartialAssertion :=
  partial_assertion%[
    MODIFIES[x]
    PROP[(2 : Nat) = 2]
    LOCAL[temp x := CExpr.intLit 9]
    SEP[HProp.emp]
  ]

def annotationSmokeApplied : Assertion :=
  annotationSmokePatch.applyTo annotationSmokeAssertion

def annotationSmokeFunc : FuncAnnotation :=
  func_annotation%[
    name := "id";
    params := [param x : CType.int];
    ret := CType.int;
    requires := assertion%[
      PROP[True]
      LOCAL[temp x := CExpr.intLit 5]
      SEP[]
    ];
    ensures rv => assertion%[
      PROP[rv = CVal.int 5]
      LOCAL[]
      SEP[]
    ];
    body := CStmt.ret (CExpr.var "x");
    modifies := [x]
  ]

def annotationSmokeLoop : LoopAnnotation :=
  loop_annotation%[
    path := [0, 1];
    fuel := 8;
    invariant := assertion%[
      PROP[True]
      LOCAL[temp n := CExpr.intLit 0]
      SEP[]
    ];
    variant := CExpr.var "n"
  ]

def annotationSmokeInput : VerifyInput :=
  annotationSmokeFunc.toVerifyInput .swp [annotationSmokeLoop.toLoopHint]

example : annotationSmokeAssertion.pure.length = 2 := rfl

example : annotationSmokeAssertion.locals.map (·.name) = ["x", "p"] := rfl

example : annotationSmokeApplied.locals.map (·.name) = ["p", "x"] := rfl

example : annotationSmokeFunc.toSFunSpec.name = "id" := rfl

example : annotationSmokeLoop.toLoopHint.path = [0, 1] := rfl

example : annotationSmokeInput.name = "id" := rfl

end HeytingLean.LeanCP
