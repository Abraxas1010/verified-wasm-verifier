import HeytingLean.LeanCP.Lang.CDecl
import HeytingLean.LoF.Combinators.SKYReducerKernel

/-!
# SKYLowering

Lower the export-facing `SKYReducerKernel` step into raw LeanCP-owned C syntax.

This is intentionally a first-order buffer-mutating kernel surface. It avoids
`MiniC` entirely for SKY-class reducer execution and targets the wider LeanCP C
owner directly.
-/

namespace HeytingLean
namespace LeanCP
namespace Compile
namespace SKYLowering

open HeytingLean.LoF.Combinators.SKYReducerKernel

def loadAt (base : String) (idx : CExpr) : CExpr :=
  .arrayAccess (.var base) idx

def storeAt (base : String) (idx value : CExpr) : CStmt :=
  .assign (.deref (.binop .add (.var base) idx)) value

def writeScalar (ptrName : String) (value : CExpr) : CStmt :=
  .assign (.deref (.var ptrName)) value

def seqs : List CStmt → CStmt
  | [] => .skip
  | [stmt] => stmt
  | stmt :: rest => .seq stmt (seqs rest)

def commitAndReturn (code : StepStatus) : CStmt :=
  .seq
    (writeScalar "focusPtr" (.var "focus"))
    (.seq
      (writeScalar "stackSizePtr" (.var "stackSize"))
      (.seq
        (writeScalar "nodeCountPtr" (.var "nodeCount"))
        (.ret (.intLit code.code))))

def stackIx (depthFromTop : Nat) : CExpr :=
  .binop .sub (.var "stackSize") (.intLit (Int.ofNat depthFromTop))

def nodeIx (offset : Nat) : CExpr :=
  .binop .add (.var "nodeCount") (.intLit (Int.ofNat offset))

def appTagExpr : CExpr := .intLit (NodeTag.code .app)

def appCase : CStmt :=
  seqs
    [ .assign (.var "x") (loadAt "rhs" (.var "focus"))
    , storeAt "stack" (.var "stackSize") (.var "x")
    , .assign (.var "focus") (loadAt "lhs" (.var "focus"))
    , .assign (.var "stackSize") (.binop .add (.var "stackSize") (.intLit 1))
    , commitAndReturn .progress ]

def kCase : CStmt :=
  .ite
    (.binop .ge (.var "stackSize") (.intLit 2))
    (seqs
      [ .assign (.var "x") (loadAt "stack" (stackIx 1))
      , .assign (.var "focus") (.var "x")
      , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
      , commitAndReturn .progress ])
    (commitAndReturn .halted)

def sCase : CStmt :=
  .ite
    (.binop .ge (.var "stackSize") (.intLit 3))
    (.ite
      (.binop .le (.binop .add (.var "nodeCount") (.intLit 3)) (.var "maxNodes"))
      (seqs
        [ .assign (.var "x") (loadAt "stack" (stackIx 1))
        , .assign (.var "y") (loadAt "stack" (stackIx 2))
        , .assign (.var "z") (loadAt "stack" (stackIx 3))
        , storeAt "tags" (nodeIx 0) appTagExpr
        , storeAt "lhs" (nodeIx 0) (.var "x")
        , storeAt "rhs" (nodeIx 0) (.var "z")
        , storeAt "oracleRefs" (nodeIx 0) (.intLit 0)
        , storeAt "tags" (nodeIx 1) appTagExpr
        , storeAt "lhs" (nodeIx 1) (.var "y")
        , storeAt "rhs" (nodeIx 1) (.var "z")
        , storeAt "oracleRefs" (nodeIx 1) (.intLit 0)
        , storeAt "tags" (nodeIx 2) appTagExpr
        , storeAt "lhs" (nodeIx 2) (nodeIx 0)
        , storeAt "rhs" (nodeIx 2) (nodeIx 1)
        , storeAt "oracleRefs" (nodeIx 2) (.intLit 0)
        , .assign (.var "focus") (nodeIx 2)
        , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 3))
        , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 3))
        , commitAndReturn .progress ])
      (commitAndReturn .outOfHeap))
    (commitAndReturn .halted)

def yCase : CStmt :=
  .ite
    (.binop .ge (.var "stackSize") (.intLit 1))
    (.ite
      (.binop .le (.binop .add (.var "nodeCount") (.intLit 2)) (.var "maxNodes"))
      (seqs
        [ .assign (.var "x") (loadAt "stack" (stackIx 1))
        , storeAt "tags" (nodeIx 0) appTagExpr
        , storeAt "lhs" (nodeIx 0) (.var "focus")
        , storeAt "rhs" (nodeIx 0) (.var "x")
        , storeAt "oracleRefs" (nodeIx 0) (.intLit 0)
        , storeAt "tags" (nodeIx 1) appTagExpr
        , storeAt "lhs" (nodeIx 1) (.var "x")
        , storeAt "rhs" (nodeIx 1) (nodeIx 0)
        , storeAt "oracleRefs" (nodeIx 1) (.intLit 0)
        , .assign (.var "focus") (nodeIx 1)
        , .assign (.var "nodeCount") (.binop .add (.var "nodeCount") (.intLit 2))
        , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 1))
        , commitAndReturn .progress ])
      (commitAndReturn .outOfHeap))
    (commitAndReturn .halted)

def oracleCase : CStmt :=
  .ite
    (.binop .ge (.var "stackSize") (.intLit 2))
    (seqs
      [ .assign (.var "x") (loadAt "stack" (stackIx 1))
      , .assign (.var "y") (loadAt "stack" (stackIx 2))
      , .assign (.var "ref") (loadAt "oracleRefs" (.var "focus"))
      , .ite
          (.binop .ne (loadAt "oracleValues" (.var "ref")) (.intLit 0))
          (seqs
            [ .assign (.var "focus") (.var "x")
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
            , commitAndReturn .progress ])
          (seqs
            [ .assign (.var "focus") (.var "y")
            , .assign (.var "stackSize") (.binop .sub (.var "stackSize") (.intLit 2))
            , commitAndReturn .progress ]) ])
    (commitAndReturn .halted)

def skyReducerStepBody : CStmt :=
  .block
    [ ("tag", .int)
    , ("focus", .int)
    , ("stackSize", .int)
    , ("nodeCount", .int)
    , ("x", .int)
    , ("y", .int)
    , ("z", .int)
    , ("ref", .int) ]
    (seqs
      [ .assign (.var "focus") (.deref (.var "focusPtr"))
      , .assign (.var "stackSize") (.deref (.var "stackSizePtr"))
      , .assign (.var "nodeCount") (.deref (.var "nodeCountPtr"))
      , .ite
          (.binop .lt (.var "focus") (.var "nodeCount"))
          (.seq
            (.assign (.var "tag") (loadAt "tags" (.var "focus")))
            (switchMany (.var "tag")
              [ (NodeTag.code .app, appCase)
              , (NodeTag.code .combK, kCase)
              , (NodeTag.code .combS, sCase)
              , (NodeTag.code .combY, yCase)
              , (NodeTag.code .oracle, oracleCase) ]
              (commitAndReturn .halted)))
          (commitAndReturn .halted)
      ])

def skyReducerStepDecl : CFunDecl :=
  { name := "sky_reducer_step"
    params :=
      [ ("tags", .ptr .int)
      , ("lhs", .ptr .int)
      , ("rhs", .ptr .int)
      , ("oracleRefs", .ptr .int)
      , ("oracleValues", .ptr .int)
      , ("stack", .ptr .int)
      , ("focusPtr", .ptr .int)
      , ("stackSizePtr", .ptr .int)
      , ("nodeCountPtr", .ptr .int)
      , ("maxNodes", .int) ]
    retType := .int
    body := skyReducerStepBody }

def skyReducerProgram : CProgramDecl :=
  { defs := []
    main := skyReducerStepDecl }

end SKYLowering
end Compile
end LeanCP
end HeytingLean
