import HeytingLean.Numbers.Surreal.CanonicalizeWF.Core

/-!
# Canonicalize Smoke

Std-only smoke harness importing the Core module and running `#eval` guards for
`normListCore` and `canonicalizeWF`.
-/

open HeytingLean.Numbers.Surreal

namespace HeytingLean.Numbers.Surreal.Test

open SurrealCore

def leaf (b := 0) : PreGame := { L := [], R := [], birth := b }

def node (ls rs : List PreGame) (b := 0) : PreGame := { L := ls, R := rs, birth := b }

#eval canonicalizeWF (leaf 3)
#eval canonicalizeWF (node [leaf, leaf, leaf] [leaf] 7)
#eval canonicalizeWF (node [leaf, node [leaf] [], leaf] [node [] [leaf]] 0)

-- Idempotence sanity checks
#eval Surreal.normListCoreIdem [leaf, leaf, leaf]

def t1 := node [leaf, node [leaf] [], leaf] [node [] [leaf]] 0

#eval Surreal.eqByKey (Surreal.canonicalizeWF t1)
                     (Surreal.canonicalizeWF (Surreal.canonicalizeWF t1))

def deep : PreGame := node [node [node [leaf] []] []] [] 0

#eval Surreal.eqByKey (Surreal.canonicalizeWF deep)
                     (Surreal.canonicalizeWF (Surreal.canonicalizeWF deep))

-- Property guards (expect `true`)
#eval Surreal.normListCoreOk [leaf, leaf, leaf]

def t2 := node [leaf, node [leaf] [], leaf] [node [] [leaf]] 0

#eval Surreal.normListCoreOk (t2.L ++ t2.R)

#eval Surreal.normListCorePermOk [leaf, leaf, leaf]
#eval Surreal.heightDecOK t2
#eval Surreal.heightDecOK deep

end HeytingLean.Numbers.Surreal.Test

def main : IO UInt32 := pure 0
