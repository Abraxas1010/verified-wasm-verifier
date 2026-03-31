import HeytingLean.Reasoning.Rules
import HeytingLean.Reasoning.Engine
import HeytingLean.Reasoning.Collapse
import HeytingLean.Logic.StageSemantics

/-
Compile-only check for collapse-aware saturation and a tiny bridge example.
-/

namespace HeytingLean
namespace Tests
namespace Reasoning

open HeytingLean.Reasoning
open HeytingLean.Logic.Stage

-- Identity collapse on String
def idCollapse (s : String) : String := s

def facts1 : Array String := #["P", "Q"]
def rPQ : Rule String := { premises := #["P", "Q"], concl := "R" }
def rR  : Rule String := { premises := #["R"], concl := "S" }
def rules1 : Array (Rule String) := #[rPQ, rR]

def closure1 : Array String := saturateCollapsed idCollapse rules1 facts1 8

-- Tiny bridge example on Nat using StageSemantics.Bridge (identity bridge)
def idBridgeNat : Bridge Nat Nat where
  shadow := id
  lift   := id
  rt₁    := by intro u; rfl
  rt₂    := by intro x; exact le_rfl

def κNat (n : Nat) : Nat := n   -- identity collapse on Ω=Nat
def collapseA : Nat → Nat := collapseViaBridge (B := idBridgeNat) κNat

def factsN : Array Nat := #[1, 2]
def rN    : Rule Nat := { premises := #[1,2], concl := 3 }
def rulesN : Array (Rule Nat) := #[rN]
def closureN : Array Nat := saturateCollapsed collapseA rulesN factsN 4

end Reasoning
end Tests
end HeytingLean

