
import Kernel.OmegaR
open OmegaR
open List

def Γ : List Formula := [(OmegaR.Formula.var "A")]
def goal : Formula := (OmegaR.Formula.orR (OmegaR.Formula.var "A") (OmegaR.Formula.var "B"))

theorem imported : Provable Γ goal :=
  (OmegaR.Provable.orRI (Γ:=[(OmegaR.Formula.var "A")]) (A:=(OmegaR.Formula.var "A")) (B:=(OmegaR.Formula.var "B")) (OmegaR.Provable.hyp (Γ:=[(OmegaR.Formula.var "A")]) (φ:=(OmegaR.Formula.var "A")) (List.Mem.head (as:=[]))))
