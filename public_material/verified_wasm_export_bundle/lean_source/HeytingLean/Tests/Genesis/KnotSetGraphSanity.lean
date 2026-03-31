import HeytingLean.Genesis

/-!
# Genesis Knot Set Graph Sanity
-/

namespace HeytingLean.Tests.Genesis

open HeytingLean.Genesis

#check MemGraph
#check MemGraph.Bisim
#check MemGraph.bisim_equiv
#check OmegaGraph
#check omega_mem_self
#check LinkGraph
#check link_mutual
#check MemGraph.toCoGame
#check omega_toCoGame_bisim_life

example : OmegaGraph.mem Omega Omega := omega_mem_self

example : LinkGraph.mem LinkA LinkB := link_mutual.1

example : LinkGraph.mem LinkB LinkA := link_mutual.2

example : CoGame.Bisim (MemGraph.toCoGame OmegaGraph Omega) CoGame.Life :=
  omega_toCoGame_bisim_life

example : Equivalence (MemGraph.Bisim OmegaGraph) := MemGraph.bisim_equiv (G := OmegaGraph)

end HeytingLean.Tests.Genesis
