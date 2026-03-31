import HeytingLean.LoF.NucleusLemmas

open Classical

namespace HeytingLean
namespace Tests
namespace LoF

example {α} [CompleteLattice α] (j k : Nucleus α) (x : α)
  (hxj : j x = x) (hxk : k x = x) :
  (j ⊓ k) x = x :=
  HeytingLean.LoF.mem_fix_inf_of_mem_fixes j k hxj hxk

end LoF
end Tests
end HeytingLean
