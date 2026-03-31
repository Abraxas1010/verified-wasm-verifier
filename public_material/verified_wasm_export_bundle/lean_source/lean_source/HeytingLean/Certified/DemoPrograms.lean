import HeytingLean.Certified.Program

namespace HeytingLean
namespace Certified
namespace Demo

open Certified

def filterGT (t : Nat) : List Nat → List Nat :=
  fun xs => xs.filter (fun n => t < n)

def sumList : List Nat → Nat :=
  fun xs => xs.foldl (fun acc n => acc + n) 0

def clampNat (lo hi : Nat) : Nat → Nat :=
  fun n => Nat.min hi (Nat.max lo n)

private def v0_1_0 : SemVer := { major := 0, minor := 1, patch := 0 }

def progFilterGT100 : CertifiedProgram :=
  let fn : Ty.interp .listNat → Ty.interp .listNat := filterGT 100
  CertifiedProgram.mkHashed
    (id := "filter_gt_100")
    (name := "filter_gt_100")
    (version := v0_1_0)
    (dom := .listNat) (cod := .listNat)
    (dimension := .D1_Heyting)
    (lenses := [.core, .c])
    (properties := []) (invariants := [])
    (fn := fn)
    (propProofs := by
      intro p hp
      cases hp)
    (cCode :=
      "/* filter_gt_100: ListNat -> ListNat\n" ++
      "   C ABI: size_t filter_gt_100(const uint32_t* xs, size_t n, uint32_t* out, size_t out_cap)\n" ++
      "   Returns the number of elements > 100 (may exceed out_cap).\n" ++
      "*/\n" ++
      "#include <stdint.h>\n" ++
      "#include <stddef.h>\n" ++
      "size_t filter_gt_100(const uint32_t* xs, size_t n, uint32_t* out, size_t out_cap) {\n" ++
      "  size_t j = 0;\n" ++
      "  for (size_t i = 0; i < n; i++) {\n" ++
      "    uint32_t x = xs[i];\n" ++
      "    if (x > 100u) {\n" ++
      "      if (j < out_cap) out[j] = x;\n" ++
      "      j++;\n" ++
      "    }\n" ++
      "  }\n" ++
      "  return j;\n" ++
      "}\n")

def progSumList : CertifiedProgram :=
  let fn : Ty.interp .listNat → Ty.interp .nat := sumList
  CertifiedProgram.mkHashed
    (id := "sum_list")
    (name := "sum_list")
    (version := v0_1_0)
    (dom := .listNat) (cod := .nat)
    (dimension := .D1_Heyting)
    (lenses := [.core, .c])
    (properties := []) (invariants := [])
    (fn := fn)
    (propProofs := by
      intro p hp
      cases hp)
    (cCode :=
      "/* sum_list: ListNat -> Nat\n" ++
      "   C ABI: uint32_t sum_list(const uint32_t* xs, size_t n)\n" ++
      "   Note: this demo uses a 32-bit return value.\n" ++
      "*/\n" ++
      "#include <stdint.h>\n" ++
      "#include <stddef.h>\n" ++
      "uint32_t sum_list(const uint32_t* xs, size_t n) {\n" ++
      "  uint64_t acc = 0;\n" ++
      "  for (size_t i = 0; i < n; i++) {\n" ++
      "    acc += (uint64_t)xs[i];\n" ++
      "  }\n" ++
      "  return (uint32_t)acc;\n" ++
      "}\n")

private theorem clamp_0_10000_bounded :
    Property.Holds (.boundedNat 0 10000) .nat .nat (clampNat 0 10000) := by
  intro n
  constructor
  · exact Nat.zero_le _
  · exact Nat.min_le_left _ _

def progClamp0_10000 : CertifiedProgram :=
  let fn : Ty.interp .nat → Ty.interp .nat := clampNat 0 10000
  let props : List Property := [.boundedNat 0 10000]
  CertifiedProgram.mkHashed
    (id := "clamp_0_10000")
    (name := "clamp_0_10000")
    (version := v0_1_0)
    (dom := .nat) (cod := .nat)
    (dimension := .D1_Heyting)
    (lenses := [.core, .c])
    (properties := props) (invariants := props)
    (fn := fn)
    (propProofs := by
      intro p hp
      have hp' : p = .boundedNat 0 10000 := by
        simpa [props] using (List.mem_singleton.mp hp)
      subst hp'
      simpa using clamp_0_10000_bounded)
    (cCode :=
      "/* clamp_0_10000: Nat -> Nat */\n" ++
      "#include <stdint.h>\n" ++
      "uint32_t clamp_0_10000(uint32_t x) {\n" ++
      "  if (x > 10000u) return 10000u;\n" ++
      "  return x;\n" ++
      "}\n")

private theorem clamp_100_10000_bounded :
    Property.Holds (.boundedNat 100 10000) .nat .nat (clampNat 100 10000) := by
  intro n
  constructor
  ·
    have h₁ : 100 ≤ Nat.max 100 n := le_max_left _ _
    have h₂ : 100 ≤ 10000 := by decide
    exact le_min h₂ h₁
  · exact Nat.min_le_left _ _

def progClamp100_10000 : CertifiedProgram :=
  let fn : Ty.interp .nat → Ty.interp .nat := clampNat 100 10000
  let props : List Property := [.boundedNat 100 10000]
  CertifiedProgram.mkHashed
    (id := "clamp_100_10000")
    (name := "clamp_100_10000")
    (version := v0_1_0)
    (dom := .nat) (cod := .nat)
    (dimension := .D1_Heyting)
    (lenses := [.core, .c])
    (properties := props) (invariants := props)
    (fn := fn)
    (propProofs := by
      intro p hp
      have hp' : p = .boundedNat 100 10000 := by
        simpa [props] using (List.mem_singleton.mp hp)
      subst hp'
      simpa using clamp_100_10000_bounded)
    (cCode :=
      "/* clamp_100_10000: Nat -> Nat */\n" ++
      "#include <stdint.h>\n" ++
      "uint32_t clamp_100_10000(uint32_t x) {\n" ++
      "  if (x < 100u) return 100u;\n" ++
      "  if (x > 10000u) return 10000u;\n" ++
      "  return x;\n" ++
      "}\n")

private theorem clamp_0_99_bounded :
    Property.Holds (.boundedNat 0 99) .nat .nat (clampNat 0 99) := by
  intro n
  constructor
  · exact Nat.zero_le _
  · exact Nat.min_le_left _ _

def progClamp0_99 : CertifiedProgram :=
  let fn : Ty.interp .nat → Ty.interp .nat := clampNat 0 99
  let props : List Property := [.boundedNat 0 99]
  CertifiedProgram.mkHashed
    (id := "clamp_0_99")
    (name := "clamp_0_99")
    (version := v0_1_0)
    (dom := .nat) (cod := .nat)
    (dimension := .D1_Heyting)
    (lenses := [.core, .c])
    (properties := props) (invariants := props)
    (fn := fn)
    (propProofs := by
      intro p hp
      have hp' : p = .boundedNat 0 99 := by
        simpa [props] using (List.mem_singleton.mp hp)
      subst hp'
      simpa using clamp_0_99_bounded)
    (cCode :=
      "/* clamp_0_99: Nat -> Nat */\n" ++
      "#include <stdint.h>\n" ++
      "uint32_t clamp_0_99(uint32_t x) {\n" ++
      "  if (x > 99u) return 99u;\n" ++
      "  return x;\n" ++
      "}\n")

private theorem clamp_101_10000_bounded :
    Property.Holds (.boundedNat 101 10000) .nat .nat (clampNat 101 10000) := by
  intro n
  constructor
  ·
    have h₁ : 101 ≤ Nat.max 101 n := le_max_left _ _
    have h₂ : 101 ≤ 10000 := by decide
    exact le_min h₂ h₁
  · exact Nat.min_le_left _ _

def progClamp101_10000 : CertifiedProgram :=
  let fn : Ty.interp .nat → Ty.interp .nat := clampNat 101 10000
  let props : List Property := [.boundedNat 101 10000]
  CertifiedProgram.mkHashed
    (id := "clamp_101_10000")
    (name := "clamp_101_10000")
    (version := v0_1_0)
    (dom := .nat) (cod := .nat)
    (dimension := .D1_Heyting)
    (lenses := [.core, .c])
    (properties := props) (invariants := props)
    (fn := fn)
    (propProofs := by
      intro p hp
      have hp' : p = .boundedNat 101 10000 := by
        simpa [props] using (List.mem_singleton.mp hp)
      subst hp'
      simpa using clamp_101_10000_bounded)
    (cCode :=
      "/* clamp_101_10000: Nat -> Nat */\n" ++
      "#include <stdint.h>\n" ++
      "uint32_t clamp_101_10000(uint32_t x) {\n" ++
      "  if (x < 101u) return 101u;\n" ++
      "  if (x > 10000u) return 10000u;\n" ++
      "  return x;\n" ++
      "}\n")

def libraryPrograms : List CertifiedProgram :=
  [progFilterGT100, progSumList, progClamp0_10000, progClamp100_10000, progClamp0_99, progClamp101_10000]

end Demo
end Certified
end HeytingLean
