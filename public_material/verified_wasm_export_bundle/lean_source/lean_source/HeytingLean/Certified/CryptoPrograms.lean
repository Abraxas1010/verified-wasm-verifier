import HeytingLean.Certified.Program
import HeytingLean.Crypto.Hash.SHA256Primitives

namespace HeytingLean
namespace Certified

namespace Crypto

open HeytingLean.Crypto.Hash.SHA256Primitives

private def v0_1_0 : SemVer := { major := 0, minor := 1, patch := 0 }

private def propsSigma0 : List Property := [.custom "SHA256.Sigma0"]
private def propsSigma1 : List Property := [.custom "SHA256.Sigma1"]
private def propssigma0 : List Property := [.custom "SHA256.sigma0"]
private def propssigma1 : List Property := [.custom "SHA256.sigma1"]
private def propsCh : List Property := [.custom "SHA256.ch"]
private def propsMaj : List Property := [.custom "SHA256.maj"]
private def propsScheduleStep : List Property := [.custom "SHA256.scheduleStep"]
private def propsT1 : List Property := [.custom "SHA256.T1"]
private def propsT2 : List Property := [.custom "SHA256.T2"]

private def u32x3 : Ty := .prod .u32 (.prod .u32 .u32)
private def u32x4 : Ty := .prod .u32 (.prod .u32 (.prod .u32 .u32))
private def u32x6 : Ty := .prod .u32 (.prod .u32 (.prod .u32 (.prod .u32 (.prod .u32 .u32))))

def progSha256_Sigma0 : CertifiedProgram :=
  CertifiedProgram.mkHashed
    (id := "sha256_Sigma0")
    (name := "sha256_Sigma0")
    (version := v0_1_0)
    (dom := .u32) (cod := .u32)
    (dimension := .D3_Classical)
    (lenses := [.core, .c])
    (properties := propsSigma0) (invariants := [])
    (fn := Sigma0_u32)
    (propProofs := by
      intro p hp
      have hp' : p = .custom "SHA256.Sigma0" := by
        simpa [propsSigma0] using (List.mem_singleton.mp hp)
      subst hp'
      trivial)
    (cCode :=
      "/* sha256_Sigma0: UInt32 -> UInt32 */\n" ++
      "#include <stdint.h>\n" ++
      "uint32_t sha256_Sigma0(uint32_t x) {\n" ++
      "  return ((x >> 2) | (x << 30)) ^ ((x >> 13) | (x << 19)) ^ ((x >> 22) | (x << 10));\n" ++
      "}\n")

def progSha256_Sigma1 : CertifiedProgram :=
  CertifiedProgram.mkHashed
    (id := "sha256_Sigma1")
    (name := "sha256_Sigma1")
    (version := v0_1_0)
    (dom := .u32) (cod := .u32)
    (dimension := .D3_Classical)
    (lenses := [.core, .c])
    (properties := propsSigma1) (invariants := [])
    (fn := Sigma1_u32)
    (propProofs := by
      intro p hp
      have hp' : p = .custom "SHA256.Sigma1" := by
        simpa [propsSigma1] using (List.mem_singleton.mp hp)
      subst hp'
      trivial)
    (cCode :=
      "/* sha256_Sigma1: UInt32 -> UInt32 */\n" ++
      "#include <stdint.h>\n" ++
      "uint32_t sha256_Sigma1(uint32_t x) {\n" ++
      "  return ((x >> 6) | (x << 26)) ^ ((x >> 11) | (x << 21)) ^ ((x >> 25) | (x << 7));\n" ++
      "}\n")

def progSha256_sigma0 : CertifiedProgram :=
  CertifiedProgram.mkHashed
    (id := "sha256_sigma0")
    (name := "sha256_sigma0")
    (version := v0_1_0)
    (dom := .u32) (cod := .u32)
    (dimension := .D3_Classical)
    (lenses := [.core, .c])
    (properties := propssigma0) (invariants := [])
    (fn := sigma0_u32)
    (propProofs := by
      intro p hp
      have hp' : p = .custom "SHA256.sigma0" := by
        simpa [propssigma0] using (List.mem_singleton.mp hp)
      subst hp'
      trivial)
    (cCode :=
      "/* sha256_sigma0: UInt32 -> UInt32 */\n" ++
      "#include <stdint.h>\n" ++
      "uint32_t sha256_sigma0(uint32_t x) {\n" ++
      "  return ((x >> 7) | (x << 25)) ^ ((x >> 18) | (x << 14)) ^ (x >> 3);\n" ++
      "}\n")

def progSha256_sigma1 : CertifiedProgram :=
  CertifiedProgram.mkHashed
    (id := "sha256_sigma1")
    (name := "sha256_sigma1")
    (version := v0_1_0)
    (dom := .u32) (cod := .u32)
    (dimension := .D3_Classical)
    (lenses := [.core, .c])
    (properties := propssigma1) (invariants := [])
    (fn := sigma1_u32)
    (propProofs := by
      intro p hp
      have hp' : p = .custom "SHA256.sigma1" := by
        simpa [propssigma1] using (List.mem_singleton.mp hp)
      subst hp'
      trivial)
    (cCode :=
      "/* sha256_sigma1: UInt32 -> UInt32 */\n" ++
      "#include <stdint.h>\n" ++
      "uint32_t sha256_sigma1(uint32_t x) {\n" ++
      "  return ((x >> 17) | (x << 15)) ^ ((x >> 19) | (x << 13)) ^ (x >> 10);\n" ++
      "}\n")

def progSha256_ch : CertifiedProgram :=
  CertifiedProgram.mkHashed
    (id := "sha256_ch")
    (name := "sha256_ch")
    (version := v0_1_0)
    (dom := u32x3) (cod := .u32)
    (dimension := .D3_Classical)
    (lenses := [.core, .c])
    (properties := propsCh) (invariants := [])
    (fn := fun | (x, (y, z)) => ch_u32 x y z)
    (propProofs := by
      intro p hp
      have hp' : p = .custom "SHA256.ch" := by
        simpa [propsCh] using (List.mem_singleton.mp hp)
      subst hp'
      trivial)
    (cCode :=
      "/* sha256_ch: (UInt32×UInt32×UInt32) -> UInt32 */\n" ++
      "#include <stdint.h>\n" ++
      "uint32_t sha256_ch(uint32_t x, uint32_t y, uint32_t z) {\n" ++
      "  return (x & y) ^ ((~x) & z);\n" ++
      "}\n")

def progSha256_maj : CertifiedProgram :=
  CertifiedProgram.mkHashed
    (id := "sha256_maj")
    (name := "sha256_maj")
    (version := v0_1_0)
    (dom := u32x3) (cod := .u32)
    (dimension := .D3_Classical)
    (lenses := [.core, .c])
    (properties := propsMaj) (invariants := [])
    (fn := fun | (x, (y, z)) => maj_u32 x y z)
    (propProofs := by
      intro p hp
      have hp' : p = .custom "SHA256.maj" := by
        simpa [propsMaj] using (List.mem_singleton.mp hp)
      subst hp'
      trivial)
    (cCode :=
      "/* sha256_maj: (UInt32×UInt32×UInt32) -> UInt32 */\n" ++
      "#include <stdint.h>\n" ++
      "uint32_t sha256_maj(uint32_t x, uint32_t y, uint32_t z) {\n" ++
      "  return (x & y) ^ (x & z) ^ (y & z);\n" ++
      "}\n")

def progSha256_scheduleStep : CertifiedProgram :=
  CertifiedProgram.mkHashed
    (id := "sha256_schedule_step")
    (name := "sha256_schedule_step")
    (version := v0_1_0)
    (dom := u32x4) (cod := .u32)
    (dimension := .D3_Classical)
    (lenses := [.core, .c])
    (properties := propsScheduleStep) (invariants := [])
    (fn := fun | (w2, (w7, (w15, w16))) => sigma1_u32 w2 + w7 + sigma0_u32 w15 + w16)
    (propProofs := by
      intro p hp
      have hp' : p = .custom "SHA256.scheduleStep" := by
        simpa [propsScheduleStep] using (List.mem_singleton.mp hp)
      subst hp'
      trivial)
    (cCode :=
      "/* sha256_schedule_step: (UInt32×UInt32×UInt32×UInt32) -> UInt32 */\n" ++
      "#include <stdint.h>\n" ++
      "uint32_t sha256_schedule_step(uint32_t w2, uint32_t w7, uint32_t w15, uint32_t w16) {\n" ++
      "  uint32_t s1 = ((w2 >> 17) | (w2 << 15)) ^ ((w2 >> 19) | (w2 << 13)) ^ (w2 >> 10);\n" ++
      "  uint32_t s0 = ((w15 >> 7) | (w15 << 25)) ^ ((w15 >> 18) | (w15 << 14)) ^ (w15 >> 3);\n" ++
      "  return s1 + w7 + s0 + w16;\n" ++
      "}\n")

def progSha256_T1 : CertifiedProgram :=
  CertifiedProgram.mkHashed
    (id := "sha256_T1")
    (name := "sha256_T1")
    (version := v0_1_0)
    (dom := u32x6) (cod := .u32)
    (dimension := .D3_Classical)
    (lenses := [.core, .c])
    (properties := propsT1) (invariants := [])
    (fn := fun | (h, (e, (f, (g, (k, w))))) => h + Sigma1_u32 e + ch_u32 e f g + k + w)
    (propProofs := by
      intro p hp
      have hp' : p = .custom "SHA256.T1" := by
        simpa [propsT1] using (List.mem_singleton.mp hp)
      subst hp'
      trivial)
    (cCode :=
      "/* sha256_T1: (UInt32×UInt32×UInt32×UInt32×UInt32×UInt32) -> UInt32 */\n" ++
      "#include <stdint.h>\n" ++
      "uint32_t sha256_T1(uint32_t h, uint32_t e, uint32_t f, uint32_t g, uint32_t k, uint32_t w) {\n" ++
      "  uint32_t S1 = ((e >> 6) | (e << 26)) ^ ((e >> 11) | (e << 21)) ^ ((e >> 25) | (e << 7));\n" ++
      "  uint32_t ch = (e & f) ^ ((~e) & g);\n" ++
      "  return h + S1 + ch + k + w;\n" ++
      "}\n")

def progSha256_T2 : CertifiedProgram :=
  CertifiedProgram.mkHashed
    (id := "sha256_T2")
    (name := "sha256_T2")
    (version := v0_1_0)
    (dom := u32x3) (cod := .u32)
    (dimension := .D3_Classical)
    (lenses := [.core, .c])
    (properties := propsT2) (invariants := [])
    (fn := fun | (a, (b, c)) => Sigma0_u32 a + maj_u32 a b c)
    (propProofs := by
      intro p hp
      have hp' : p = .custom "SHA256.T2" := by
        simpa [propsT2] using (List.mem_singleton.mp hp)
      subst hp'
      trivial)
    (cCode :=
      "/* sha256_T2: (UInt32×UInt32×UInt32) -> UInt32 */\n" ++
      "#include <stdint.h>\n" ++
      "uint32_t sha256_T2(uint32_t a, uint32_t b, uint32_t c) {\n" ++
      "  uint32_t S0 = ((a >> 2) | (a << 30)) ^ ((a >> 13) | (a << 19)) ^ ((a >> 22) | (a << 10));\n" ++
      "  uint32_t maj = (a & b) ^ (a & c) ^ (b & c);\n" ++
      "  return S0 + maj;\n" ++
      "}\n")

def libraryPrograms : List CertifiedProgram :=
  [ progSha256_Sigma0
  , progSha256_Sigma1
  , progSha256_sigma0
  , progSha256_sigma1
  , progSha256_ch
  , progSha256_maj
  , progSha256_scheduleStep
  , progSha256_T1
  , progSha256_T2
  ]

end Crypto

end Certified
end HeytingLean
