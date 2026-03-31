import HeytingLean.Crypto.DSA.MLDSA
import HeytingLean.Crypto.DSA.MLDSA204Params
import HeytingLean.Crypto.KEM.MLKEM
import HeytingLean.Crypto.KEM.MLKEM203Params

namespace HeytingLean
namespace Crypto
namespace VerifiedPQC

/-!
# VerifiedPQC standardized runtime boundary

This module records the executable boundary between the Lean proof/program surface and the
vendored PQClean-backed ML-KEM / ML-DSA runtimes used by the external audits.
-/

/-- Standards-aligned parameter bundle shared by the protocol and the external runtime audit. -/
structure ParameterBundle where
  kem : KEM.FIPS203.MLKEM203Params
  dsa : DSA.FIPS204.MLDSA204Params

/-- Runtime metadata for a standardized ML-KEM backend. -/
structure RuntimeKEMBackend where
  scheme : String
  buildScript : String
  keygenCli : String
  encapCli : String
  keygenEncapCli : String
  decapCli : String
  decapDumpCli : String
  implementation : String
  deriving Repr, DecidableEq

/-- Runtime metadata for a standardized ML-DSA backend. -/
structure RuntimeDSABackend where
  scheme : String
  buildScript : String
  signCli : String
  openCli : String
  implementation : String
  deriving Repr, DecidableEq

/-- Standardized runtime bundle used by the exact protocol audit. -/
structure RuntimeBundle where
  kem : RuntimeKEMBackend
  dsa : RuntimeDSABackend
  deriving Repr, DecidableEq

def runtimeKEMBackend (p : KEM.FIPS203.MLKEM203Params) : RuntimeKEMBackend :=
  match p.k with
  | 2 =>
      { scheme := "ML-KEM-512"
        buildScript := "WIP/pqc_lattice/scripts/build_kem_cli.sh kyber512"
        keygenCli := "WIP/pqc_lattice/out/kem_keygen_cli_512"
        encapCli := "WIP/pqc_lattice/out/kem_encap_cli_512"
        keygenEncapCli := "WIP/pqc_lattice/out/kem_kat_cli_512"
        decapCli := "WIP/pqc_lattice/out/kem_dec_cli_512"
        decapDumpCli := "WIP/pqc_lattice/out/kem_decap_dump_cli_512"
        implementation := "PQClean ML-KEM-512 clean" }
  | 3 =>
      { scheme := "ML-KEM-768"
        buildScript := "WIP/pqc_lattice/scripts/build_kem_cli.sh kyber768"
        keygenCli := "WIP/pqc_lattice/out/kem_keygen_cli_768"
        encapCli := "WIP/pqc_lattice/out/kem_encap_cli_768"
        keygenEncapCli := "WIP/pqc_lattice/out/kem_kat_cli_768"
        decapCli := "WIP/pqc_lattice/out/kem_dec_cli_768"
        decapDumpCli := "WIP/pqc_lattice/out/kem_decap_dump_cli_768"
        implementation := "PQClean ML-KEM-768 clean" }
  | _ =>
      { scheme := "ML-KEM-1024"
        buildScript := "WIP/pqc_lattice/scripts/build_kem_cli.sh kyber1024"
        keygenCli := "WIP/pqc_lattice/out/kem_keygen_cli_1024"
        encapCli := "WIP/pqc_lattice/out/kem_encap_cli_1024"
        keygenEncapCli := "WIP/pqc_lattice/out/kem_kat_cli_1024"
        decapCli := "WIP/pqc_lattice/out/kem_dec_cli_1024"
        decapDumpCli := "WIP/pqc_lattice/out/kem_decap_dump_cli_1024"
        implementation := "PQClean ML-KEM-1024 clean" }

def runtimeDSABackend (p : DSA.FIPS204.MLDSA204Params) : RuntimeDSABackend :=
  match p.k with
  | 4 =>
      { scheme := "ML-DSA-44"
        buildScript := "WIP/pqc_lattice/scripts/build_dsa_cli.sh dilithium2"
        signCli := "WIP/pqc_lattice/out/dsa_sign_cli_2"
        openCli := "WIP/pqc_lattice/out/dsa_open_cli_2"
        implementation := "PQClean ML-DSA-44 clean" }
  | 6 =>
      { scheme := "ML-DSA-65"
        buildScript := "WIP/pqc_lattice/scripts/build_dsa_cli.sh dilithium3"
        signCli := "WIP/pqc_lattice/out/dsa_sign_cli_3"
        openCli := "WIP/pqc_lattice/out/dsa_open_cli_3"
        implementation := "PQClean ML-DSA-65 clean" }
  | _ =>
      { scheme := "ML-DSA-87"
        buildScript := "WIP/pqc_lattice/scripts/build_dsa_cli.sh dilithium5"
        signCli := "WIP/pqc_lattice/out/dsa_sign_cli_5"
        openCli := "WIP/pqc_lattice/out/dsa_open_cli_5"
        implementation := "PQClean ML-DSA-87 clean" }

def standardRuntimeBundle (bundle : ParameterBundle) : RuntimeBundle :=
  { kem := runtimeKEMBackend bundle.kem
    dsa := runtimeDSABackend bundle.dsa }

end VerifiedPQC
end Crypto
end HeytingLean
