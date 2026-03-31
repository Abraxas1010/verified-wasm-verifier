import HeytingLean.CLI.MLDSAParamValidator

/-!
# `mldsa_param_validator` executable entrypoint

This provides the dedicated entrypoint used by `lake exe mldsa_param_validator`.
-/

def main (argv : List String) : IO Unit :=
  HeytingLean.CLI.MLDSAValidator.main argv

