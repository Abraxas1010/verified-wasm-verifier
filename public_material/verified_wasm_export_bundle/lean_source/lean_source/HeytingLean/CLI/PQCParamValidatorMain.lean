import HeytingLean.CLI.PQCParamValidator

/-!
# `pqc_param_validator` executable entrypoint

The library module `HeytingLean.CLI.PQCParamValidator` is imported by other executables, so it
must not define a top-level `main` (which would collide). This file provides the dedicated
entrypoint used by `lake exe pqc_param_validator`.
-/

def main (argv : List String) : IO Unit :=
  HeytingLean.CLI.PQCValidator.main argv

