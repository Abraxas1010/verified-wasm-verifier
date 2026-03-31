import HeytingLean.CLI.PQCNTTCheck

/-!
# `pqc_ntt_check` executable entrypoint
-/

def main (argv : List String) : IO Unit :=
  HeytingLean.CLI.PQCNTTCheck.main argv
