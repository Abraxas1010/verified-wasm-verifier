import HeytingLean.CLI.PQCFailureBound

/-!
# `pqc_failure_bound` executable entrypoint
-/

def main (argv : List String) : IO Unit :=
  HeytingLean.CLI.PQCFailureBound.main argv

