import HeytingLean.LeanCP.Bench.Seed

namespace HeytingLean.LeanCP.Bench

def allEntries : List BenchEntry :=
  seedEntries

def countedEntries : List BenchEntry :=
  allEntries.filter BenchEntry.isCounted

end HeytingLean.LeanCP.Bench
