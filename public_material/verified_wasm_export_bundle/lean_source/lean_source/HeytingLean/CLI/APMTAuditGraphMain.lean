import HeytingLean.CLI.APMTAuditGraph

open HeytingLean.CLI

def main (args : List String) : IO UInt32 :=
  APMTAuditGraph.runWithArgs args
