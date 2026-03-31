import HeytingLean.CLI.OFIProgression

noncomputable def main (argv : List String) : IO UInt32 :=
  HeytingLean.CLI.OFIProgression.runWithArgs argv
