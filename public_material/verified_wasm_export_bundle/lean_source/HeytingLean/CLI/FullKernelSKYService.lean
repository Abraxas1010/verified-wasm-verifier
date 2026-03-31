import HeytingLean.CLI.FullKernelSKYMain

namespace HeytingLean.CLI.FullKernelSKYService

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.FullKernelSKYMain.main ("--service" :: args)

end HeytingLean.CLI.FullKernelSKYService
