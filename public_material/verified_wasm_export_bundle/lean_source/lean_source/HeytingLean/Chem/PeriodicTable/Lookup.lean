import HeytingLean.Chem.PeriodicTable.CIAAW2024

namespace HeytingLean.Chem.PeriodicTable

-- All elements (as Fin 118) in ascending atomic-number order.
def all : List Element :=
  List.ofFn (fun i : Fin 118 => i)

def ofSymbol? (s : String) : Option Element :=
  all.find? (fun e => symbol e = s)

def ofName? (s : String) : Option Element :=
  all.find? (fun e => name e = s)

end HeytingLean.Chem.PeriodicTable

