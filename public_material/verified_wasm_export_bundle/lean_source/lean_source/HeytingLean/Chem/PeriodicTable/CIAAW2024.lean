/-
Auto-generated periodic-table snapshot from:
  https://www.ciaaw.org/atomic-weights.htm
Fetched on: 2026-02-03

Do not edit by hand. Regenerate with:
  python3 scripts/chem_fetch_ciaaw_atomic_weights_2024.py --write-lean
-/

namespace HeytingLean.Chem.PeriodicTable

structure ElementInfo where
  atomicNumber : Nat
  symbol : String
  name : String
  standardAtomicWeight : Option String
  noteCodes : List String
deriving Repr, DecidableEq

def table : Array ElementInfo :=
  #[
    { atomicNumber := 1
      symbol := "H"
      name := "hydrogen"
      standardAtomicWeight := some "[1.007 84, 1.008 11]"
      noteCodes := ["m"]
    },
    { atomicNumber := 2
      symbol := "He"
      name := "helium"
      standardAtomicWeight := some "4.002 602(2)"
      noteCodes := ["g", "r"]
    },
    { atomicNumber := 3
      symbol := "Li"
      name := "lithium"
      standardAtomicWeight := some "[6.938, 6.997]"
      noteCodes := ["m"]
    },
    { atomicNumber := 4
      symbol := "Be"
      name := "beryllium"
      standardAtomicWeight := some "9.012 1831(5)"
      noteCodes := []
    },
    { atomicNumber := 5
      symbol := "B"
      name := "boron"
      standardAtomicWeight := some "[10.806, 10.821]"
      noteCodes := ["m"]
    },
    { atomicNumber := 6
      symbol := "C"
      name := "carbon"
      standardAtomicWeight := some "[12.0096, 12.0116]"
      noteCodes := []
    },
    { atomicNumber := 7
      symbol := "N"
      name := "nitrogen"
      standardAtomicWeight := some "[14.006 43, 14.007 28]"
      noteCodes := ["m"]
    },
    { atomicNumber := 8
      symbol := "O"
      name := "oxygen"
      standardAtomicWeight := some "[15.999 03, 15.999 77]"
      noteCodes := ["m"]
    },
    { atomicNumber := 9
      symbol := "F"
      name := "fluorine"
      standardAtomicWeight := some "18.998 403 162(5)"
      noteCodes := []
    },
    { atomicNumber := 10
      symbol := "Ne"
      name := "neon"
      standardAtomicWeight := some "20.1797(6)"
      noteCodes := ["g", "m"]
    },
    { atomicNumber := 11
      symbol := "Na"
      name := "sodium"
      standardAtomicWeight := some "22.989 769 28(2)"
      noteCodes := []
    },
    { atomicNumber := 12
      symbol := "Mg"
      name := "magnesium"
      standardAtomicWeight := some "[24.304, 24.307]"
      noteCodes := []
    },
    { atomicNumber := 13
      symbol := "Al"
      name := "aluminium"
      standardAtomicWeight := some "26.981 5384(3)"
      noteCodes := []
    },
    { atomicNumber := 14
      symbol := "Si"
      name := "silicon"
      standardAtomicWeight := some "[28.084, 28.086]"
      noteCodes := []
    },
    { atomicNumber := 15
      symbol := "P"
      name := "phosphorus"
      standardAtomicWeight := some "30.973 761 998(5)"
      noteCodes := []
    },
    { atomicNumber := 16
      symbol := "S"
      name := "sulfur"
      standardAtomicWeight := some "[32.059, 32.076]"
      noteCodes := []
    },
    { atomicNumber := 17
      symbol := "Cl"
      name := "chlorine"
      standardAtomicWeight := some "[35.446, 35.457]"
      noteCodes := ["m"]
    },
    { atomicNumber := 18
      symbol := "Ar"
      name := "argon"
      standardAtomicWeight := some "[39.792, 39.963]"
      noteCodes := []
    },
    { atomicNumber := 19
      symbol := "K"
      name := "potassium"
      standardAtomicWeight := some "39.0983(1)"
      noteCodes := []
    },
    { atomicNumber := 20
      symbol := "Ca"
      name := "calcium"
      standardAtomicWeight := some "40.078(4)"
      noteCodes := ["g"]
    },
    { atomicNumber := 21
      symbol := "Sc"
      name := "scandium"
      standardAtomicWeight := some "44.955 907(4)"
      noteCodes := []
    },
    { atomicNumber := 22
      symbol := "Ti"
      name := "titanium"
      standardAtomicWeight := some "47.867(1)"
      noteCodes := []
    },
    { atomicNumber := 23
      symbol := "V"
      name := "vanadium"
      standardAtomicWeight := some "50.9415(1)"
      noteCodes := []
    },
    { atomicNumber := 24
      symbol := "Cr"
      name := "chromium"
      standardAtomicWeight := some "51.9961(6)"
      noteCodes := []
    },
    { atomicNumber := 25
      symbol := "Mn"
      name := "manganese"
      standardAtomicWeight := some "54.938 043(2)"
      noteCodes := []
    },
    { atomicNumber := 26
      symbol := "Fe"
      name := "iron"
      standardAtomicWeight := some "55.845(2)"
      noteCodes := []
    },
    { atomicNumber := 27
      symbol := "Co"
      name := "cobalt"
      standardAtomicWeight := some "58.933 194(3)"
      noteCodes := []
    },
    { atomicNumber := 28
      symbol := "Ni"
      name := "nickel"
      standardAtomicWeight := some "58.6934(4)"
      noteCodes := ["r"]
    },
    { atomicNumber := 29
      symbol := "Cu"
      name := "copper"
      standardAtomicWeight := some "63.546(3)"
      noteCodes := ["r"]
    },
    { atomicNumber := 30
      symbol := "Zn"
      name := "zinc"
      standardAtomicWeight := some "65.38(2)"
      noteCodes := ["r"]
    },
    { atomicNumber := 31
      symbol := "Ga"
      name := "gallium"
      standardAtomicWeight := some "69.723(1)"
      noteCodes := []
    },
    { atomicNumber := 32
      symbol := "Ge"
      name := "germanium"
      standardAtomicWeight := some "72.630(8)"
      noteCodes := []
    },
    { atomicNumber := 33
      symbol := "As"
      name := "arsenic"
      standardAtomicWeight := some "74.921 595(6)"
      noteCodes := []
    },
    { atomicNumber := 34
      symbol := "Se"
      name := "selenium"
      standardAtomicWeight := some "78.971(8)"
      noteCodes := ["r"]
    },
    { atomicNumber := 35
      symbol := "Br"
      name := "bromine"
      standardAtomicWeight := some "[79.901, 79.907]"
      noteCodes := []
    },
    { atomicNumber := 36
      symbol := "Kr"
      name := "krypton"
      standardAtomicWeight := some "83.798(2)"
      noteCodes := ["g", "m"]
    },
    { atomicNumber := 37
      symbol := "Rb"
      name := "rubidium"
      standardAtomicWeight := some "85.4678(3)"
      noteCodes := ["g"]
    },
    { atomicNumber := 38
      symbol := "Sr"
      name := "strontium"
      standardAtomicWeight := some "87.62(1)"
      noteCodes := ["g", "r"]
    },
    { atomicNumber := 39
      symbol := "Y"
      name := "yttrium"
      standardAtomicWeight := some "88.905 838(2)"
      noteCodes := []
    },
    { atomicNumber := 40
      symbol := "Zr"
      name := "zirconium"
      standardAtomicWeight := some "91.222(3)"
      noteCodes := ["g"]
    },
    { atomicNumber := 41
      symbol := "Nb"
      name := "niobium"
      standardAtomicWeight := some "92.906 37(1)"
      noteCodes := []
    },
    { atomicNumber := 42
      symbol := "Mo"
      name := "molybdenum"
      standardAtomicWeight := some "95.95(1)"
      noteCodes := ["g"]
    },
    { atomicNumber := 43
      symbol := "Tc"
      name := "technetium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 44
      symbol := "Ru"
      name := "ruthenium"
      standardAtomicWeight := some "101.07(2)"
      noteCodes := ["g"]
    },
    { atomicNumber := 45
      symbol := "Rh"
      name := "rhodium"
      standardAtomicWeight := some "102.905 49(2)"
      noteCodes := []
    },
    { atomicNumber := 46
      symbol := "Pd"
      name := "palladium"
      standardAtomicWeight := some "106.42(1)"
      noteCodes := ["g"]
    },
    { atomicNumber := 47
      symbol := "Ag"
      name := "silver"
      standardAtomicWeight := some "107.8682(2)"
      noteCodes := ["g"]
    },
    { atomicNumber := 48
      symbol := "Cd"
      name := "cadmium"
      standardAtomicWeight := some "112.414(4)"
      noteCodes := ["g"]
    },
    { atomicNumber := 49
      symbol := "In"
      name := "indium"
      standardAtomicWeight := some "114.818(1)"
      noteCodes := []
    },
    { atomicNumber := 50
      symbol := "Sn"
      name := "tin"
      standardAtomicWeight := some "118.710(7)"
      noteCodes := ["g"]
    },
    { atomicNumber := 51
      symbol := "Sb"
      name := "antimony"
      standardAtomicWeight := some "121.760(1)"
      noteCodes := ["g"]
    },
    { atomicNumber := 52
      symbol := "Te"
      name := "tellurium"
      standardAtomicWeight := some "127.60(3)"
      noteCodes := ["g"]
    },
    { atomicNumber := 53
      symbol := "I"
      name := "iodine"
      standardAtomicWeight := some "126.904 47(3)"
      noteCodes := []
    },
    { atomicNumber := 54
      symbol := "Xe"
      name := "xenon"
      standardAtomicWeight := some "131.293(6)"
      noteCodes := ["g", "m"]
    },
    { atomicNumber := 55
      symbol := "Cs"
      name := "caesium"
      standardAtomicWeight := some "132.905 451 96(6)"
      noteCodes := []
    },
    { atomicNumber := 56
      symbol := "Ba"
      name := "barium"
      standardAtomicWeight := some "137.327(7)"
      noteCodes := []
    },
    { atomicNumber := 57
      symbol := "La"
      name := "lanthanum"
      standardAtomicWeight := some "138.905 47(7)"
      noteCodes := ["g"]
    },
    { atomicNumber := 58
      symbol := "Ce"
      name := "cerium"
      standardAtomicWeight := some "140.116(1)"
      noteCodes := ["g"]
    },
    { atomicNumber := 59
      symbol := "Pr"
      name := "praseodymium"
      standardAtomicWeight := some "140.907 66(1)"
      noteCodes := []
    },
    { atomicNumber := 60
      symbol := "Nd"
      name := "neodymium"
      standardAtomicWeight := some "144.242(3)"
      noteCodes := ["g"]
    },
    { atomicNumber := 61
      symbol := "Pm"
      name := "promethium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 62
      symbol := "Sm"
      name := "samarium"
      standardAtomicWeight := some "150.36(2)"
      noteCodes := ["g"]
    },
    { atomicNumber := 63
      symbol := "Eu"
      name := "europium"
      standardAtomicWeight := some "151.964(1)"
      noteCodes := ["g"]
    },
    { atomicNumber := 64
      symbol := "Gd"
      name := "gadolinium"
      standardAtomicWeight := some "157.249(2)"
      noteCodes := ["g"]
    },
    { atomicNumber := 65
      symbol := "Tb"
      name := "terbium"
      standardAtomicWeight := some "158.925 354(7)"
      noteCodes := []
    },
    { atomicNumber := 66
      symbol := "Dy"
      name := "dysprosium"
      standardAtomicWeight := some "162.500(1)"
      noteCodes := ["g"]
    },
    { atomicNumber := 67
      symbol := "Ho"
      name := "holmium"
      standardAtomicWeight := some "164.930 329(5)"
      noteCodes := []
    },
    { atomicNumber := 68
      symbol := "Er"
      name := "erbium"
      standardAtomicWeight := some "167.259(3)"
      noteCodes := ["g"]
    },
    { atomicNumber := 69
      symbol := "Tm"
      name := "thulium"
      standardAtomicWeight := some "168.934 219(5)"
      noteCodes := []
    },
    { atomicNumber := 70
      symbol := "Yb"
      name := "ytterbium"
      standardAtomicWeight := some "173.045(10)"
      noteCodes := ["g"]
    },
    { atomicNumber := 71
      symbol := "Lu"
      name := "lutetium"
      standardAtomicWeight := some "174.966 69(5)"
      noteCodes := ["g"]
    },
    { atomicNumber := 72
      symbol := "Hf"
      name := "hafnium"
      standardAtomicWeight := some "178.486(6)"
      noteCodes := ["g"]
    },
    { atomicNumber := 73
      symbol := "Ta"
      name := "tantalum"
      standardAtomicWeight := some "180.947 88(2)"
      noteCodes := []
    },
    { atomicNumber := 74
      symbol := "W"
      name := "tungsten"
      standardAtomicWeight := some "183.84(1)"
      noteCodes := []
    },
    { atomicNumber := 75
      symbol := "Re"
      name := "rhenium"
      standardAtomicWeight := some "186.207(1)"
      noteCodes := []
    },
    { atomicNumber := 76
      symbol := "Os"
      name := "osmium"
      standardAtomicWeight := some "190.23(3)"
      noteCodes := ["g"]
    },
    { atomicNumber := 77
      symbol := "Ir"
      name := "iridium"
      standardAtomicWeight := some "192.217(2)"
      noteCodes := []
    },
    { atomicNumber := 78
      symbol := "Pt"
      name := "platinum"
      standardAtomicWeight := some "195.084(9)"
      noteCodes := []
    },
    { atomicNumber := 79
      symbol := "Au"
      name := "gold"
      standardAtomicWeight := some "196.966 570(4)"
      noteCodes := []
    },
    { atomicNumber := 80
      symbol := "Hg"
      name := "mercury"
      standardAtomicWeight := some "200.592(3)"
      noteCodes := []
    },
    { atomicNumber := 81
      symbol := "Tl"
      name := "thallium"
      standardAtomicWeight := some "[204.382, 204.385]"
      noteCodes := []
    },
    { atomicNumber := 82
      symbol := "Pb"
      name := "lead"
      standardAtomicWeight := some "[206.14, 207.94]"
      noteCodes := []
    },
    { atomicNumber := 83
      symbol := "Bi"
      name := "bismuth"
      standardAtomicWeight := some "208.980 40(1)"
      noteCodes := []
    },
    { atomicNumber := 84
      symbol := "Po"
      name := "polonium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 85
      symbol := "At"
      name := "astatine"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 86
      symbol := "Rn"
      name := "radon"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 87
      symbol := "Fr"
      name := "francium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 88
      symbol := "Ra"
      name := "radium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 89
      symbol := "Ac"
      name := "actinium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 90
      symbol := "Th"
      name := "thorium"
      standardAtomicWeight := some "232.0377(4)"
      noteCodes := ["g"]
    },
    { atomicNumber := 91
      symbol := "Pa"
      name := "protactinium"
      standardAtomicWeight := some "231.035 88(1)"
      noteCodes := []
    },
    { atomicNumber := 92
      symbol := "U"
      name := "uranium"
      standardAtomicWeight := some "238.028 91(3)"
      noteCodes := ["g", "m"]
    },
    { atomicNumber := 93
      symbol := "Np"
      name := "neptunium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 94
      symbol := "Pu"
      name := "plutonium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 95
      symbol := "Am"
      name := "americium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 96
      symbol := "Cm"
      name := "curium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 97
      symbol := "Bk"
      name := "berkelium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 98
      symbol := "Cf"
      name := "californium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 99
      symbol := "Es"
      name := "einsteinium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 100
      symbol := "Fm"
      name := "fermium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 101
      symbol := "Md"
      name := "mendelevium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 102
      symbol := "No"
      name := "nobelium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 103
      symbol := "Lr"
      name := "lawrencium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 104
      symbol := "Rf"
      name := "rutherfordium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 105
      symbol := "Db"
      name := "dubnium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 106
      symbol := "Sg"
      name := "seaborgium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 107
      symbol := "Bh"
      name := "bohrium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 108
      symbol := "Hs"
      name := "hassium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 109
      symbol := "Mt"
      name := "meitnerium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 110
      symbol := "Ds"
      name := "darmstadtium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 111
      symbol := "Rg"
      name := "roentgenium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 112
      symbol := "Cn"
      name := "copernicium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 113
      symbol := "Nh"
      name := "nihonium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 114
      symbol := "Fl"
      name := "flerovium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 115
      symbol := "Mc"
      name := "moscovium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 116
      symbol := "Lv"
      name := "livermorium"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 117
      symbol := "Ts"
      name := "tennessine"
      standardAtomicWeight := none
      noteCodes := []
    },
    { atomicNumber := 118
      symbol := "Og"
      name := "oganesson"
      standardAtomicWeight := none
      noteCodes := []
    },
  ]

abbrev Element : Type := Fin 118

@[simp] theorem table_size : table.size = 118 := rfl

def info (e : Element) : ElementInfo :=
  table[(⟨e.val, by
    simp [table_size]
  ⟩ : Fin table.size)]

def atomicNumber (e : Element) : Nat := (info e).atomicNumber
def symbol (e : Element) : String := (info e).symbol
def name (e : Element) : String := (info e).name
def standardAtomicWeight? (e : Element) : Option String := (info e).standardAtomicWeight
def noteCodes (e : Element) : List String := (info e).noteCodes

def ofAtomicNumber? (n : Nat) : Option Element :=
  if n = 0 then none else
    let m := n - 1
    if hm : m < 118 then some ⟨m, hm⟩ else none

def infoByAtomicNumber? (n : Nat) : Option ElementInfo :=
  (ofAtomicNumber? n).map info

end HeytingLean.Chem.PeriodicTable
