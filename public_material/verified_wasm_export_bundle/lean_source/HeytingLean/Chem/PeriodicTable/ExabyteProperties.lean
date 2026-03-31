/-
Auto-generated periodic-table property snapshot from:
  https://github.com/exabyte-io/periodic-table
Revision: 0f969c06e15c
Source JSON: data/chem/periodic_table_exabyte_0f969c06e15c.json
Generated on: 2026-02-03

Do not edit by hand. Regenerate with:
  python3 scripts/chem_import_exabyte_periodic_table.py --json data/chem/periodic_table_exabyte_0f969c06e15c.json --rev 0f969c06e15c --out lean/HeytingLean/Chem/PeriodicTable/ExabyteProperties.lean
-/

import HeytingLean.Chem.PeriodicTable.CIAAW2024
import Mathlib.Data.Int.Basic

namespace HeytingLean.Chem.PeriodicTable

/--
Element properties as provided by the Exabyte periodic-table dataset.

Most numeric-looking fields are stored as `Option String` because the upstream
mixes plain numbers and annotated strings (approximation markers, phase notes, etc.).
-/
structure ExabyteElementProperties where
  atomicNumber : Nat
  symbol : String
  name : String
  atomicMass : Option String
  atomicRadius_pm : Option String
  atomicVolume_cm3_per_mol : Option String
  boilingPoint_K : Option String
  covalentRadius_pm : Option String
  density_g_per_cm3 : Option String
  electronicConfiguration : Option String
  evaporationHeat_kJ_mol : Option String
  firstIonizing_kJ_mol : Option String
  fusionHeat_kJ_mol : Option String
  ionicRadius_pm : Option String
  latticeConstant_ang : Option String
  latticeStructure : Option String
  meltingPoint_K : Option String
  oxidationStates : List Int
  paulingNegativity : Option String
  specificHeat_J_g_mol : Option String
  thermalConductivity_25C_W_m_K : Option String
  vanDerWaalsRadius_pm : Option String
deriving Repr, DecidableEq

def exabyteTable : Array ExabyteElementProperties :=
  #[
{
      atomicNumber := 1
      symbol := "H"
      name := "Hydrogen"
      atomicMass := some "1.00794"
      atomicRadius_pm := some "25"
      atomicVolume_cm3_per_mol := some "14.1"
      boilingPoint_K := some "20.28"
      covalentRadius_pm := some "32"
      density_g_per_cm3 := some "0.0708 (@ -253degC)"
      electronicConfiguration := some "1s1"
      evaporationHeat_kJ_mol := some "0.904 (H-H)"
      firstIonizing_kJ_mol := some "1311.3"
      fusionHeat_kJ_mol := some "0.117 (H-H)"
      ionicRadius_pm := none
      latticeConstant_ang := some "3.75"
      latticeStructure := some "HEX"
      meltingPoint_K := some "14.01"
      oxidationStates := [1, -1]
      paulingNegativity := some "2.2"
      specificHeat_J_g_mol := some "14.267 (H-H)"
      thermalConductivity_25C_W_m_K := some "0.1815"
      vanDerWaalsRadius_pm := some "120"
    },
{
      atomicNumber := 2
      symbol := "He"
      name := "Helium"
      atomicMass := some "4.002602"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := some "31.8"
      boilingPoint_K := some "4.216"
      covalentRadius_pm := some "28"
      density_g_per_cm3 := some "0.147 (@ -270degC)"
      electronicConfiguration := some "1s2"
      evaporationHeat_kJ_mol := some "0.08"
      firstIonizing_kJ_mol := some "2361.3"
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := some "3.57"
      latticeStructure := some "HEX"
      meltingPoint_K := some "0.95"
      oxidationStates := []
      paulingNegativity := none
      specificHeat_J_g_mol := some "5.188"
      thermalConductivity_25C_W_m_K := some "0.152"
      vanDerWaalsRadius_pm := some "140"
    },
{
      atomicNumber := 3
      symbol := "Li"
      name := "Lithium"
      atomicMass := some "6.941"
      atomicRadius_pm := some "145"
      atomicVolume_cm3_per_mol := some "13.1"
      boilingPoint_K := some "1118.15"
      covalentRadius_pm := some "128"
      density_g_per_cm3 := some "0.534"
      electronicConfiguration := some "[He]2s1"
      evaporationHeat_kJ_mol := some "148"
      firstIonizing_kJ_mol := some "519.9"
      fusionHeat_kJ_mol := some "2.89"
      ionicRadius_pm := none
      latticeConstant_ang := some "3.49"
      latticeStructure := some "BCC"
      meltingPoint_K := some "553.69"
      oxidationStates := [1]
      paulingNegativity := some "0.98"
      specificHeat_J_g_mol := some "3.489"
      thermalConductivity_25C_W_m_K := some "84.8"
      vanDerWaalsRadius_pm := some "182"
    },
{
      atomicNumber := 4
      symbol := "Be"
      name := "Beryllium"
      atomicMass := some "9.01218"
      atomicRadius_pm := some "105"
      atomicVolume_cm3_per_mol := some "5"
      boilingPoint_K := some "3243"
      covalentRadius_pm := some "96"
      density_g_per_cm3 := some "1.848"
      electronicConfiguration := some "[He]2s2"
      evaporationHeat_kJ_mol := some "309"
      firstIonizing_kJ_mol := some "898.8"
      fusionHeat_kJ_mol := some "12.21"
      ionicRadius_pm := none
      latticeConstant_ang := some "2.29"
      latticeStructure := some "HEX"
      meltingPoint_K := some "1551"
      oxidationStates := [2]
      paulingNegativity := some "1.57"
      specificHeat_J_g_mol := some "1.824"
      thermalConductivity_25C_W_m_K := some "201"
      vanDerWaalsRadius_pm := some "153"
    },
{
      atomicNumber := 5
      symbol := "B"
      name := "Boron"
      atomicMass := some "10.811"
      atomicRadius_pm := some "85"
      atomicVolume_cm3_per_mol := some "4.6"
      boilingPoint_K := some "3931"
      covalentRadius_pm := some "84"
      density_g_per_cm3 := some "2.34"
      electronicConfiguration := some "[He]2s22p1"
      evaporationHeat_kJ_mol := some "504.5"
      firstIonizing_kJ_mol := some "800.2"
      fusionHeat_kJ_mol := some "23.6"
      ionicRadius_pm := none
      latticeConstant_ang := some "8.73"
      latticeStructure := some "TET"
      meltingPoint_K := some "2573"
      oxidationStates := [3]
      paulingNegativity := some "2.04"
      specificHeat_J_g_mol := some "1.025"
      thermalConductivity_25C_W_m_K := some "27.4"
      vanDerWaalsRadius_pm := some "192"
    },
{
      atomicNumber := 6
      symbol := "C"
      name := "Carbon"
      atomicMass := some "12.011"
      atomicRadius_pm := some "70"
      atomicVolume_cm3_per_mol := some "5.3"
      boilingPoint_K := some "5100"
      covalentRadius_pm := some "76"
      density_g_per_cm3 := some "2.25 (graphite)"
      electronicConfiguration := some "[He]2s22p2"
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := some "1085.7"
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := some "3.57"
      latticeStructure := some "DIA"
      meltingPoint_K := some "3820"
      oxidationStates := [4, 2, -4]
      paulingNegativity := some "2.55"
      specificHeat_J_g_mol := some "0.711"
      thermalConductivity_25C_W_m_K := some "1.59"
      vanDerWaalsRadius_pm := some "170"
    },
{
      atomicNumber := 7
      symbol := "N"
      name := "Nitrogen"
      atomicMass := some "14.00674"
      atomicRadius_pm := some "65"
      atomicVolume_cm3_per_mol := some "17.3"
      boilingPoint_K := some "77.4"
      covalentRadius_pm := some "71"
      density_g_per_cm3 := some "0.808 (@ -195.8degC)"
      electronicConfiguration := some "[He]2s22p3"
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := some "1401.5"
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := some "4.039"
      latticeStructure := some "HEX"
      meltingPoint_K := some "63.29"
      oxidationStates := [5, 4, 3, 2, -3]
      paulingNegativity := some "3.04"
      specificHeat_J_g_mol := some "1.042 (N-N)"
      thermalConductivity_25C_W_m_K := some "0.026"
      vanDerWaalsRadius_pm := some "155"
    },
{
      atomicNumber := 8
      symbol := "O"
      name := "Oxygen"
      atomicMass := some "15.9994"
      atomicRadius_pm := some "60"
      atomicVolume_cm3_per_mol := some "14"
      boilingPoint_K := some "90.19"
      covalentRadius_pm := some "66"
      density_g_per_cm3 := some "1.149 (@ -183degC)"
      electronicConfiguration := some "[He]2s22p"
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := some "1313.1"
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := some "6.83"
      latticeStructure := some "CUB"
      meltingPoint_K := some "54.8"
      oxidationStates := [-2, -1]
      paulingNegativity := some "3.44"
      specificHeat_J_g_mol := some "0.916 (O-O)"
      thermalConductivity_25C_W_m_K := some "0.027"
      vanDerWaalsRadius_pm := some "152"
    },
{
      atomicNumber := 9
      symbol := "F"
      name := "Fluorine"
      atomicMass := some "18.998404"
      atomicRadius_pm := some "50"
      atomicVolume_cm3_per_mol := some "17.1"
      boilingPoint_K := some "85.01"
      covalentRadius_pm := some "57"
      density_g_per_cm3 := some "1.108 (@ -189degC)"
      electronicConfiguration := some "[He]2s22p"
      evaporationHeat_kJ_mol := some "6.54 (F-F)"
      firstIonizing_kJ_mol := some "1680"
      fusionHeat_kJ_mol := some "0.51 (F-F)"
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := some "MCL"
      meltingPoint_K := some "53.53"
      oxidationStates := [-1]
      paulingNegativity := some "3.98"
      specificHeat_J_g_mol := some "0.824 (F-F)"
      thermalConductivity_25C_W_m_K := some "0.028"
      vanDerWaalsRadius_pm := some "147"
    },
{
      atomicNumber := 10
      symbol := "Ne"
      name := "Neon"
      atomicMass := some "20.1797"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := some "16.8"
      boilingPoint_K := some "27.1"
      covalentRadius_pm := some "58"
      density_g_per_cm3 := some "1.204 (@ -246degC)"
      electronicConfiguration := some "[He]2s22p"
      evaporationHeat_kJ_mol := some "1.74"
      firstIonizing_kJ_mol := some "2079.4"
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := some "4.43"
      latticeStructure := some "FCC"
      meltingPoint_K := some "48"
      oxidationStates := []
      paulingNegativity := some "0"
      specificHeat_J_g_mol := some "1.029"
      thermalConductivity_25C_W_m_K := some "(0.0493)"
      vanDerWaalsRadius_pm := some "154"
    },
{
      atomicNumber := 11
      symbol := "Na"
      name := "Sodium"
      atomicMass := some "22.989767"
      atomicRadius_pm := some "180"
      atomicVolume_cm3_per_mol := some "23.7"
      boilingPoint_K := some "1156.1"
      covalentRadius_pm := some "166"
      density_g_per_cm3 := some "0.971"
      electronicConfiguration := some "[Ne]3s1"
      evaporationHeat_kJ_mol := some "97.9"
      firstIonizing_kJ_mol := some "495.6"
      fusionHeat_kJ_mol := some "2.64"
      ionicRadius_pm := none
      latticeConstant_ang := some "4.23"
      latticeStructure := some "BCC"
      meltingPoint_K := some "370.96"
      oxidationStates := [1]
      paulingNegativity := some "0.93"
      specificHeat_J_g_mol := some "1.222"
      thermalConductivity_25C_W_m_K := some "142"
      vanDerWaalsRadius_pm := some "227"
    },
{
      atomicNumber := 12
      symbol := "Mg"
      name := "Magnesium"
      atomicMass := some "24.305"
      atomicRadius_pm := some "150"
      atomicVolume_cm3_per_mol := some "14"
      boilingPoint_K := some "1363"
      covalentRadius_pm := some "141"
      density_g_per_cm3 := some "1.738"
      electronicConfiguration := some "[Ne]3s2"
      evaporationHeat_kJ_mol := some "131.8"
      firstIonizing_kJ_mol := some "737.3"
      fusionHeat_kJ_mol := some "9.2"
      ionicRadius_pm := none
      latticeConstant_ang := some "3.21"
      latticeStructure := some "HEX"
      meltingPoint_K := some "922"
      oxidationStates := [2]
      paulingNegativity := some "1.31"
      specificHeat_J_g_mol := some "1.025"
      thermalConductivity_25C_W_m_K := some "156"
      vanDerWaalsRadius_pm := some "173"
    },
{
      atomicNumber := 13
      symbol := "Al"
      name := "Aluminum"
      atomicMass := some "26.981539"
      atomicRadius_pm := some "125"
      atomicVolume_cm3_per_mol := some "10"
      boilingPoint_K := some "2740"
      covalentRadius_pm := some "121"
      density_g_per_cm3 := some "2.6989"
      electronicConfiguration := some "[Ne]3s23p1"
      evaporationHeat_kJ_mol := some "284.1"
      firstIonizing_kJ_mol := some "577.2"
      fusionHeat_kJ_mol := some "10.75"
      ionicRadius_pm := none
      latticeConstant_ang := some "4.05"
      latticeStructure := some "FCC"
      meltingPoint_K := some "933.5"
      oxidationStates := [3]
      paulingNegativity := some "1.61"
      specificHeat_J_g_mol := some "0.9"
      thermalConductivity_25C_W_m_K := some "237"
      vanDerWaalsRadius_pm := some "184"
    },
{
      atomicNumber := 14
      symbol := "Si"
      name := "Silicon"
      atomicMass := some "28.0855"
      atomicRadius_pm := some "110"
      atomicVolume_cm3_per_mol := some "12.1"
      boilingPoint_K := some "2628"
      covalentRadius_pm := some "111"
      density_g_per_cm3 := some "2.33"
      electronicConfiguration := some "[Ne]3s23p2"
      evaporationHeat_kJ_mol := some "383"
      firstIonizing_kJ_mol := some "786"
      fusionHeat_kJ_mol := some "50.6"
      ionicRadius_pm := none
      latticeConstant_ang := some "5.43"
      latticeStructure := some "DIA"
      meltingPoint_K := some "1683"
      oxidationStates := [4, -4]
      paulingNegativity := some "1.9"
      specificHeat_J_g_mol := some "0.703"
      thermalConductivity_25C_W_m_K := some "149"
      vanDerWaalsRadius_pm := some "210"
    },
{
      atomicNumber := 15
      symbol := "P"
      name := "Phosphorus"
      atomicMass := some "30.973763"
      atomicRadius_pm := some "100"
      atomicVolume_cm3_per_mol := some "17"
      boilingPoint_K := some "553"
      covalentRadius_pm := some "107"
      density_g_per_cm3 := some "1.82 (white phosphorus)"
      electronicConfiguration := some "[Ne]3s23p3"
      evaporationHeat_kJ_mol := some "49.8"
      firstIonizing_kJ_mol := some "1011.2"
      fusionHeat_kJ_mol := some "2.51"
      ionicRadius_pm := none
      latticeConstant_ang := some "7.17"
      latticeStructure := some "CUB"
      meltingPoint_K := some "317.3"
      oxidationStates := [5, 3, -3]
      paulingNegativity := some "2.19"
      specificHeat_J_g_mol := some "0.757"
      thermalConductivity_25C_W_m_K := some "(0.236)"
      vanDerWaalsRadius_pm := some "180"
    },
{
      atomicNumber := 16
      symbol := "S"
      name := "Sulfur"
      atomicMass := some "32.066"
      atomicRadius_pm := some "100"
      atomicVolume_cm3_per_mol := some "15.5"
      boilingPoint_K := some "717.824"
      covalentRadius_pm := some "105"
      density_g_per_cm3 := some "2.07"
      electronicConfiguration := some "[Ne]3s23p"
      evaporationHeat_kJ_mol := some "10.5"
      firstIonizing_kJ_mol := some "999"
      fusionHeat_kJ_mol := some "1.23"
      ionicRadius_pm := none
      latticeConstant_ang := some "10.47"
      latticeStructure := some "ORC"
      meltingPoint_K := some "386"
      oxidationStates := [6, 4, 2, -2]
      paulingNegativity := some "2.58"
      specificHeat_J_g_mol := some "0.732"
      thermalConductivity_25C_W_m_K := some "0.27"
      vanDerWaalsRadius_pm := some "180"
    },
{
      atomicNumber := 17
      symbol := "Cl"
      name := "Chlorine"
      atomicMass := some "35.4527"
      atomicRadius_pm := some "100"
      atomicVolume_cm3_per_mol := some "18.7"
      boilingPoint_K := some "238.6"
      covalentRadius_pm := some "102"
      density_g_per_cm3 := some "1.56 (@ -33.6degC)"
      electronicConfiguration := some "[Ne]3s23p"
      evaporationHeat_kJ_mol := some "20.41 (Cl-Cl)"
      firstIonizing_kJ_mol := some "1254.9"
      fusionHeat_kJ_mol := some "6.41 (Cl-Cl)"
      ionicRadius_pm := none
      latticeConstant_ang := some "6.24"
      latticeStructure := some "ORC"
      meltingPoint_K := some "172.2"
      oxidationStates := [7, 5, 3, 1, -1]
      paulingNegativity := some "3.16"
      specificHeat_J_g_mol := some "0.477 (Cl-Cl)"
      thermalConductivity_25C_W_m_K := some "0.009"
      vanDerWaalsRadius_pm := some "175"
    },
{
      atomicNumber := 18
      symbol := "Ar"
      name := "Argon"
      atomicMass := some "39.948"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := some "24.2"
      boilingPoint_K := some "87.3"
      covalentRadius_pm := some "106"
      density_g_per_cm3 := some "1.40 (@ -186degC)"
      electronicConfiguration := some "[Ne]3s23p"
      evaporationHeat_kJ_mol := some "6.52"
      firstIonizing_kJ_mol := some "1519.6"
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := some "5.26"
      latticeStructure := some "FCC"
      meltingPoint_K := some "83.8"
      oxidationStates := []
      paulingNegativity := some "0"
      specificHeat_J_g_mol := some "0.138"
      thermalConductivity_25C_W_m_K := some "0.0177"
      vanDerWaalsRadius_pm := some "188"
    },
{
      atomicNumber := 19
      symbol := "K"
      name := "Potassium"
      atomicMass := some "39.0983"
      atomicRadius_pm := some "220"
      atomicVolume_cm3_per_mol := some "45.3"
      boilingPoint_K := some "1047"
      covalentRadius_pm := some "203"
      density_g_per_cm3 := some "0.856"
      electronicConfiguration := some "[Ar]4s1"
      evaporationHeat_kJ_mol := some "2.33"
      firstIonizing_kJ_mol := some "418.5"
      fusionHeat_kJ_mol := some "102.5"
      ionicRadius_pm := none
      latticeConstant_ang := some "5.23"
      latticeStructure := some "BCC"
      meltingPoint_K := some "336.8"
      oxidationStates := [1]
      paulingNegativity := some "0.82"
      specificHeat_J_g_mol := some "0.753"
      thermalConductivity_25C_W_m_K := some "79"
      vanDerWaalsRadius_pm := some "275"
    },
{
      atomicNumber := 20
      symbol := "Ca"
      name := "Calcium"
      atomicMass := some "40.078"
      atomicRadius_pm := some "180"
      atomicVolume_cm3_per_mol := some "29.9"
      boilingPoint_K := some "1757"
      covalentRadius_pm := some "176"
      density_g_per_cm3 := some "1.55"
      electronicConfiguration := some "[Ar]4s2"
      evaporationHeat_kJ_mol := some "153.6"
      firstIonizing_kJ_mol := some "589.4"
      fusionHeat_kJ_mol := some "9.2"
      ionicRadius_pm := none
      latticeConstant_ang := some "5.58"
      latticeStructure := some "FCC"
      meltingPoint_K := some "1112"
      oxidationStates := [2]
      paulingNegativity := some "1"
      specificHeat_J_g_mol := some "0.653"
      thermalConductivity_25C_W_m_K := some "(201)"
      vanDerWaalsRadius_pm := some "231"
    },
{
      atomicNumber := 21
      symbol := "Sc"
      name := "Scandium"
      atomicMass := some "44.95591"
      atomicRadius_pm := some "160"
      atomicVolume_cm3_per_mol := some "15"
      boilingPoint_K := some "3104"
      covalentRadius_pm := some "170"
      density_g_per_cm3 := some "2.99"
      electronicConfiguration := some "[Ar]3d14s2"
      evaporationHeat_kJ_mol := some "332.7"
      firstIonizing_kJ_mol := some "630.8"
      fusionHeat_kJ_mol := some "15.8"
      ionicRadius_pm := none
      latticeConstant_ang := some "3.31"
      latticeStructure := some "HEX"
      meltingPoint_K := some "1814"
      oxidationStates := [3]
      paulingNegativity := some "1.36"
      specificHeat_J_g_mol := some "0.556"
      thermalConductivity_25C_W_m_K := some "15.8"
      vanDerWaalsRadius_pm := some "211"
    },
{
      atomicNumber := 22
      symbol := "Ti"
      name := "Titanium"
      atomicMass := some "47.88"
      atomicRadius_pm := some "140"
      atomicVolume_cm3_per_mol := some "10.6"
      boilingPoint_K := some "3560"
      covalentRadius_pm := some "160"
      density_g_per_cm3 := some "4.54"
      electronicConfiguration := some "[Ar]3d24s2"
      evaporationHeat_kJ_mol := some "422.6"
      firstIonizing_kJ_mol := some "657.8"
      fusionHeat_kJ_mol := some "18.8"
      ionicRadius_pm := none
      latticeConstant_ang := some "2.95"
      latticeStructure := some "HEX"
      meltingPoint_K := some "1933"
      oxidationStates := [4, 3]
      paulingNegativity := some "1.54"
      specificHeat_J_g_mol := some "0.523"
      thermalConductivity_25C_W_m_K := some "21.9"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 23
      symbol := "V"
      name := "Vanadium"
      atomicMass := some "50.9415"
      atomicRadius_pm := some "135"
      atomicVolume_cm3_per_mol := some "8.35"
      boilingPoint_K := some "3650"
      covalentRadius_pm := some "153"
      density_g_per_cm3 := some "6.11"
      electronicConfiguration := some "[Ar]3d34s2"
      evaporationHeat_kJ_mol := some "460"
      firstIonizing_kJ_mol := some "650.1"
      fusionHeat_kJ_mol := some "17.5"
      ionicRadius_pm := none
      latticeConstant_ang := some "3.02"
      latticeStructure := some "BCC"
      meltingPoint_K := some "2160"
      oxidationStates := [5, 4, 3, 2, 0]
      paulingNegativity := some "1.63"
      specificHeat_J_g_mol := some "0.485"
      thermalConductivity_25C_W_m_K := some "30.7"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 24
      symbol := "Cr"
      name := "Chromium"
      atomicMass := some "51.9961"
      atomicRadius_pm := some "140"
      atomicVolume_cm3_per_mol := some "7.23"
      boilingPoint_K := some "2945"
      covalentRadius_pm := some "139"
      density_g_per_cm3 := some "7.18"
      electronicConfiguration := some "[Ar]3d4s1"
      evaporationHeat_kJ_mol := some "342"
      firstIonizing_kJ_mol := some "652.4"
      fusionHeat_kJ_mol := some "21"
      ionicRadius_pm := none
      latticeConstant_ang := some "2.88"
      latticeStructure := some "BCC"
      meltingPoint_K := some "2130"
      oxidationStates := [6, 3, 2, 0]
      paulingNegativity := some "1.66"
      specificHeat_J_g_mol := some "0.488"
      thermalConductivity_25C_W_m_K := some "93.9"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 25
      symbol := "Mn"
      name := "Manganese"
      atomicMass := some "54.93805"
      atomicRadius_pm := some "140"
      atomicVolume_cm3_per_mol := some "7.39"
      boilingPoint_K := some "2235"
      covalentRadius_pm := some "139"
      density_g_per_cm3 := some "7.21"
      electronicConfiguration := some "[Ar]3d4s2"
      evaporationHeat_kJ_mol := some "221"
      firstIonizing_kJ_mol := some "716.8"
      fusionHeat_kJ_mol := some "(13.4)"
      ionicRadius_pm := none
      latticeConstant_ang := some "8.89"
      latticeStructure := some "CUB"
      meltingPoint_K := some "1517"
      oxidationStates := [7, 6, 4, 3, 2, 0, -1]
      paulingNegativity := some "1.55"
      specificHeat_J_g_mol := some "0.477"
      thermalConductivity_25C_W_m_K := some "(7.8)"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 26
      symbol := "Fe"
      name := "Iron"
      atomicMass := some "55.847"
      atomicRadius_pm := some "140"
      atomicVolume_cm3_per_mol := some "7.1"
      boilingPoint_K := some "3023"
      covalentRadius_pm := some "132"
      density_g_per_cm3 := some "7.874"
      electronicConfiguration := some "[Ar]3d4s2"
      evaporationHeat_kJ_mol := some "~340"
      firstIonizing_kJ_mol := some "759.1"
      fusionHeat_kJ_mol := some "13.8"
      ionicRadius_pm := none
      latticeConstant_ang := some "2.87"
      latticeStructure := some "BCC"
      meltingPoint_K := some "1808"
      oxidationStates := [6, 3, 2, 0, -2]
      paulingNegativity := some "1.83"
      specificHeat_J_g_mol := some "0.443"
      thermalConductivity_25C_W_m_K := some "80.4"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 27
      symbol := "Co"
      name := "Cobalt"
      atomicMass := some "58.9332"
      atomicRadius_pm := some "135"
      atomicVolume_cm3_per_mol := some "6.7"
      boilingPoint_K := some "3143"
      covalentRadius_pm := some "126"
      density_g_per_cm3 := some "8.9"
      electronicConfiguration := some "[Ar]3d4s2"
      evaporationHeat_kJ_mol := some "389.1"
      firstIonizing_kJ_mol := some "758.1"
      fusionHeat_kJ_mol := some "15.48"
      ionicRadius_pm := none
      latticeConstant_ang := some "2.51"
      latticeStructure := some "HEX"
      meltingPoint_K := some "1768"
      oxidationStates := [3, 2, 0, -1]
      paulingNegativity := some "1.88"
      specificHeat_J_g_mol := some "0.456"
      thermalConductivity_25C_W_m_K := some "100"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 28
      symbol := "Ni"
      name := "Nickel"
      atomicMass := some "58.6934"
      atomicRadius_pm := some "135"
      atomicVolume_cm3_per_mol := some "6.6"
      boilingPoint_K := some "3005"
      covalentRadius_pm := some "124"
      density_g_per_cm3 := some "8.902"
      electronicConfiguration := some "[Ar]3d4s2"
      evaporationHeat_kJ_mol := some "378.6"
      firstIonizing_kJ_mol := some "736.2"
      fusionHeat_kJ_mol := some "17.61"
      ionicRadius_pm := none
      latticeConstant_ang := some "3.52"
      latticeStructure := some "FCC"
      meltingPoint_K := some "1726"
      oxidationStates := [3, 2, 0]
      paulingNegativity := some "1.91"
      specificHeat_J_g_mol := some "0.443"
      thermalConductivity_25C_W_m_K := some "90.9"
      vanDerWaalsRadius_pm := some "163"
    },
{
      atomicNumber := 29
      symbol := "Cu"
      name := "Copper"
      atomicMass := some "63.546"
      atomicRadius_pm := some "135"
      atomicVolume_cm3_per_mol := some "7.1"
      boilingPoint_K := some "2840"
      covalentRadius_pm := some "132"
      density_g_per_cm3 := some "8.96"
      electronicConfiguration := some "[Ar]3d14s1"
      evaporationHeat_kJ_mol := some "304.6"
      firstIonizing_kJ_mol := some "745"
      fusionHeat_kJ_mol := some "13.01"
      ionicRadius_pm := none
      latticeConstant_ang := some "3.61"
      latticeStructure := some "FCC"
      meltingPoint_K := some "1356.6"
      oxidationStates := [2, 1]
      paulingNegativity := some "1.9"
      specificHeat_J_g_mol := some "0.385"
      thermalConductivity_25C_W_m_K := some "401"
      vanDerWaalsRadius_pm := some "140"
    },
{
      atomicNumber := 30
      symbol := "Zn"
      name := "Zinc"
      atomicMass := some "65.39"
      atomicRadius_pm := some "135"
      atomicVolume_cm3_per_mol := some "9.2"
      boilingPoint_K := some "1180"
      covalentRadius_pm := some "122"
      density_g_per_cm3 := some "7.133"
      electronicConfiguration := some "[Ar]3d14s2"
      evaporationHeat_kJ_mol := some "114.8"
      firstIonizing_kJ_mol := some "905.8"
      fusionHeat_kJ_mol := some "7.28"
      ionicRadius_pm := none
      latticeConstant_ang := some "2.66"
      latticeStructure := some "HEX"
      meltingPoint_K := some "692.73"
      oxidationStates := [2]
      paulingNegativity := some "1.65"
      specificHeat_J_g_mol := some "0.388"
      thermalConductivity_25C_W_m_K := some "116"
      vanDerWaalsRadius_pm := some "139"
    },
{
      atomicNumber := 31
      symbol := "Ga"
      name := "Gallium"
      atomicMass := some "69.723"
      atomicRadius_pm := some "130"
      atomicVolume_cm3_per_mol := some "11.8"
      boilingPoint_K := some "2676"
      covalentRadius_pm := some "122"
      density_g_per_cm3 := some "5.91"
      electronicConfiguration := some "[Ar]3d14s24p1"
      evaporationHeat_kJ_mol := some "270.3"
      firstIonizing_kJ_mol := some "578.7"
      fusionHeat_kJ_mol := some "5.59"
      ionicRadius_pm := none
      latticeConstant_ang := some "4.51"
      latticeStructure := some "ORC"
      meltingPoint_K := some "302.93"
      oxidationStates := [3]
      paulingNegativity := some "1.81"
      specificHeat_J_g_mol := some "0.372"
      thermalConductivity_25C_W_m_K := some "28.1"
      vanDerWaalsRadius_pm := some "187"
    },
{
      atomicNumber := 32
      symbol := "Ge"
      name := "Germanium"
      atomicMass := some "72.61"
      atomicRadius_pm := some "125"
      atomicVolume_cm3_per_mol := some "13.6"
      boilingPoint_K := some "3103"
      covalentRadius_pm := some "120"
      density_g_per_cm3 := some "5.323"
      electronicConfiguration := some "[Ar]3d14s24p2"
      evaporationHeat_kJ_mol := some "328"
      firstIonizing_kJ_mol := some "760"
      fusionHeat_kJ_mol := some "36.8"
      ionicRadius_pm := none
      latticeConstant_ang := some "5.66"
      latticeStructure := some "DIA"
      meltingPoint_K := some "1210.6"
      oxidationStates := [4]
      paulingNegativity := some "2.01"
      specificHeat_J_g_mol := some "0.322"
      thermalConductivity_25C_W_m_K := some "60.2"
      vanDerWaalsRadius_pm := some "211"
    },
{
      atomicNumber := 33
      symbol := "As"
      name := "Arsenic"
      atomicMass := some "74.92159"
      atomicRadius_pm := some "115"
      atomicVolume_cm3_per_mol := some "13.1"
      boilingPoint_K := some "876"
      covalentRadius_pm := some "119"
      density_g_per_cm3 := some "5.73 (grey arsenic)"
      electronicConfiguration := some "[Ar]3d14s24p3"
      evaporationHeat_kJ_mol := some "32.4"
      firstIonizing_kJ_mol := some "946.2"
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := some "4.13"
      latticeStructure := some "RHL"
      meltingPoint_K := some "1090"
      oxidationStates := [5, 3, -2]
      paulingNegativity := some "2.18"
      specificHeat_J_g_mol := some "0.328"
      thermalConductivity_25C_W_m_K := some "(50.2)"
      vanDerWaalsRadius_pm := some "185"
    },
{
      atomicNumber := 34
      symbol := "Se"
      name := "Selenium"
      atomicMass := some "78.96"
      atomicRadius_pm := some "115"
      atomicVolume_cm3_per_mol := some "16.5"
      boilingPoint_K := some "958.1"
      covalentRadius_pm := some "120"
      density_g_per_cm3 := some "4.79"
      electronicConfiguration := some "[Ar]3d14s24p"
      evaporationHeat_kJ_mol := some "59.7"
      firstIonizing_kJ_mol := some "940.4"
      fusionHeat_kJ_mol := some "5.23"
      ionicRadius_pm := none
      latticeConstant_ang := some "4.36"
      latticeStructure := some "HEX"
      meltingPoint_K := some "490"
      oxidationStates := [6, 4, -2]
      paulingNegativity := some "2.55"
      specificHeat_J_g_mol := some "0.321 (Se-Se)"
      thermalConductivity_25C_W_m_K := some "0.52"
      vanDerWaalsRadius_pm := some "190"
    },
{
      atomicNumber := 35
      symbol := "Br"
      name := "Bromine"
      atomicMass := some "79.904"
      atomicRadius_pm := some "115"
      atomicVolume_cm3_per_mol := some "23.5"
      boilingPoint_K := some "331.9"
      covalentRadius_pm := some "120"
      density_g_per_cm3 := some "3.12"
      electronicConfiguration := some "[Ar]3d14s24p"
      evaporationHeat_kJ_mol := some "29.56 (Br-Br)"
      firstIonizing_kJ_mol := some "1142"
      fusionHeat_kJ_mol := some "10.57 (Br-Br)"
      ionicRadius_pm := none
      latticeConstant_ang := some "6.67"
      latticeStructure := some "ORC"
      meltingPoint_K := some "265.9"
      oxidationStates := [7, 5, 3, 1, -1]
      paulingNegativity := some "2.96"
      specificHeat_J_g_mol := some "0.473 (Br-Br)"
      thermalConductivity_25C_W_m_K := some "0.005"
      vanDerWaalsRadius_pm := some "185"
    },
{
      atomicNumber := 36
      symbol := "Kr"
      name := "Krypton"
      atomicMass := some "83.8"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := some "32.2"
      boilingPoint_K := some "120.85"
      covalentRadius_pm := some "116"
      density_g_per_cm3 := some "2.155 (@ -153degC)"
      electronicConfiguration := some "[Ar]3d14s24p"
      evaporationHeat_kJ_mol := some "9.05"
      firstIonizing_kJ_mol := some "1350"
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := some "5.72"
      latticeStructure := some "FCC"
      meltingPoint_K := some "116.6"
      oxidationStates := [2]
      paulingNegativity := some "0"
      specificHeat_J_g_mol := some "0.247"
      thermalConductivity_25C_W_m_K := some "0.0095"
      vanDerWaalsRadius_pm := some "202"
    },
{
      atomicNumber := 37
      symbol := "Rb"
      name := "Rubidium"
      atomicMass := some "85.4678"
      atomicRadius_pm := some "235"
      atomicVolume_cm3_per_mol := some "55.9"
      boilingPoint_K := some "961"
      covalentRadius_pm := some "220"
      density_g_per_cm3 := some "1.532"
      electronicConfiguration := some "[Kr]5s1"
      evaporationHeat_kJ_mol := some "75.8"
      firstIonizing_kJ_mol := some "402.8"
      fusionHeat_kJ_mol := some "2.2"
      ionicRadius_pm := none
      latticeConstant_ang := some "5.59"
      latticeStructure := some "BCC"
      meltingPoint_K := some "312.2"
      oxidationStates := [1]
      paulingNegativity := some "0.82"
      specificHeat_J_g_mol := some "0.36"
      thermalConductivity_25C_W_m_K := some "58.2"
      vanDerWaalsRadius_pm := some "303"
    },
{
      atomicNumber := 38
      symbol := "Sr"
      name := "Strontium"
      atomicMass := some "87.62"
      atomicRadius_pm := some "200"
      atomicVolume_cm3_per_mol := some "33.7"
      boilingPoint_K := some "1657"
      covalentRadius_pm := some "195"
      density_g_per_cm3 := some "2.54"
      electronicConfiguration := some "[Kr]5s2"
      evaporationHeat_kJ_mol := some "144"
      firstIonizing_kJ_mol := some "549"
      fusionHeat_kJ_mol := some "9.2"
      ionicRadius_pm := none
      latticeConstant_ang := some "6.08"
      latticeStructure := some "FCC"
      meltingPoint_K := some "1042"
      oxidationStates := [2]
      paulingNegativity := some "0.95"
      specificHeat_J_g_mol := some "0.301"
      thermalConductivity_25C_W_m_K := some "(35.4)"
      vanDerWaalsRadius_pm := some "249"
    },
{
      atomicNumber := 39
      symbol := "Y"
      name := "Yttrium"
      atomicMass := some "88.90585"
      atomicRadius_pm := some "180"
      atomicVolume_cm3_per_mol := some "19.8"
      boilingPoint_K := some "3611"
      covalentRadius_pm := some "190"
      density_g_per_cm3 := some "4.47"
      electronicConfiguration := some "[Kr]4d15s2"
      evaporationHeat_kJ_mol := some "367"
      firstIonizing_kJ_mol := some "615.4"
      fusionHeat_kJ_mol := some "11.5"
      ionicRadius_pm := none
      latticeConstant_ang := some "3.65"
      latticeStructure := some "HEX"
      meltingPoint_K := some "1795"
      oxidationStates := [3]
      paulingNegativity := some "1.22"
      specificHeat_J_g_mol := some "0.284"
      thermalConductivity_25C_W_m_K := some "(17.2)"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 40
      symbol := "Zr"
      name := "Zirconium"
      atomicMass := some "91.224"
      atomicRadius_pm := some "155"
      atomicVolume_cm3_per_mol := some "14.1"
      boilingPoint_K := some "4650"
      covalentRadius_pm := some "175"
      density_g_per_cm3 := some "6.506"
      electronicConfiguration := some "[Kr]4d25s2"
      evaporationHeat_kJ_mol := some "567"
      firstIonizing_kJ_mol := some "659.7"
      fusionHeat_kJ_mol := some "19.2"
      ionicRadius_pm := none
      latticeConstant_ang := some "3.23"
      latticeStructure := some "HEX"
      meltingPoint_K := some "2125"
      oxidationStates := [4]
      paulingNegativity := some "1.33"
      specificHeat_J_g_mol := some "0.281"
      thermalConductivity_25C_W_m_K := some "22.7"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 41
      symbol := "Nb"
      name := "Niobium"
      atomicMass := some "92.90638"
      atomicRadius_pm := some "145"
      atomicVolume_cm3_per_mol := some "10.8"
      boilingPoint_K := some "5015"
      covalentRadius_pm := some "164"
      density_g_per_cm3 := some "8.57"
      electronicConfiguration := some "[Kr]4d5s1"
      evaporationHeat_kJ_mol := some "680"
      firstIonizing_kJ_mol := some "663.6"
      fusionHeat_kJ_mol := some "26.8"
      ionicRadius_pm := none
      latticeConstant_ang := some "3.3"
      latticeStructure := some "BCC"
      meltingPoint_K := some "2741"
      oxidationStates := [5, 3]
      paulingNegativity := some "1.6"
      specificHeat_J_g_mol := some "0.268"
      thermalConductivity_25C_W_m_K := some "53.7"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 42
      symbol := "Mo"
      name := "Molybdenum"
      atomicMass := some "95.94"
      atomicRadius_pm := some "145"
      atomicVolume_cm3_per_mol := some "9.4"
      boilingPoint_K := some "4885"
      covalentRadius_pm := some "154"
      density_g_per_cm3 := some "10.22"
      electronicConfiguration := some "[Kr]4d5s1"
      evaporationHeat_kJ_mol := some "~590"
      firstIonizing_kJ_mol := some "684.8"
      fusionHeat_kJ_mol := some "28"
      ionicRadius_pm := none
      latticeConstant_ang := some "3.15"
      latticeStructure := some "BCC"
      meltingPoint_K := some "2890"
      oxidationStates := [6, 5, 4, 3, 2, 0]
      paulingNegativity := some "2.16"
      specificHeat_J_g_mol := some "0.251"
      thermalConductivity_25C_W_m_K := some "(138)"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 43
      symbol := "Tc"
      name := "Technetium"
      atomicMass := some "97.9072"
      atomicRadius_pm := some "135"
      atomicVolume_cm3_per_mol := some "8.5"
      boilingPoint_K := some "5150"
      covalentRadius_pm := some "147"
      density_g_per_cm3 := some "11.5"
      electronicConfiguration := some "[Kr]4d5s1"
      evaporationHeat_kJ_mol := some "585"
      firstIonizing_kJ_mol := some "702.2"
      fusionHeat_kJ_mol := some "23.8"
      ionicRadius_pm := none
      latticeConstant_ang := some "2.74"
      latticeStructure := some "HEX"
      meltingPoint_K := some "2445"
      oxidationStates := [7]
      paulingNegativity := some "1.9"
      specificHeat_J_g_mol := some "0.243"
      thermalConductivity_25C_W_m_K := some "50.6"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 44
      symbol := "Ru"
      name := "Ruthenium"
      atomicMass := some "101.07"
      atomicRadius_pm := some "130"
      atomicVolume_cm3_per_mol := some "8.3"
      boilingPoint_K := some "4173"
      covalentRadius_pm := some "146"
      density_g_per_cm3 := some "12.41"
      electronicConfiguration := some "[Kr]4d5s1"
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := some "710.3"
      fusionHeat_kJ_mol := some "(25.5)"
      ionicRadius_pm := none
      latticeConstant_ang := some "2.7"
      latticeStructure := some "HEX"
      meltingPoint_K := some "2583"
      oxidationStates := [8, 6, 4, 3, 2, 0, -2]
      paulingNegativity := some "2.2"
      specificHeat_J_g_mol := some "0.238"
      thermalConductivity_25C_W_m_K := some "117"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 45
      symbol := "Rh"
      name := "Rhodium"
      atomicMass := some "102.9055"
      atomicRadius_pm := some "135"
      atomicVolume_cm3_per_mol := some "8.3"
      boilingPoint_K := some "4000"
      covalentRadius_pm := some "142"
      density_g_per_cm3 := some "12.41"
      electronicConfiguration := some "[Kr]4d5s1"
      evaporationHeat_kJ_mol := some "494"
      firstIonizing_kJ_mol := some "719.5"
      fusionHeat_kJ_mol := some "21.8"
      ionicRadius_pm := none
      latticeConstant_ang := some "3.8"
      latticeStructure := some "FCC"
      meltingPoint_K := some "2239"
      oxidationStates := [5, 4, 3, 2, 1, 0]
      paulingNegativity := some "2.28"
      specificHeat_J_g_mol := some "0.244"
      thermalConductivity_25C_W_m_K := some "150"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 46
      symbol := "Pd"
      name := "Palladium"
      atomicMass := some "106.42"
      atomicRadius_pm := some "140"
      atomicVolume_cm3_per_mol := some "8.9"
      boilingPoint_K := some "3413"
      covalentRadius_pm := some "139"
      density_g_per_cm3 := some "12.02"
      electronicConfiguration := some "[Kr]4d5s"
      evaporationHeat_kJ_mol := some "372.4"
      firstIonizing_kJ_mol := some "803.5"
      fusionHeat_kJ_mol := some "17.24"
      ionicRadius_pm := none
      latticeConstant_ang := some "3.89"
      latticeStructure := some "FCC"
      meltingPoint_K := some "1825"
      oxidationStates := [4, 2, 0]
      paulingNegativity := some "2.2"
      specificHeat_J_g_mol := some "0.244"
      thermalConductivity_25C_W_m_K := some "71.8"
      vanDerWaalsRadius_pm := some "163"
    },
{
      atomicNumber := 47
      symbol := "Ag"
      name := "Silver"
      atomicMass := some "107.8682"
      atomicRadius_pm := some "160"
      atomicVolume_cm3_per_mol := some "10.3"
      boilingPoint_K := some "2485"
      covalentRadius_pm := some "145"
      density_g_per_cm3 := some "10.5"
      electronicConfiguration := some "[Kr]4d5s1"
      evaporationHeat_kJ_mol := some "254.1"
      firstIonizing_kJ_mol := some "730.5"
      fusionHeat_kJ_mol := some "11.95"
      ionicRadius_pm := none
      latticeConstant_ang := some "4.09"
      latticeStructure := some "FCC"
      meltingPoint_K := some "1235.1"
      oxidationStates := [2, 1]
      paulingNegativity := some "1.93"
      specificHeat_J_g_mol := some "0.237"
      thermalConductivity_25C_W_m_K := some "429"
      vanDerWaalsRadius_pm := some "172"
    },
{
      atomicNumber := 48
      symbol := "Cd"
      name := "Cadmium"
      atomicMass := some "112.411"
      atomicRadius_pm := some "155"
      atomicVolume_cm3_per_mol := some "13.1"
      boilingPoint_K := some "1038"
      covalentRadius_pm := some "144"
      density_g_per_cm3 := some "8.65"
      electronicConfiguration := some "[Kr]4d5s2"
      evaporationHeat_kJ_mol := some "59.1"
      firstIonizing_kJ_mol := some "867.2"
      fusionHeat_kJ_mol := some "6.11"
      ionicRadius_pm := none
      latticeConstant_ang := some "2.98"
      latticeStructure := some "HEX"
      meltingPoint_K := some "594.1"
      oxidationStates := [2]
      paulingNegativity := some "1.69"
      specificHeat_J_g_mol := some "0.232"
      thermalConductivity_25C_W_m_K := some "96.9"
      vanDerWaalsRadius_pm := some "158"
    },
{
      atomicNumber := 49
      symbol := "In"
      name := "Indium"
      atomicMass := some "114.818"
      atomicRadius_pm := some "155"
      atomicVolume_cm3_per_mol := some "15.7"
      boilingPoint_K := some "2353"
      covalentRadius_pm := some "142"
      density_g_per_cm3 := some "7.31"
      electronicConfiguration := some "[Kr]4d5s25p1"
      evaporationHeat_kJ_mol := some "225.1"
      firstIonizing_kJ_mol := some "558"
      fusionHeat_kJ_mol := some "3.24"
      ionicRadius_pm := none
      latticeConstant_ang := some "4.59"
      latticeStructure := some "TET"
      meltingPoint_K := some "429.32"
      oxidationStates := [3]
      paulingNegativity := some "1.78"
      specificHeat_J_g_mol := some "0.234"
      thermalConductivity_25C_W_m_K := some "81.8"
      vanDerWaalsRadius_pm := some "193"
    },
{
      atomicNumber := 50
      symbol := "Sn"
      name := "Tin"
      atomicMass := some "118.71"
      atomicRadius_pm := some "145"
      atomicVolume_cm3_per_mol := some "16.3"
      boilingPoint_K := some "2543"
      covalentRadius_pm := some "139"
      density_g_per_cm3 := some "7.31"
      electronicConfiguration := some "[Kr]4d5s25p2"
      evaporationHeat_kJ_mol := some "296"
      firstIonizing_kJ_mol := some "708.2"
      fusionHeat_kJ_mol := some "7.07"
      ionicRadius_pm := none
      latticeConstant_ang := some "5.82"
      latticeStructure := some "TET"
      meltingPoint_K := some "505.1"
      oxidationStates := [4, 2]
      paulingNegativity := some "1.96"
      specificHeat_J_g_mol := some "0.222"
      thermalConductivity_25C_W_m_K := some "66.8"
      vanDerWaalsRadius_pm := some "217"
    },
{
      atomicNumber := 51
      symbol := "Sb"
      name := "Antimony"
      atomicMass := some "121.76"
      atomicRadius_pm := some "145"
      atomicVolume_cm3_per_mol := some "18.4"
      boilingPoint_K := some "1908"
      covalentRadius_pm := some "139"
      density_g_per_cm3 := some "6.691"
      electronicConfiguration := some "[Kr]4d5s25p3"
      evaporationHeat_kJ_mol := some "195.2"
      firstIonizing_kJ_mol := some "833.3"
      fusionHeat_kJ_mol := some "20.08"
      ionicRadius_pm := none
      latticeConstant_ang := some "4.51"
      latticeStructure := some "RHL"
      meltingPoint_K := some "903.9"
      oxidationStates := [5, 3, -2]
      paulingNegativity := some "2.05"
      specificHeat_J_g_mol := some "0.205"
      thermalConductivity_25C_W_m_K := some "24.43"
      vanDerWaalsRadius_pm := some "206"
    },
{
      atomicNumber := 52
      symbol := "Te"
      name := "Tellurium"
      atomicMass := some "127.6"
      atomicRadius_pm := some "140"
      atomicVolume_cm3_per_mol := some "20.5"
      boilingPoint_K := some "1263"
      covalentRadius_pm := some "138"
      density_g_per_cm3 := some "6.24"
      electronicConfiguration := some "[Kr]4d5s25p"
      evaporationHeat_kJ_mol := some "49.8"
      firstIonizing_kJ_mol := some "869"
      fusionHeat_kJ_mol := some "17.91"
      ionicRadius_pm := none
      latticeConstant_ang := some "4.45"
      latticeStructure := some "HEX"
      meltingPoint_K := some "722.7"
      oxidationStates := [6, 4, 2]
      paulingNegativity := some "2.1"
      specificHeat_J_g_mol := some "0.201"
      thermalConductivity_25C_W_m_K := some "14.3"
      vanDerWaalsRadius_pm := some "206"
    },
{
      atomicNumber := 53
      symbol := "I"
      name := "Iodine"
      atomicMass := some "126.90447"
      atomicRadius_pm := some "140"
      atomicVolume_cm3_per_mol := some "25.7"
      boilingPoint_K := some "457.5"
      covalentRadius_pm := some "139"
      density_g_per_cm3 := some "4.93"
      electronicConfiguration := some "[Kr]4d5s25p"
      evaporationHeat_kJ_mol := some "41.95 (I-I)"
      firstIonizing_kJ_mol := some "1008.3"
      fusionHeat_kJ_mol := some "15.52 (I-I)"
      ionicRadius_pm := none
      latticeConstant_ang := some "7.72"
      latticeStructure := some "ORC"
      meltingPoint_K := some "386.7"
      oxidationStates := [7, 5, 1, -1]
      paulingNegativity := some "2.66"
      specificHeat_J_g_mol := some "0.427 (I-I)"
      thermalConductivity_25C_W_m_K := some "(0.45)"
      vanDerWaalsRadius_pm := some "198"
    },
{
      atomicNumber := 54
      symbol := "Xe"
      name := "Xenon"
      atomicMass := some "131.29"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := some "42.9"
      boilingPoint_K := some "166.1"
      covalentRadius_pm := some "140"
      density_g_per_cm3 := some "3.52 (@ -109degC)"
      electronicConfiguration := some "[Kr]4d5s25p"
      evaporationHeat_kJ_mol := some "12.65"
      firstIonizing_kJ_mol := some "1170"
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := some "6.2"
      latticeStructure := some "FCC"
      meltingPoint_K := some "161.3"
      oxidationStates := [7]
      paulingNegativity := some "0"
      specificHeat_J_g_mol := some "0.158"
      thermalConductivity_25C_W_m_K := some "0.0057"
      vanDerWaalsRadius_pm := some "216"
    },
{
      atomicNumber := 55
      symbol := "Cs"
      name := "Caesium"
      atomicMass := some "132.90543"
      atomicRadius_pm := some "260"
      atomicVolume_cm3_per_mol := some "70"
      boilingPoint_K := some "951.6"
      covalentRadius_pm := some "244"
      density_g_per_cm3 := some "1.873"
      electronicConfiguration := some "[Xe]6s1"
      evaporationHeat_kJ_mol := some "68.3"
      firstIonizing_kJ_mol := some "375.5"
      fusionHeat_kJ_mol := some "2.09"
      ionicRadius_pm := none
      latticeConstant_ang := some "6.05"
      latticeStructure := some "BCC"
      meltingPoint_K := some "301.6"
      oxidationStates := [1]
      paulingNegativity := some "0.79"
      specificHeat_J_g_mol := some "0.241"
      thermalConductivity_25C_W_m_K := some "35.9"
      vanDerWaalsRadius_pm := some "343"
    },
{
      atomicNumber := 56
      symbol := "Ba"
      name := "Barium"
      atomicMass := some "137.327"
      atomicRadius_pm := some "215"
      atomicVolume_cm3_per_mol := some "39"
      boilingPoint_K := some "1910"
      covalentRadius_pm := some "215"
      density_g_per_cm3 := some "3.5"
      electronicConfiguration := some "[Xe]6s2"
      evaporationHeat_kJ_mol := some "142"
      firstIonizing_kJ_mol := some "502.5"
      fusionHeat_kJ_mol := some "7.66"
      ionicRadius_pm := none
      latticeConstant_ang := some "5.02"
      latticeStructure := some "BCC"
      meltingPoint_K := some "1002"
      oxidationStates := [2]
      paulingNegativity := some "0.89"
      specificHeat_J_g_mol := some "0.192"
      thermalConductivity_25C_W_m_K := some "(18.4)"
      vanDerWaalsRadius_pm := some "268"
    },
{
      atomicNumber := 57
      symbol := "La"
      name := "Lanthanum"
      atomicMass := some "138.9055"
      atomicRadius_pm := some "195"
      atomicVolume_cm3_per_mol := some "22.5"
      boilingPoint_K := some "3730"
      covalentRadius_pm := some "207"
      density_g_per_cm3 := some "6.15"
      electronicConfiguration := some "[Xe]6d16s2"
      evaporationHeat_kJ_mol := some "402"
      firstIonizing_kJ_mol := some "541.1"
      fusionHeat_kJ_mol := some "8.5"
      ionicRadius_pm := none
      latticeConstant_ang := some "3.75"
      latticeStructure := some "HEX"
      meltingPoint_K := some "1194"
      oxidationStates := [3]
      paulingNegativity := some "1.1"
      specificHeat_J_g_mol := some "0.197"
      thermalConductivity_25C_W_m_K := some "13.4"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 58
      symbol := "Ce"
      name := "Cerium"
      atomicMass := some "140.115"
      atomicRadius_pm := some "185"
      atomicVolume_cm3_per_mol := some "21"
      boilingPoint_K := some "3699"
      covalentRadius_pm := some "204"
      density_g_per_cm3 := some "6.757"
      electronicConfiguration := some "[Xe]4f15d16s2"
      evaporationHeat_kJ_mol := some "398"
      firstIonizing_kJ_mol := some "540.1"
      fusionHeat_kJ_mol := some "5.2"
      ionicRadius_pm := none
      latticeConstant_ang := some "5.16"
      latticeStructure := some "FCC"
      meltingPoint_K := some "1072"
      oxidationStates := [4, 3]
      paulingNegativity := some "1.12"
      specificHeat_J_g_mol := some "0.205"
      thermalConductivity_25C_W_m_K := some "11.3"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 59
      symbol := "Pr"
      name := "Praseodymium"
      atomicMass := some "140.90765"
      atomicRadius_pm := some "185"
      atomicVolume_cm3_per_mol := some "20.8"
      boilingPoint_K := some "3785"
      covalentRadius_pm := some "203"
      density_g_per_cm3 := some "6.773"
      electronicConfiguration := some "[Xe]4f35d6s2"
      evaporationHeat_kJ_mol := some "331"
      firstIonizing_kJ_mol := some "526.6"
      fusionHeat_kJ_mol := some "11.3"
      ionicRadius_pm := none
      latticeConstant_ang := some "3.67"
      latticeStructure := some "HEX"
      meltingPoint_K := some "1204"
      oxidationStates := [4, 3]
      paulingNegativity := some "1.13"
      specificHeat_J_g_mol := some "0.192"
      thermalConductivity_25C_W_m_K := some "12.5"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 60
      symbol := "Nd"
      name := "Neodymium"
      atomicMass := some "144.24"
      atomicRadius_pm := some "185"
      atomicVolume_cm3_per_mol := some "20.6"
      boilingPoint_K := some "3341"
      covalentRadius_pm := some "201"
      density_g_per_cm3 := some "7.007"
      electronicConfiguration := some "[Xe]4f5d6s2"
      evaporationHeat_kJ_mol := some "289"
      firstIonizing_kJ_mol := some "531.5"
      fusionHeat_kJ_mol := some "7.1"
      ionicRadius_pm := none
      latticeConstant_ang := some "3.66"
      latticeStructure := some "HEX"
      meltingPoint_K := some "1294"
      oxidationStates := [3]
      paulingNegativity := some "1.14"
      specificHeat_J_g_mol := some "0.205"
      thermalConductivity_25C_W_m_K := some "(16.5)"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 61
      symbol := "Pm"
      name := "Promethium"
      atomicMass := some "144.9127"
      atomicRadius_pm := some "185"
      atomicVolume_cm3_per_mol := none
      boilingPoint_K := some "3000"
      covalentRadius_pm := some "199"
      density_g_per_cm3 := some "7.2"
      electronicConfiguration := some "[Xe]4f5d6s2"
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := some "536"
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := none
      meltingPoint_K := some "1441"
      oxidationStates := [3]
      paulingNegativity := some "0"
      specificHeat_J_g_mol := some "0.185"
      thermalConductivity_25C_W_m_K := some "17.9"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 62
      symbol := "Sm"
      name := "Samarium"
      atomicMass := some "150.36"
      atomicRadius_pm := some "185"
      atomicVolume_cm3_per_mol := some "19.9"
      boilingPoint_K := some "2064"
      covalentRadius_pm := some "198"
      density_g_per_cm3 := some "7.52"
      electronicConfiguration := some "[Xe]4f5d6s2"
      evaporationHeat_kJ_mol := some "165"
      firstIonizing_kJ_mol := some "540.1"
      fusionHeat_kJ_mol := some "8.9"
      ionicRadius_pm := none
      latticeConstant_ang := some "9"
      latticeStructure := some "RHL"
      meltingPoint_K := some "1350"
      oxidationStates := [3, 2]
      paulingNegativity := some "1.17"
      specificHeat_J_g_mol := some "0.18"
      thermalConductivity_25C_W_m_K := some "(13.3)"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 63
      symbol := "Eu"
      name := "Europium"
      atomicMass := some "151.965"
      atomicRadius_pm := some "185"
      atomicVolume_cm3_per_mol := some "28.9"
      boilingPoint_K := some "1870"
      covalentRadius_pm := some "198"
      density_g_per_cm3 := some "5.243"
      electronicConfiguration := some "[Xe]4f5d6s2"
      evaporationHeat_kJ_mol := some "176"
      firstIonizing_kJ_mol := some "546.9"
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := some "4.61"
      latticeStructure := some "BCC"
      meltingPoint_K := some "1095"
      oxidationStates := [3, 2]
      paulingNegativity := some "0"
      specificHeat_J_g_mol := some "0.176"
      thermalConductivity_25C_W_m_K := some "13.9"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 64
      symbol := "Gd"
      name := "Gadolinium"
      atomicMass := some "157.25"
      atomicRadius_pm := some "180"
      atomicVolume_cm3_per_mol := some "19.9"
      boilingPoint_K := some "3539"
      covalentRadius_pm := some "196"
      density_g_per_cm3 := some "7.9"
      electronicConfiguration := some "[Xe]4f5d16s2"
      evaporationHeat_kJ_mol := some "398"
      firstIonizing_kJ_mol := some "594.2"
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := some "3.64"
      latticeStructure := some "HEX"
      meltingPoint_K := some "1586"
      oxidationStates := [3]
      paulingNegativity := some "1.2"
      specificHeat_J_g_mol := some "0.23"
      thermalConductivity_25C_W_m_K := some "(10.5)"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 65
      symbol := "Tb"
      name := "Terbium"
      atomicMass := some "158.92534"
      atomicRadius_pm := some "175"
      atomicVolume_cm3_per_mol := some "19.2"
      boilingPoint_K := some "3296"
      covalentRadius_pm := some "194"
      density_g_per_cm3 := some "8.229"
      electronicConfiguration := some "[Xe]4f5d6s2"
      evaporationHeat_kJ_mol := some "389"
      firstIonizing_kJ_mol := some "569"
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := some "3.6"
      latticeStructure := some "HEX"
      meltingPoint_K := some "1629"
      oxidationStates := [4, 3]
      paulingNegativity := some "1.2"
      specificHeat_J_g_mol := some "0.183"
      thermalConductivity_25C_W_m_K := some "11.1"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 66
      symbol := "Dy"
      name := "Dysprosium"
      atomicMass := some "162.5"
      atomicRadius_pm := some "175"
      atomicVolume_cm3_per_mol := some "19"
      boilingPoint_K := some "2835"
      covalentRadius_pm := some "192"
      density_g_per_cm3 := some "8.55"
      electronicConfiguration := some "[Xe]4f5d6s2"
      evaporationHeat_kJ_mol := some "291"
      firstIonizing_kJ_mol := some "567"
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := some "3.59"
      latticeStructure := some "HEX"
      meltingPoint_K := some "1685"
      oxidationStates := [3]
      paulingNegativity := none
      specificHeat_J_g_mol := some "0.173"
      thermalConductivity_25C_W_m_K := some "10.7"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 67
      symbol := "Ho"
      name := "Holmium"
      atomicMass := some "164.93031"
      atomicRadius_pm := some "175"
      atomicVolume_cm3_per_mol := some "18.7"
      boilingPoint_K := some "2968"
      covalentRadius_pm := some "192"
      density_g_per_cm3 := some "8.795"
      electronicConfiguration := some "[Xe]4f115d6s2"
      evaporationHeat_kJ_mol := some "301"
      firstIonizing_kJ_mol := some "574"
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := some "3.58"
      latticeStructure := some "HEX"
      meltingPoint_K := some "1747"
      oxidationStates := [3]
      paulingNegativity := some "1.23"
      specificHeat_J_g_mol := some "0.164"
      thermalConductivity_25C_W_m_K := some "(16.2)"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 68
      symbol := "Er"
      name := "Erbium"
      atomicMass := some "167.26"
      atomicRadius_pm := some "175"
      atomicVolume_cm3_per_mol := some "18.4"
      boilingPoint_K := some "3136"
      covalentRadius_pm := some "189"
      density_g_per_cm3 := some "9.06"
      electronicConfiguration := some "[Xe]4f125d6s2"
      evaporationHeat_kJ_mol := some "317"
      firstIonizing_kJ_mol := some "581"
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := some "3.56"
      latticeStructure := some "HEX"
      meltingPoint_K := some "1802"
      oxidationStates := [3]
      paulingNegativity := some "1.24"
      specificHeat_J_g_mol := some "0.168"
      thermalConductivity_25C_W_m_K := some "(14.5)"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 69
      symbol := "Tm"
      name := "Thulium"
      atomicMass := some "168.9342"
      atomicRadius_pm := some "175"
      atomicVolume_cm3_per_mol := some "18.1"
      boilingPoint_K := some "2220"
      covalentRadius_pm := some "190"
      density_g_per_cm3 := some "9.321"
      electronicConfiguration := some "[Xe]4f135d6s2"
      evaporationHeat_kJ_mol := some "232"
      firstIonizing_kJ_mol := some "589"
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := some "3.54"
      latticeStructure := some "HEX"
      meltingPoint_K := some "1818"
      oxidationStates := [3, 2]
      paulingNegativity := some "1.25"
      specificHeat_J_g_mol := some "0.16"
      thermalConductivity_25C_W_m_K := some "(16.9)"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 70
      symbol := "Yb"
      name := "Ytterbium"
      atomicMass := some "173.04"
      atomicRadius_pm := some "175"
      atomicVolume_cm3_per_mol := some "24.8"
      boilingPoint_K := some "1466"
      covalentRadius_pm := some "187"
      density_g_per_cm3 := some "6.9654"
      electronicConfiguration := some "[Xe]4f15d16s2"
      evaporationHeat_kJ_mol := some "159"
      firstIonizing_kJ_mol := some "603"
      fusionHeat_kJ_mol := some "3.35"
      ionicRadius_pm := none
      latticeConstant_ang := some "5.49"
      latticeStructure := some "FCC"
      meltingPoint_K := some "1097"
      oxidationStates := [3, 2]
      paulingNegativity := some "1.1"
      specificHeat_J_g_mol := some "0.145"
      thermalConductivity_25C_W_m_K := some "(34.9)"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 71
      symbol := "Lu"
      name := "Lutetium"
      atomicMass := some "174.967"
      atomicRadius_pm := some "175"
      atomicVolume_cm3_per_mol := some "17.8"
      boilingPoint_K := some "3668"
      covalentRadius_pm := some "187"
      density_g_per_cm3 := some "9.8404"
      electronicConfiguration := some "[Xe]4f15d16s2"
      evaporationHeat_kJ_mol := some "414"
      firstIonizing_kJ_mol := some "513"
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := some "3.51"
      latticeStructure := some "HEX"
      meltingPoint_K := some "1936"
      oxidationStates := [3]
      paulingNegativity := some "1.27"
      specificHeat_J_g_mol := some "0.155"
      thermalConductivity_25C_W_m_K := some "(16.4)"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 72
      symbol := "Hf"
      name := "Hafnium"
      atomicMass := some "178.49"
      atomicRadius_pm := some "155"
      atomicVolume_cm3_per_mol := some "13.6"
      boilingPoint_K := some "5470"
      covalentRadius_pm := some "175"
      density_g_per_cm3 := some "13.31"
      electronicConfiguration := some "[Xe]4f15d26s2"
      evaporationHeat_kJ_mol := some "575"
      firstIonizing_kJ_mol := some "575.2"
      fusionHeat_kJ_mol := some "(25.1)"
      ionicRadius_pm := none
      latticeConstant_ang := some "3.2"
      latticeStructure := some "HEX"
      meltingPoint_K := some "2503"
      oxidationStates := [4]
      paulingNegativity := some "1.3"
      specificHeat_J_g_mol := some "0.146"
      thermalConductivity_25C_W_m_K := some "23"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 73
      symbol := "Ta"
      name := "Tantalum"
      atomicMass := some "180.9479"
      atomicRadius_pm := some "145"
      atomicVolume_cm3_per_mol := some "10.9"
      boilingPoint_K := some "5698"
      covalentRadius_pm := some "170"
      density_g_per_cm3 := some "16.654"
      electronicConfiguration := some "[Xe]4f15d36s2"
      evaporationHeat_kJ_mol := some "758"
      firstIonizing_kJ_mol := some "760.1"
      fusionHeat_kJ_mol := some "24.7"
      ionicRadius_pm := none
      latticeConstant_ang := some "3.31"
      latticeStructure := some "BCC"
      meltingPoint_K := some "3269"
      oxidationStates := [5]
      paulingNegativity := some "1.5"
      specificHeat_J_g_mol := some "0.14"
      thermalConductivity_25C_W_m_K := some "57.5"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 74
      symbol := "W"
      name := "Tungsten"
      atomicMass := some "183.84"
      atomicRadius_pm := some "135"
      atomicVolume_cm3_per_mol := some "9.53"
      boilingPoint_K := some "5930"
      covalentRadius_pm := some "162"
      density_g_per_cm3 := some "19.3"
      electronicConfiguration := some "[Xe]4f15d6s2"
      evaporationHeat_kJ_mol := some "824"
      firstIonizing_kJ_mol := some "769.7"
      fusionHeat_kJ_mol := some "(35)"
      ionicRadius_pm := none
      latticeConstant_ang := some "3.16"
      latticeStructure := some "BCC"
      meltingPoint_K := some "3680"
      oxidationStates := [6, 5, 4, 3, 2, 0]
      paulingNegativity := some "1.7"
      specificHeat_J_g_mol := some "0.133"
      thermalConductivity_25C_W_m_K := some "173"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 75
      symbol := "Re"
      name := "Rhenium"
      atomicMass := some "186.207"
      atomicRadius_pm := some "135"
      atomicVolume_cm3_per_mol := some "8.85"
      boilingPoint_K := some "5900"
      covalentRadius_pm := some "151"
      density_g_per_cm3 := some "21.02"
      electronicConfiguration := some "[Xe]4f15d6s2"
      evaporationHeat_kJ_mol := some "704"
      firstIonizing_kJ_mol := some "759.1"
      fusionHeat_kJ_mol := some "34"
      ionicRadius_pm := none
      latticeConstant_ang := some "2.76"
      latticeStructure := some "HEX"
      meltingPoint_K := some "3453"
      oxidationStates := [5, 4, 3, 2, -1]
      paulingNegativity := some "1.9"
      specificHeat_J_g_mol := some "0.138"
      thermalConductivity_25C_W_m_K := some "48"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 76
      symbol := "Os"
      name := "Osmium"
      atomicMass := some "190.23"
      atomicRadius_pm := some "130"
      atomicVolume_cm3_per_mol := some "8.43"
      boilingPoint_K := some "5300"
      covalentRadius_pm := some "144"
      density_g_per_cm3 := some "22.57"
      electronicConfiguration := some "[Xe]4f15d6s2"
      evaporationHeat_kJ_mol := some "738"
      firstIonizing_kJ_mol := some "819.8"
      fusionHeat_kJ_mol := some "31.7"
      ionicRadius_pm := none
      latticeConstant_ang := some "2.74"
      latticeStructure := some "HEX"
      meltingPoint_K := some "3327"
      oxidationStates := [8, 6, 4, 3, 2, 0, -2]
      paulingNegativity := some "2.2"
      specificHeat_J_g_mol := some "0.131"
      thermalConductivity_25C_W_m_K := some "(87.6)"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 77
      symbol := "Ir"
      name := "Iridium"
      atomicMass := some "192.22"
      atomicRadius_pm := some "135"
      atomicVolume_cm3_per_mol := some "8.54"
      boilingPoint_K := some "4403"
      covalentRadius_pm := some "141"
      density_g_per_cm3 := some "22.42"
      electronicConfiguration := some "[Xe]4f15d6s2"
      evaporationHeat_kJ_mol := some "604"
      firstIonizing_kJ_mol := some "868.1"
      fusionHeat_kJ_mol := some "27.61"
      ionicRadius_pm := none
      latticeConstant_ang := some "3.84"
      latticeStructure := some "FCC"
      meltingPoint_K := some "2683"
      oxidationStates := [6, 4, 3, 2, 1, 0, -1]
      paulingNegativity := some "2.2"
      specificHeat_J_g_mol := some "0.133"
      thermalConductivity_25C_W_m_K := some "147"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 78
      symbol := "Pt"
      name := "Platinum"
      atomicMass := some "195.08"
      atomicRadius_pm := some "135"
      atomicVolume_cm3_per_mol := some "9.1"
      boilingPoint_K := some "4100"
      covalentRadius_pm := some "136"
      density_g_per_cm3 := some "21.45"
      electronicConfiguration := some "[Xe]4f15d6s2"
      evaporationHeat_kJ_mol := some "~470"
      firstIonizing_kJ_mol := some "868.1"
      fusionHeat_kJ_mol := some "21.76"
      ionicRadius_pm := none
      latticeConstant_ang := some "3.92"
      latticeStructure := some "FCC"
      meltingPoint_K := some "2045"
      oxidationStates := [4, 2, 0]
      paulingNegativity := some "2.28"
      specificHeat_J_g_mol := some "0.133"
      thermalConductivity_25C_W_m_K := some "71.6"
      vanDerWaalsRadius_pm := some "175"
    },
{
      atomicNumber := 79
      symbol := "Au"
      name := "Gold"
      atomicMass := some "196.96654"
      atomicRadius_pm := some "135"
      atomicVolume_cm3_per_mol := some "10.2"
      boilingPoint_K := some "3080"
      covalentRadius_pm := some "136"
      density_g_per_cm3 := some "19.3"
      electronicConfiguration := some "[Xe]4f15d16s2"
      evaporationHeat_kJ_mol := some "~340"
      firstIonizing_kJ_mol := some "889.3"
      fusionHeat_kJ_mol := some "12.68"
      ionicRadius_pm := none
      latticeConstant_ang := some "4.08"
      latticeStructure := some "FCC"
      meltingPoint_K := some "1337.58"
      oxidationStates := [3, 1]
      paulingNegativity := some "2.54"
      specificHeat_J_g_mol := some "0.129"
      thermalConductivity_25C_W_m_K := some "318"
      vanDerWaalsRadius_pm := some "166"
    },
{
      atomicNumber := 80
      symbol := "Hg"
      name := "Mercury"
      atomicMass := some "200.59"
      atomicRadius_pm := some "150"
      atomicVolume_cm3_per_mol := some "14.8"
      boilingPoint_K := some "629.73"
      covalentRadius_pm := some "132"
      density_g_per_cm3 := some "13.546 (@ +20degC)"
      electronicConfiguration := some "[Xe]4f15d16s2"
      evaporationHeat_kJ_mol := some "58.5"
      firstIonizing_kJ_mol := some "1006"
      fusionHeat_kJ_mol := some "2.295"
      ionicRadius_pm := none
      latticeConstant_ang := some "2.99"
      latticeStructure := some "RHL"
      meltingPoint_K := some "234.28"
      oxidationStates := [2, 1]
      paulingNegativity := some "2"
      specificHeat_J_g_mol := some "0.138"
      thermalConductivity_25C_W_m_K := some "8.3"
      vanDerWaalsRadius_pm := some "155"
    },
{
      atomicNumber := 81
      symbol := "Tl"
      name := "Thallium"
      atomicMass := some "204.3833"
      atomicRadius_pm := some "190"
      atomicVolume_cm3_per_mol := some "17.2"
      boilingPoint_K := some "1730"
      covalentRadius_pm := some "145"
      density_g_per_cm3 := some "11.85"
      electronicConfiguration := some "[Xe]4f15d16s26p1"
      evaporationHeat_kJ_mol := some "162.4"
      firstIonizing_kJ_mol := some "588.9"
      fusionHeat_kJ_mol := some "4.31"
      ionicRadius_pm := none
      latticeConstant_ang := some "3.46"
      latticeStructure := some "HEX"
      meltingPoint_K := some "576.6"
      oxidationStates := [3, 1]
      paulingNegativity := some "1.62"
      specificHeat_J_g_mol := some "0.128"
      thermalConductivity_25C_W_m_K := some "46.1"
      vanDerWaalsRadius_pm := some "196"
    },
{
      atomicNumber := 82
      symbol := "Pb"
      name := "Lead"
      atomicMass := some "207.2"
      atomicRadius_pm := some "180"
      atomicVolume_cm3_per_mol := some "18.3"
      boilingPoint_K := some "2013"
      covalentRadius_pm := some "146"
      density_g_per_cm3 := some "11.35"
      electronicConfiguration := some "[Xe]4f15d16s26p2"
      evaporationHeat_kJ_mol := some "177.8"
      firstIonizing_kJ_mol := some "715.2"
      fusionHeat_kJ_mol := some "4.77"
      ionicRadius_pm := none
      latticeConstant_ang := some "4.95"
      latticeStructure := some "FCC"
      meltingPoint_K := some "600.65"
      oxidationStates := [4, 2]
      paulingNegativity := some "1.8"
      specificHeat_J_g_mol := some "0.159"
      thermalConductivity_25C_W_m_K := some "35.3"
      vanDerWaalsRadius_pm := some "202"
    },
{
      atomicNumber := 83
      symbol := "Bi"
      name := "Bismuth"
      atomicMass := some "208.98038"
      atomicRadius_pm := some "160"
      atomicVolume_cm3_per_mol := some "21.3"
      boilingPoint_K := some "1883"
      covalentRadius_pm := some "148"
      density_g_per_cm3 := some "9.747"
      electronicConfiguration := some "[Xe]4f15d16s26p3"
      evaporationHeat_kJ_mol := some "172"
      firstIonizing_kJ_mol := some "702.9"
      fusionHeat_kJ_mol := some "11"
      ionicRadius_pm := none
      latticeConstant_ang := some "4.75"
      latticeStructure := some "RHL"
      meltingPoint_K := some "544.5"
      oxidationStates := [5, 3]
      paulingNegativity := some "2.02"
      specificHeat_J_g_mol := some "0.124"
      thermalConductivity_25C_W_m_K := some "7.9"
      vanDerWaalsRadius_pm := some "207"
    },
{
      atomicNumber := 84
      symbol := "Po"
      name := "Polonium"
      atomicMass := some "208.9824"
      atomicRadius_pm := some "190"
      atomicVolume_cm3_per_mol := some "22.7"
      boilingPoint_K := some "1235"
      covalentRadius_pm := some "140"
      density_g_per_cm3 := some "9.32"
      electronicConfiguration := some "[Xe]4f15d16s26p"
      evaporationHeat_kJ_mol := some "(102.9)"
      firstIonizing_kJ_mol := some "813.1"
      fusionHeat_kJ_mol := some "(10)"
      ionicRadius_pm := none
      latticeConstant_ang := some "3.35"
      latticeStructure := some "SC"
      meltingPoint_K := some "527"
      oxidationStates := [6, 4, 2]
      paulingNegativity := some "2"
      specificHeat_J_g_mol := some "0.125"
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := some "197"
    },
{
      atomicNumber := 85
      symbol := "At"
      name := "Astatine"
      atomicMass := some "209.9871"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := none
      boilingPoint_K := some "610"
      covalentRadius_pm := some "150"
      density_g_per_cm3 := none
      electronicConfiguration := some "[Xe]4f15d16s26p"
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := some "916.3"
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := none
      meltingPoint_K := some "575"
      oxidationStates := [7, 5, 3, 1, -1]
      paulingNegativity := some "2.2"
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := some "202"
    },
{
      atomicNumber := 86
      symbol := "Rn"
      name := "Radon"
      atomicMass := some "222.0176"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := none
      boilingPoint_K := some "211.4"
      covalentRadius_pm := some "150"
      density_g_per_cm3 := some "4.4 (@ -62degC)"
      electronicConfiguration := some "[Xe]4f15d16s26p"
      evaporationHeat_kJ_mol := some "18.1"
      firstIonizing_kJ_mol := some "1036.5"
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := some "FCC"
      meltingPoint_K := some "202"
      oxidationStates := []
      paulingNegativity := none
      specificHeat_J_g_mol := some "0.094"
      thermalConductivity_25C_W_m_K := some "0.0036"
      vanDerWaalsRadius_pm := some "220"
    },
{
      atomicNumber := 87
      symbol := "Fr"
      name := "Francium"
      atomicMass := some "223.0197"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := none
      boilingPoint_K := some "950"
      covalentRadius_pm := some "260"
      density_g_per_cm3 := none
      electronicConfiguration := some "[Rn]7s1"
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := some "~375"
      fusionHeat_kJ_mol := some "15"
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := some "BCC"
      meltingPoint_K := some "300"
      oxidationStates := [2]
      paulingNegativity := some "0.7"
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := some "348"
    },
{
      atomicNumber := 88
      symbol := "Ra"
      name := "Radium"
      atomicMass := some "226.0254"
      atomicRadius_pm := some "215"
      atomicVolume_cm3_per_mol := some "45"
      boilingPoint_K := some "1413"
      covalentRadius_pm := some "221"
      density_g_per_cm3 := some "(5.5)"
      electronicConfiguration := some "[Rn]7s2"
      evaporationHeat_kJ_mol := some "(113)"
      firstIonizing_kJ_mol := some "509"
      fusionHeat_kJ_mol := some "(9.6)"
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := none
      meltingPoint_K := some "973"
      oxidationStates := [2]
      paulingNegativity := some "0.9"
      specificHeat_J_g_mol := some "0.12"
      thermalConductivity_25C_W_m_K := some "(18.6)"
      vanDerWaalsRadius_pm := some "283"
    },
{
      atomicNumber := 89
      symbol := "Ac"
      name := "Actinium"
      atomicMass := some "227.0278"
      atomicRadius_pm := some "195"
      atomicVolume_cm3_per_mol := some "22.54"
      boilingPoint_K := some "3470"
      covalentRadius_pm := some "215"
      density_g_per_cm3 := none
      electronicConfiguration := some "[Rn]6d17s2"
      evaporationHeat_kJ_mol := some "(292.9)"
      firstIonizing_kJ_mol := some "665.5"
      fusionHeat_kJ_mol := some "(10.5)"
      ionicRadius_pm := none
      latticeConstant_ang := some "5.31"
      latticeStructure := some "FCC"
      meltingPoint_K := some "1320"
      oxidationStates := [3]
      paulingNegativity := some "1.1"
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 90
      symbol := "Th"
      name := "Thorium"
      atomicMass := some "232.0381"
      atomicRadius_pm := some "180"
      atomicVolume_cm3_per_mol := some "19.8"
      boilingPoint_K := some "5060"
      covalentRadius_pm := some "206"
      density_g_per_cm3 := some "11.78"
      electronicConfiguration := some "[Rn]5f6d17s2"
      evaporationHeat_kJ_mol := some "513.7"
      firstIonizing_kJ_mol := some "670.4"
      fusionHeat_kJ_mol := some "16.11"
      ionicRadius_pm := none
      latticeConstant_ang := some "5.08"
      latticeStructure := some "FCC"
      meltingPoint_K := some "2028"
      oxidationStates := [4]
      paulingNegativity := some "1.3"
      specificHeat_J_g_mol := some "0.113"
      thermalConductivity_25C_W_m_K := some "(54.0)"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 91
      symbol := "Pa"
      name := "Protactinium"
      atomicMass := some "231.03587"
      atomicRadius_pm := some "180"
      atomicVolume_cm3_per_mol := some "15"
      boilingPoint_K := some "4300"
      covalentRadius_pm := some "200"
      density_g_per_cm3 := some "15.37"
      electronicConfiguration := some "[Rn]5f26d17s2"
      evaporationHeat_kJ_mol := some "481.2"
      firstIonizing_kJ_mol := none
      fusionHeat_kJ_mol := some "16.7"
      ionicRadius_pm := none
      latticeConstant_ang := some "3.92"
      latticeStructure := some "TET"
      meltingPoint_K := some "2113"
      oxidationStates := [5, 4]
      paulingNegativity := some "1.5"
      specificHeat_J_g_mol := some "0.121"
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 92
      symbol := "U"
      name := "Uranium"
      atomicMass := some "238.0289"
      atomicRadius_pm := some "175"
      atomicVolume_cm3_per_mol := some "12.5"
      boilingPoint_K := some "4018"
      covalentRadius_pm := some "196"
      density_g_per_cm3 := some "19.05"
      electronicConfiguration := some "[Rn]5f36d17s2"
      evaporationHeat_kJ_mol := some "417"
      firstIonizing_kJ_mol := some "686.4"
      fusionHeat_kJ_mol := some "12.6"
      ionicRadius_pm := none
      latticeConstant_ang := some "2.85"
      latticeStructure := some "ORC"
      meltingPoint_K := some "1405.5"
      oxidationStates := [6, 5, 4, 3]
      paulingNegativity := some "1.38"
      specificHeat_J_g_mol := some "0.115"
      thermalConductivity_25C_W_m_K := some "27.5"
      vanDerWaalsRadius_pm := some "186"
    },
{
      atomicNumber := 93
      symbol := "Np"
      name := "Neptunium"
      atomicMass := some "237.048"
      atomicRadius_pm := some "175"
      atomicVolume_cm3_per_mol := some "21.1"
      boilingPoint_K := some "4175"
      covalentRadius_pm := some "190"
      density_g_per_cm3 := some "20.25"
      electronicConfiguration := some "[Rn]5f6d17s2"
      evaporationHeat_kJ_mol := some "336"
      firstIonizing_kJ_mol := none
      fusionHeat_kJ_mol := some "(9.6)"
      ionicRadius_pm := none
      latticeConstant_ang := some "4.72"
      latticeStructure := some "ORC"
      meltingPoint_K := some "913"
      oxidationStates := [6, 5, 4, 3]
      paulingNegativity := some "1.36"
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := some "(6.3)"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 94
      symbol := "Pu"
      name := "Plutonium"
      atomicMass := some "244.0642"
      atomicRadius_pm := some "175"
      atomicVolume_cm3_per_mol := none
      boilingPoint_K := some "3505"
      covalentRadius_pm := some "187"
      density_g_per_cm3 := some "19.84"
      electronicConfiguration := some "[Rn]5f6d7s2"
      evaporationHeat_kJ_mol := some "343.5"
      firstIonizing_kJ_mol := some "491.9"
      fusionHeat_kJ_mol := some "2.8"
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := some "MCL"
      meltingPoint_K := some "914"
      oxidationStates := [6, 5, 4, 3]
      paulingNegativity := some "1.28"
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := some "(6.7)"
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 95
      symbol := "Am"
      name := "Americium"
      atomicMass := some "243.0614"
      atomicRadius_pm := some "175"
      atomicVolume_cm3_per_mol := some "20.8"
      boilingPoint_K := some "2880"
      covalentRadius_pm := some "180"
      density_g_per_cm3 := some "13.67"
      electronicConfiguration := some "[Rn]5f6d7s2"
      evaporationHeat_kJ_mol := some "238.5"
      firstIonizing_kJ_mol := none
      fusionHeat_kJ_mol := some "(10.0)"
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := none
      meltingPoint_K := some "1267"
      oxidationStates := [6, 5, 4, 3]
      paulingNegativity := some "1.3"
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 96
      symbol := "Cm"
      name := "Curium"
      atomicMass := some "247.0703"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := some "18.28"
      boilingPoint_K := none
      covalentRadius_pm := some "169"
      density_g_per_cm3 := some "13.51"
      electronicConfiguration := some "[Rn]5f6d17s2"
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := some "(580)"
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := none
      meltingPoint_K := some "1340"
      oxidationStates := [4, 3]
      paulingNegativity := some "1.3"
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 97
      symbol := "Bk"
      name := "Berkelium"
      atomicMass := some "247.0703"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := none
      boilingPoint_K := none
      covalentRadius_pm := none
      density_g_per_cm3 := some "13.25"
      electronicConfiguration := some "[Rn]5f6d7s2"
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := some "(600)"
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := none
      meltingPoint_K := none
      oxidationStates := [4, 3]
      paulingNegativity := some "1.3"
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 98
      symbol := "Cf"
      name := "Californium"
      atomicMass := some "251.0796"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := none
      boilingPoint_K := none
      covalentRadius_pm := none
      density_g_per_cm3 := some "15.1"
      electronicConfiguration := some "[Rn]5f16d7s2"
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := some "(610)"
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := none
      meltingPoint_K := some "900"
      oxidationStates := [4, 3]
      paulingNegativity := some "1.3"
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 99
      symbol := "Es"
      name := "Einsteinium"
      atomicMass := some "252.083"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := none
      boilingPoint_K := some "1130"
      covalentRadius_pm := none
      density_g_per_cm3 := none
      electronicConfiguration := some "[Rn]5f116d7s2"
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := some "(620)"
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := none
      meltingPoint_K := none
      oxidationStates := [3]
      paulingNegativity := some "1.3"
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 100
      symbol := "Fm"
      name := "Fermium"
      atomicMass := some "257.0951"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := none
      boilingPoint_K := none
      covalentRadius_pm := none
      density_g_per_cm3 := none
      electronicConfiguration := some "[Rn]5f126d7s2"
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := some "(630)"
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := none
      meltingPoint_K := some "1800"
      oxidationStates := [3]
      paulingNegativity := some "1.3"
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 101
      symbol := "Md"
      name := "Mendelevium"
      atomicMass := some "258.1"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := none
      boilingPoint_K := none
      covalentRadius_pm := none
      density_g_per_cm3 := none
      electronicConfiguration := some "[Rn]5f136d7s2"
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := some "(635)"
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := none
      meltingPoint_K := some "1100"
      oxidationStates := [3]
      paulingNegativity := some "1.3"
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 102
      symbol := "No"
      name := "Nobelium"
      atomicMass := some "259.1009"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := none
      boilingPoint_K := none
      covalentRadius_pm := none
      density_g_per_cm3 := none
      electronicConfiguration := some "[Rn]5f16d7s2"
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := some "(640)"
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := none
      meltingPoint_K := some "1100"
      oxidationStates := [3, 2]
      paulingNegativity := some "1.3"
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 103
      symbol := "Lr"
      name := "Lawrencium"
      atomicMass := some "262.11"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := none
      boilingPoint_K := none
      covalentRadius_pm := none
      density_g_per_cm3 := none
      electronicConfiguration := some "[Rn]5f16d17s2"
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := none
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := none
      meltingPoint_K := none
      oxidationStates := [3]
      paulingNegativity := none
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 104
      symbol := "Rf"
      name := "Rutherfordium"
      atomicMass := some "267"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := none
      boilingPoint_K := none
      covalentRadius_pm := none
      density_g_per_cm3 := none
      electronicConfiguration := some "[Rn]5f16d27s2"
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := none
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := none
      meltingPoint_K := none
      oxidationStates := []
      paulingNegativity := none
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 105
      symbol := "Db"
      name := "Dubnium"
      atomicMass := some "270"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := none
      boilingPoint_K := none
      covalentRadius_pm := none
      density_g_per_cm3 := none
      electronicConfiguration := some "[Rn]5f16d36s2"
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := none
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := none
      meltingPoint_K := none
      oxidationStates := []
      paulingNegativity := none
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 106
      symbol := "Sg"
      name := "Seaborgium"
      atomicMass := some "269"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := none
      boilingPoint_K := none
      covalentRadius_pm := none
      density_g_per_cm3 := none
      electronicConfiguration := some "[Rn]5f16d17s2"
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := none
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := none
      meltingPoint_K := none
      oxidationStates := []
      paulingNegativity := none
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 107
      symbol := "Bh"
      name := "Bohrium"
      atomicMass := some "270"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := none
      boilingPoint_K := none
      covalentRadius_pm := none
      density_g_per_cm3 := none
      electronicConfiguration := none
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := none
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := none
      meltingPoint_K := none
      oxidationStates := []
      paulingNegativity := none
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 108
      symbol := "Hs"
      name := "Hassium"
      atomicMass := some "277"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := none
      boilingPoint_K := none
      covalentRadius_pm := none
      density_g_per_cm3 := none
      electronicConfiguration := none
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := none
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := none
      meltingPoint_K := none
      oxidationStates := []
      paulingNegativity := none
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 109
      symbol := "Mt"
      name := "Meitnerium"
      atomicMass := some "278"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := none
      boilingPoint_K := none
      covalentRadius_pm := none
      density_g_per_cm3 := none
      electronicConfiguration := none
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := none
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := none
      meltingPoint_K := none
      oxidationStates := []
      paulingNegativity := none
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 110
      symbol := "Ds"
      name := "Darmstadtium"
      atomicMass := some "281"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := none
      boilingPoint_K := none
      covalentRadius_pm := none
      density_g_per_cm3 := none
      electronicConfiguration := none
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := none
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := none
      meltingPoint_K := none
      oxidationStates := []
      paulingNegativity := none
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 111
      symbol := "Rg"
      name := "Roentgenium"
      atomicMass := some "282"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := none
      boilingPoint_K := none
      covalentRadius_pm := none
      density_g_per_cm3 := none
      electronicConfiguration := none
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := none
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := none
      meltingPoint_K := none
      oxidationStates := []
      paulingNegativity := none
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 112
      symbol := "Cn"
      name := "Copernicium"
      atomicMass := some "285"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := none
      boilingPoint_K := none
      covalentRadius_pm := none
      density_g_per_cm3 := none
      electronicConfiguration := none
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := none
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := none
      meltingPoint_K := none
      oxidationStates := []
      paulingNegativity := none
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 113
      symbol := "Nh"
      name := "Nihonium"
      atomicMass := some "286"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := none
      boilingPoint_K := none
      covalentRadius_pm := none
      density_g_per_cm3 := none
      electronicConfiguration := none
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := none
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := none
      meltingPoint_K := none
      oxidationStates := []
      paulingNegativity := none
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 114
      symbol := "Fl"
      name := "Flerovium"
      atomicMass := some "289"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := none
      boilingPoint_K := none
      covalentRadius_pm := none
      density_g_per_cm3 := none
      electronicConfiguration := none
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := none
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := none
      meltingPoint_K := none
      oxidationStates := []
      paulingNegativity := none
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 115
      symbol := "Mc"
      name := "Moscovium"
      atomicMass := some "290"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := none
      boilingPoint_K := none
      covalentRadius_pm := none
      density_g_per_cm3 := none
      electronicConfiguration := none
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := none
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := none
      meltingPoint_K := none
      oxidationStates := []
      paulingNegativity := none
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 116
      symbol := "Lv"
      name := "Livermorium"
      atomicMass := some "293"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := none
      boilingPoint_K := none
      covalentRadius_pm := none
      density_g_per_cm3 := none
      electronicConfiguration := none
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := none
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := none
      meltingPoint_K := none
      oxidationStates := []
      paulingNegativity := none
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 117
      symbol := "Ts"
      name := "Tennessine"
      atomicMass := some "294"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := none
      boilingPoint_K := none
      covalentRadius_pm := none
      density_g_per_cm3 := none
      electronicConfiguration := none
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := none
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := none
      meltingPoint_K := none
      oxidationStates := []
      paulingNegativity := none
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := none
    },
{
      atomicNumber := 118
      symbol := "Og"
      name := "Oganesson"
      atomicMass := some "294"
      atomicRadius_pm := none
      atomicVolume_cm3_per_mol := none
      boilingPoint_K := none
      covalentRadius_pm := none
      density_g_per_cm3 := none
      electronicConfiguration := none
      evaporationHeat_kJ_mol := none
      firstIonizing_kJ_mol := none
      fusionHeat_kJ_mol := none
      ionicRadius_pm := none
      latticeConstant_ang := none
      latticeStructure := none
      meltingPoint_K := none
      oxidationStates := []
      paulingNegativity := none
      specificHeat_J_g_mol := none
      thermalConductivity_25C_W_m_K := none
      vanDerWaalsRadius_pm := none
    },
  ]

@[simp] theorem exabyteTable_size : exabyteTable.size = 118 := rfl

def exabyteInfo (e : Element) : ExabyteElementProperties :=
  exabyteTable[(⟨e.val, by simp [exabyteTable_size]⟩ : Fin exabyteTable.size)]

def exabyteAtomicNumber (e : Element) : Nat := (exabyteInfo e).atomicNumber
def exabyteSymbol (e : Element) : String := (exabyteInfo e).symbol
def exabyteName (e : Element) : String := (exabyteInfo e).name

/-- Sanity: the Exabyte table atomic numbers agree with our `Element` indexing. -/
theorem exabyte_atomicNumber_matches : ∀ e : Element, exabyteAtomicNumber e = atomicNumber e := by
  native_decide

end HeytingLean.Chem.PeriodicTable
