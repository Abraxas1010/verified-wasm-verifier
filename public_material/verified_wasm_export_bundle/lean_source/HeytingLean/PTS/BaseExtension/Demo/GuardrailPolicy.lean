import HeytingLean.PTS.BaseExtension.Main
import HeytingLean.PTS.BaseExtension.Search

namespace HeytingLean.PTS.BaseExtension.Demo

open HeytingLean.PTS.BaseExtension

def safeAtom : Atom := ⟨10⟩
def approvedAtom : Atom := ⟨11⟩
def piiMaskedAtom : Atom := ⟨12⟩
def retentionTaggedAtom : Atom := ⟨13⟩
def minimizationCheckedAtom : Atom := ⟨14⟩
def auditTrailAtom : Atom := ⟨15⟩
def exportAllowedAtom : Atom := ⟨16⟩
def compliantAtom : Atom := ⟨17⟩
def legalBasisAtom : Atom := ⟨18⟩
def reviewLoggedAtom : Atom := ⟨19⟩

def guardrailNamedAtoms : List Atom :=
  [ safeAtom
  , approvedAtom
  , piiMaskedAtom
  , retentionTaggedAtom
  , minimizationCheckedAtom
  , auditTrailAtom
  , exportAllowedAtom
  , compliantAtom
  , legalBasisAtom
  , reviewLoggedAtom
  ]

def guardrailPolicy : IPL :=
  IPL.imp (.atom safeAtom)
    (IPL.imp (.atom approvedAtom)
      (IPL.imp (.atom piiMaskedAtom)
        (IPL.imp (.atom retentionTaggedAtom)
          (IPL.imp (.atom minimizationCheckedAtom) (.atom compliantAtom)))))

def guardrailProgram : Program :=
  [ .atom (.atom safeAtom)
  , .atom (.atom approvedAtom)
  , .atom (.atom piiMaskedAtom)
  , .atom (.atom retentionTaggedAtom)
  , .atom (.atom minimizationCheckedAtom)
  , .imp (.conj (.atom (.atom approvedAtom)) (.atom (.atom piiMaskedAtom))) (.atom auditTrailAtom)
  , .imp (.conj (.atom (.atom auditTrailAtom)) (.atom (.atom retentionTaggedAtom))) (.atom exportAllowedAtom)
  , .imp (.conj (.atom (.atom exportAllowedAtom)) (.atom (.atom minimizationCheckedAtom))) (.atom compliantAtom)
  , .imp (.atom (.atom safeAtom)) (.atom legalBasisAtom)
  , .imp (.atom (.atom legalBasisAtom)) (.atom auditTrailAtom)
  , .imp (.atom (.atom approvedAtom)) (.atom reviewLoggedAtom)
  , .imp (.atom (.atom reviewLoggedAtom)) (.atom retentionTaggedAtom)
  ]

def guardrailResult : Bool :=
  search 96 guardrailProgram (encode guardrailPolicy)

example : guardrailProgram.length >= 12 := by
  native_decide

example : guardrailNamedAtoms.length >= 8 := by
  native_decide

example : guardrailResult = true := by
  native_decide

end HeytingLean.PTS.BaseExtension.Demo
