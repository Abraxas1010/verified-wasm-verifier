namespace HeytingLean.Chem.Materials

-- Placeholder: for now, we track a space group as a label and refine later
-- into an actual group action on the lattice/basis.
structure SpaceGroup where
  label : String
deriving Repr, DecidableEq

end HeytingLean.Chem.Materials

