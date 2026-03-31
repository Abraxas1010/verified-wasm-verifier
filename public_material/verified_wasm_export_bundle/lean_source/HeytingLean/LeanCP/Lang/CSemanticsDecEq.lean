import HeytingLean.LeanCP.Lang.CSemantics

namespace HeytingLean.LeanCP

instance : DecidableEq CState
  | ⟨h1, e1, n1, m1, a1⟩, ⟨h2, e2, n2, m2, a2⟩ =>
      match decEq h1 h2, decEq e1 e2, decEq n1 n2, decEq m1 m2, decEq a1 a2 with
      | isTrue hh, isTrue he, isTrue hn, isTrue hm, isTrue ha =>
          isTrue (by cases hh; cases he; cases hn; cases hm; cases ha; rfl)
      | isFalse hh, _, _, _, _ =>
          isFalse (by intro h; cases h; exact hh rfl)
      | _, isFalse he, _, _, _ =>
          isFalse (by intro h; cases h; exact he rfl)
      | _, _, isFalse hn, _, _ =>
          isFalse (by intro h; cases h; exact hn rfl)
      | _, _, _, isFalse hm, _ =>
          isFalse (by intro h; cases h; exact hm rfl)
      | _, _, _, _, isFalse ha =>
          isFalse (by intro h; cases h; exact ha rfl)

instance : DecidableEq ExecResult
  | .normal st1, .normal st2 =>
      match decEq st1 st2 with
      | isTrue h => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro hEq; cases hEq; exact h rfl)
  | .returned v1 st1, .returned v2 st2 =>
      match decEq v1 v2, decEq st1 st2 with
      | isTrue hv, isTrue hs =>
          isTrue (by cases hv; cases hs; rfl)
      | isFalse hv, _ =>
          isFalse (by intro hEq; cases hEq; exact hv rfl)
      | _, isFalse hs =>
          isFalse (by intro hEq; cases hEq; exact hs rfl)
  | .normal _, .returned _ _ =>
      isFalse (by intro h; cases h)
  | .returned _ _, .normal _ =>
      isFalse (by intro h; cases h)

end HeytingLean.LeanCP
