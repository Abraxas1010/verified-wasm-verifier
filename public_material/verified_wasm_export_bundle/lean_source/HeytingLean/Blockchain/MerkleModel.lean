import HeytingLean.Payments.Merkle
import Mathlib.Logic.Basic

/-
# Blockchain.MerkleModel

Structural Merkle-tree model and its connection to the concrete
string-based helpers in `HeytingLean.Payments.Merkle`.

This module introduces:
* a simple inductive Merkle tree type over payload strings;
* a structural `root` function defined in terms of the pure helpers
  `computeLeaf` and `combine`; and
* a structural membership predicate.

Full membership-correctness theorems relating this model to the
`verifyMembership` function are left for future work; they will be
recorded as propositions elsewhere once the proof strategy is fixed.
-/

namespace HeytingLean
namespace Blockchain
namespace MerkleModel

open HeytingLean.Payments
open HeytingLean.Payments.Merkle

/-- Simple binary Merkle tree over string payloads. -/
inductive Tree where
  | leaf (payload : String)
  | node (left right : Tree)
  deriving Repr, Inhabited

/-- Structural Merkle root, defined using the pure string-mode helpers
    from `HeytingLean.Payments.Merkle`. -/
def root : Tree → String
  | .leaf payload => computeLeaf payload
  | .node left right => combine (root left) (root right)

/-- Structural membership of a payload in a Merkle tree. -/
def member (x : String) : Tree → Prop
  | .leaf payload => x = payload
  | .node left right => member x left ∨ member x right

/-- Attempt to construct a Merkle path for a given payload in a tree.
    Returns `some path` when a witness is found, or `none` otherwise. -/
def buildPath? (x : String) : Tree → Option (List PathElem)
  | .leaf payload =>
      if x = payload then some [] else none
  | .node left right =>
      match buildPath? x left with
      | some pathL =>
          some (pathL ++ [{ side := "R", hash := root right }])
      | none =>
          match buildPath? x right with
          | some pathR =>
              some (pathR ++ [{ side := "L", hash := root left }])
          | none => none

/-- Soundness of `buildPath?`: whenever it returns `some path`, the
    structural membership predicate holds. -/
theorem buildPath?_member (x : String) :
    ∀ (t : Tree) (path : List PathElem),
      buildPath? x t = some path → member x t := by
  classical
  intro t
  induction t with
  | leaf payload =>
      intro path h
      -- In a leaf, successful search implies the payload matches `x`.
      by_cases hx : x = payload
      · subst hx
        -- `buildPath?` reduces to `some []`, so `path = []`.
        have : path = [] := by
          simpa [buildPath?] using h
        subst this
        -- Structural membership holds by definition.
        simp [member]
      · -- If `x ≠ payload`, the search must return `none`, contradicting `h`.
        have hnone : buildPath? x (.leaf payload) = none := by
          simp [buildPath?, hx]
        simp [hnone] at h
  | node left right ihLeft ihRight =>
      intro path h
      -- Case split on the result of searching the left subtree.
      cases hLeft : buildPath? x left with
      | some pathL =>
          -- If the left search succeeds, we have membership in `left`,
          -- hence membership in the whole tree.
          have hMemLeft : member x left :=
            ihLeft pathL hLeft
          exact Or.inl hMemLeft
      | none =>
          -- Left search failed; analyze the right subtree.
          cases hRight : buildPath? x right with
          | some pathR =>
              -- Membership follows from the right subtree.
              have hMemRight : member x right :=
                ihRight pathR hRight
              exact Or.inr hMemRight
          | none =>
              -- Both searches failed, contradicting `h`.
              have hnone : buildPath? x (.node left right) = none := by
                simp [buildPath?, hLeft, hRight]
              simp [hnone] at h

/-- Completeness of `buildPath?`: if `x` is structurally a member of
    `t`, then a Merkle path can be constructed. -/
theorem member_buildPath? (x : String) :
    ∀ (t : Tree), member x t → ∃ path, buildPath? x t = some path := by
  classical
  intro t
  induction t with
  | leaf payload =>
      intro h
      -- Membership in a leaf is just equality of payloads.
      refine ?_
      refine ⟨[], ?_⟩
      simp [member] at h
      subst h
      simp [buildPath?]
  | node left right ihLeft ihRight =>
      intro h
      -- Split membership across the subtrees.
      cases h with
      | inl hL =>
          -- Use IH on the left subtree and extend the path.
          rcases ihLeft hL with ⟨pathL, hPathL⟩
          refine ⟨pathL ++ [{ side := "R", hash := root right }], ?_⟩
          simp [buildPath?, hPathL]
      | inr hR =>
          -- Membership via the right subtree; we must account for the
          -- fact that the left search may or may not succeed.
          cases hLeft : buildPath? x left with
          | some pathL =>
              refine ⟨pathL ++ [{ side := "R", hash := root right }], ?_⟩
              simp [buildPath?, hLeft]
          | none =>
              rcases ihRight hR with ⟨pathR, hPathR⟩
              refine ⟨pathR ++ [{ side := "L", hash := root left }], ?_⟩
              simp [buildPath?, hLeft, hPathR]

/-- Existence form of completeness: structural membership is equivalent
    to the existence of a path found by `buildPath?`. -/
theorem member_iff_exists_path (x : String) (t : Tree) :
    member x t ↔ ∃ path, buildPath? x t = some path := by
  constructor
  · intro h; exact member_buildPath? x t h
  · intro h
    rcases h with ⟨path, hPath⟩
    exact buildPath?_member x t path hPath

/-- Hash an initial payload together with a Merkle path using the same
    folding logic as the pure `verifyMembership` helper. -/
def hashPath (x : String) (path : List PathElem) : String :=
  path.foldl
    (fun acc e =>
      if e.side == "L" then combine e.hash acc else combine acc e.hash)
    (computeLeaf x)

/-- Boolean equality facts for the literal side tags used in Merkle
    paths. -/
theorem beq_L_L : (( "L" : String) == "L") = true := by
  decide

theorem beq_R_L : (( "R" : String) == "L") = false := by
  decide

/-- Bridge from propositional equality on strings to boolean equality,
    using the `BEq` / `LawfulBEq` instances provided by the core/Std
    libraries and the `beq_eq_decide` and `decide_eq_true_eq` lemmas
    from Mathlib. -/
theorem string_eq_imp_beq (s₁ s₂ : String) (h : s₁ = s₂) :
    (s₁ == s₂) = true := by
  classical
  cases h
  simp

/-- Snoc lemma for `hashPath`: appending a single path element corresponds
    to one final hash-combine step. -/
theorem hashPath_snoc (x : String) (path : List PathElem) (e : PathElem) :
    hashPath x (path ++ [e]) =
      (if e.side == "L" then
        combine e.hash (hashPath x path)
      else
        combine (hashPath x path) e.hash) := by
  simp [hashPath, List.foldl_append]

/-- Hashing along a path returned by `buildPath?` reproduces the
    structural Merkle root. -/
theorem hashPath_of_buildPath? (x : String) :
    ∀ (t : Tree) (path : List PathElem),
      buildPath? x t = some path → hashPath x path = root t := by
  classical
  intro t
  induction t with
  | leaf payload =>
      intro path h
      by_cases hx : x = payload
      · subst hx
        have : path = [] := by
          simpa [buildPath?] using h
        subst this
        simp [hashPath, root]
      · have hnone : buildPath? x (.leaf payload) = none := by
          simp [buildPath?, hx]
        simp [hnone] at h
  | node left right ihLeft ihRight =>
      intro path h
      -- Split on the result of searching the left subtree.
      cases hLeft : buildPath? x left with
      | some pathL =>
          -- In this case, the path comes from the left subtree, extended
          -- with a right-sibling hash at the end.
          have happ :
              some (pathL ++ [{ side := "R", hash := root right }]) =
                some path := by
            simpa [buildPath?, hLeft] using h
          have hpath :
              pathL ++ [{ side := "R", hash := root right }] = path :=
            Option.some.inj happ
          -- Use the induction hypothesis on the left subtree and the
          -- snoc lemma for `hashPath`.
          have hLeftRoot : hashPath x pathL = root left :=
            ihLeft pathL hLeft
          let eR : PathElem := { side := "R", hash := root right }
          have hHash :
              hashPath x path =
                combine (hashPath x pathL) (root right) := by
            have h' := hashPath_snoc x pathL eR
            -- Specialise `hashPath_snoc` and simplify using `hpath`
            -- and the boolean-equality fact for `"R"`.
            have := congrArg id h'
            -- Rewrite the left-hand side to use `path` and simplify
            -- the boolean test `eR.side == "L"`.
            simpa [hpath, eR, beq_R_L] using h'
          -- Finally, rewrite using the IH and the node root definition.
          simpa [root, hLeftRoot] using hHash
      | none =>
          -- Left search failed; the path must come from the right subtree.
          cases hRight : buildPath? x right with
          | some pathR =>
              have happ :
                  some (pathR ++ [{ side := "L", hash := root left }]) =
                    some path := by
                simpa [buildPath?, hLeft, hRight] using h
              have hpath :
                  pathR ++ [{ side := "L", hash := root left }] = path :=
                Option.some.inj happ
              have hRightRoot : hashPath x pathR = root right :=
                ihRight pathR hRight
              let eL : PathElem := { side := "L", hash := root left }
              have hHash :
                  hashPath x path =
                    combine (root left) (hashPath x pathR) := by
                have h' := hashPath_snoc x pathR eL
                -- Here we are in the left-sibling case; simplify using
                -- the boolean-equality fact for `"L"`.
                simpa [hpath, eL, beq_L_L] using h'
              -- Finish by rewriting with the IH and the definition of `root`.
              simpa [root, hRightRoot] using hHash
          | none =>
              -- Both searches failed, contradicting `h`.
              have hnone : buildPath? x (.node left right) = none := by
                simp [buildPath?, hLeft, hRight]
              simp [hnone] at h

/-- `verifyMembership` expressed in terms of `hashPath`. -/
theorem verifyMembership_eq_hashPath (p : VProof) :
    verifyMembership p =
      (hashPath p.recipient p.path == p.root,
       hashPath p.recipient p.path) := by
  simp [verifyMembership, hashPath]

/-- Boolean-level correctness of `verifyMembership` for paths produced by
    `buildPath?`: whenever `buildPath?` finds a path for `x` in `t`, the
    pure `verifyMembership` helper accepts the corresponding proof and
    reproduces the structural root. -/
theorem verifyMembership_of_buildPath? (x : String)
    (t : Tree) (path : List PathElem)
    (h : buildPath? x t = some path) :
    verifyMembership
        { root := root t, recipient := x, path := path } =
      (true, root t) := by
  -- First, relate the hash of the path to the structural root.
  have hHash : hashPath x path = root t :=
    hashPath_of_buildPath? x t path h
  -- Re-express `verifyMembership` via `hashPath`.
  have hVM :
      verifyMembership
          { root := root t, recipient := x, path := path } =
        (hashPath x path == root t, hashPath x path) := by
    simpa using
      (verifyMembership_eq_hashPath
        { root := root t, recipient := x, path := path })
  -- Bridge between propositional equality and boolean equality on strings.
  calc
    verifyMembership
        { root := root t, recipient := x, path := path }
        = (hashPath x path == root t, hashPath x path) := hVM
    _ = (true, root t) := by
      -- Rewrite both components using `hHash` and `hBeq`.
      simp [hHash]

end MerkleModel
end Blockchain
end HeytingLean
