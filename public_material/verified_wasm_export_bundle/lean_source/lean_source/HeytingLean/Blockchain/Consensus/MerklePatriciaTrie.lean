import HeytingLean.Basic

/-
# Blockchain.Consensus.MerklePatriciaTrie

Example Merkle-Patricia-style trie model and a minimal correctness
statement: inserting a key/value pair makes subsequent lookup of that
key return the inserted value.

This is a deliberately small, self-contained model intended to back the
`merklePatriciaTrie` consensus property with a concrete Lean theorem.
-/

namespace HeytingLean
namespace Blockchain
namespace Consensus
namespace MerklePatriciaTrie

/-- Keys are modelled as lists of Boolean "nibbles". -/
abbrev Key := List Bool

/-- Values stored in the trie (minimal value type). -/
abbrev Value := Nat

/-- Example Patricia-trie structure: each node carries an optional value at
    its position and two subtries for `false`/`true` branches. -/
inductive Trie where
  | empty
  | node (value? : Option Value) (left right : Trie)
  deriving Repr

namespace Trie

/-- Lookup a key in the trie, following bits left/right and returning
    the value stored at the final node (if any). -/
def lookup : Trie → Key → Option Value
  | .empty, _ => none
  | .node v _ _ , [] => v
  | .node _ l r, b :: ks =>
      if b then lookup r ks else lookup l ks

/-- Insert a value at the given key, creating intermediate nodes as
    needed and overwriting any existing value at that key. -/
def insert : Trie → Key → Value → Trie
  | .empty, [], v =>
      .node (some v) .empty .empty
  | .empty, b :: ks, v =>
      if b then
        .node none .empty (insert .empty ks v)
      else
        .node none (insert .empty ks v) .empty
  | .node _ l r, [], v =>
      .node (some v) l r
  | .node val l r, b :: ks, v =>
      if b then
        .node val l (insert r ks v)
      else
        .node val (insert l ks v) r

/-- Lookup after inserting the same key returns the inserted value. -/
theorem lookup_insert_self (t : Trie) (k : Key) (v : Value) :
    lookup (insert t k v) k = some v := by
  induction k generalizing t with
  | nil =>
      -- Key is empty: we overwrite or create the value at the root.
      cases t with
      | empty =>
          simp [insert, lookup]
      | node val l r =>
          simp [insert, lookup]
  | cons b ks ih =>
      -- Key has head bit `b` and tail `ks`.
      cases t with
      | empty =>
          by_cases h : b
          · -- Insert along the right branch.
            simp [insert, lookup, h, ih]
          · -- Insert along the left branch.
            simp [insert, lookup, h, ih]
      | node val l r =>
          by_cases h : b
          · -- Recurse into the right subtree.
            simp [insert, lookup, h, ih]
          · -- Recurse into the left subtree.
            simp [insert, lookup, h, ih]

end Trie

/-- Merkle-Patricia-trie correctness statement: inserting a key/value
    pair and then looking up that key yields the inserted value. -/
def Statement : Prop :=
  ∀ (t : Trie) (k : Key) (v : Value),
    Trie.lookup (Trie.insert t k v) k = some v

/-- `Statement` holds for the example trie model via `lookup_insert_self`. -/
theorem statement_holds : Statement := by
  intro t k v
  exact Trie.lookup_insert_self t k v

end MerklePatriciaTrie
end Consensus
end Blockchain
end HeytingLean
