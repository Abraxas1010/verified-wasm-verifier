import Std
import HeytingLean.BountyHunter.Solc.YulObjectMini.Types

/-!
# HeytingLean.BountyHunter.Solc.YulObjectMini.Pretty

Deterministic pretty-printer for the Yul object AST.

This deliberately canonicalizes layout (2-space indents) and does not attempt to
preserve original whitespace.
-/

namespace HeytingLean.BountyHunter.Solc.YulObjectMini

private def escapeString (s : String) : String :=
  s.foldl (fun acc c => if c = '"' then acc ++ "\\\"" else if c = '\\' then acc ++ "\\\\" else acc.push c) ""

private def indentLines (n : Nat) (s : String) : String :=
  let pad := (List.replicate n ' ').asString
  String.intercalate "\n" (s.splitOn "\n" |>.map (fun line => if line = "" then line else pad ++ line))

private def dataValueToString (v : DataValue) : String :=
  match v with
  | .str s => s!"\"{escapeString s}\""
  | .hex s => s!"hex\"{escapeString s}\""

mutual
  partial def itemToString (it : Item) (indent : Nat := 0) : String :=
    match it with
    | .object name items =>
        let inner := itemsToString items (indent + 2)
        indentLines indent ("object \"" ++ escapeString name ++ "\" {\n" ++ inner ++ "\n}")
    | .code body =>
        -- `body` is expected to already be in a reasonable canonical form. We still indent it.
        let inner := indentLines (indent + 2) body
        indentLines indent ("code {\n" ++ inner ++ "\n" ++ (List.replicate indent ' ').asString ++ "}")
    | .data name v =>
        indentLines indent ("data \"" ++ escapeString name ++ "\" " ++ dataValueToString v)

  partial def itemsToString (items : Array Item) (indent : Nat := 0) : String :=
    String.intercalate "\n" (items.toList.map (fun it => itemToString it indent))
end

def programToCanonicalString (p : Program) : String :=
  itemsToString p.items 0

end HeytingLean.BountyHunter.Solc.YulObjectMini

