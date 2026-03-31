import HeytingLean.Matula.Basic

namespace HeytingLean
namespace CLI

open HeytingLean.Matula

def MatulaDemo.run : IO Unit := do
  let sampleNs := [1, 2, 3, 4, 5, 6, 7, 8, 12, 30, 60]
  IO.println "Matula demo (n, tree, size, height, leaves, re-encode):"
  for n in sampleNs do
    let t := matulaDecode n
    IO.println s!"  {n} -> {repr t}, size={t.size}, height={t.height}, leaves={t.leaves}, re={matulaEncode t}"

  let unsorted : RTree := .node [.node [.leaf], .leaf]
  let canon := RTree.canonicalizeByMatula unsorted
  IO.println s!"Canonicalization sample:"
  IO.println s!"  unsorted = {repr unsorted}"
  IO.println s!"  canonical = {repr canon}"
  IO.println s!"  decode(encode(unsorted)) = {repr (matulaDecode (matulaEncode unsorted))}"

end CLI
end HeytingLean

def main : IO Unit :=
  HeytingLean.CLI.MatulaDemo.run
