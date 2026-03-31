import HeytingLean.Util.SHA

/-
Basic SHA-256 test vectors for the pure implementation and IO wrapper.

This executable is intended to be run under different `LOF_SHA_MODE` settings.
For example:
* `LOF_SHA_MODE=pure lake exe test_sha256_vectors`
* `LOF_SHA_MODE=external lake exe test_sha256_vectors` (may fall back to pure
  if the optional external `hashutil` is not available)
-/

open HeytingLean
open HeytingLean.Util

def main (_args : List String) : IO UInt32 := do
  let vectors : List (String × String) :=
    [ ("", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
    , ("abc", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
    , ("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
      , "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1")
    , ("The quick brown fox jumps over the lazy dog"
      , "d7a8fbb307d7809469ca9abcb0082e4f8d5651e46d3cdb762d02d0bf37c9e592")
    , ("The quick brown fox jumps over the lazy dog."
      , "ef537f25c895bfa782526529a9b63d97aa631564d5d789c2b765448c8635fb6c")
    ]
  for (inp, expected) in vectors do
    let pureHex := SHA256.sha256Hex inp.toUTF8
    if pureHex ≠ expected then
      IO.eprintln s!"SHA256 mismatch for input '{inp}': expected {expected}, got {pureHex}"
      return 1

    let ioHex ← sha256HexOfStringIO inp
    if ioHex ≠ expected then
      IO.eprintln s!"sha256HexOfStringIO mismatch for '{inp}': expected {expected}, got {ioHex}"
      return 1
    if ioHex ≠ pureHex then
      IO.eprintln s!"sha256HexOfStringIO disagrees with pure for '{inp}': {ioHex} vs {pureHex}"
      return 1

  -- FIPS-style large vector: 1,000,000 copies of 'a' (tested via ByteArray + file IO).
  let millionA : ByteArray :=
    ByteArray.mk (Array.replicate 1000000 (UInt8.ofNat 97))
  let expectedMillionA :=
    "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
  let pureHexLarge := SHA256.sha256Hex millionA
  if pureHexLarge ≠ expectedMillionA then
    IO.eprintln s!"SHA256 mismatch for 1,000,000 'a' bytes: expected {expectedMillionA}, got {pureHexLarge}"
    return 1
  let cwd ← IO.currentDir
  let outDir := cwd / System.FilePath.mk ".tmp" / System.FilePath.mk "sha256vectors"
  IO.FS.createDirAll outDir
  let path := outDir / System.FilePath.mk "million_a.bin"
  IO.FS.writeBinFile path millionA
  let ioHexLarge ← sha256HexOfFileIO path
  if ioHexLarge ≠ expectedMillionA then
    IO.eprintln s!"sha256HexOfFileIO mismatch for 1,000,000 'a' bytes: expected {expectedMillionA}, got {ioHexLarge}"
    return 1
  if ioHexLarge ≠ pureHexLarge then
    IO.eprintln s!"sha256HexOfFileIO disagrees with pure for 1,000,000 'a' bytes: {ioHexLarge} vs {pureHexLarge}"
    return 1
  IO.println "✓ SHA256Vectors test PASSED"
  return 0
