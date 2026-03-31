import HeytingLean.LoF.ICC.Syntax

/-!
# ICC Term Binary Serialization

Serialize/deserialize ICC.Term to/from ByteArray for FFI transport
to the precompiled C reduction kernel.

Binary format (little-endian):
  TAG (1 byte) + payload
  Tags: 0=var(idx:u32), 1=lam(body), 2=app(fn,arg), 3=bridge(body), 4=ann(val,typ)
-/

namespace LeanClef.FFI

open HeytingLean.LoF.ICC

/-- Serialize an ICC.Term to ByteArray. -/
partial def serializeTerm (t : Term) : ByteArray :=
  let buf := ByteArray.mkEmpty (t.size * 5)
  go t buf
where
  pushU32 (buf : ByteArray) (v : UInt32) : ByteArray :=
    buf.push (v.toUInt8)
      |>.push ((v >>> 8).toUInt8)
      |>.push ((v >>> 16).toUInt8)
      |>.push ((v >>> 24).toUInt8)

  go (t : Term) (buf : ByteArray) : ByteArray :=
    match t with
    | .var idx =>
        pushU32 (buf.push 0) idx.toUInt32
    | .lam body =>
        go body (buf.push 1)
    | .app fn arg =>
        let buf := go fn (buf.push 2)
        go arg buf
    | .bridge body =>
        go body (buf.push 3)
    | .ann val typ =>
        let buf := go val (buf.push 4)
        go typ buf

/-- Deserialize a ByteArray to ICC.Term. Returns (term, bytes_consumed). -/
partial def deserializeTerm (data : ByteArray) (pos : Nat := 0) : Option (Term × Nat) :=
  if pos < data.size then
    let tag := data.get! pos
    match tag.toNat with
    | 0 => -- VAR
      if pos + 5 ≤ data.size then
        let idx := (data.get! (pos + 1)).toNat
               ||| ((data.get! (pos + 2)).toNat <<< 8)
               ||| ((data.get! (pos + 3)).toNat <<< 16)
               ||| ((data.get! (pos + 4)).toNat <<< 24)
        some (.var idx, pos + 5)
      else none
    | 1 => -- LAM
      match deserializeTerm data (pos + 1) with
      | some (body, next) => some (.lam body, next)
      | none => none
    | 2 => -- APP
      match deserializeTerm data (pos + 1) with
      | some (fn, next1) =>
        match deserializeTerm data next1 with
        | some (arg, next2) => some (.app fn arg, next2)
        | none => none
      | none => none
    | 3 => -- BRIDGE
      match deserializeTerm data (pos + 1) with
      | some (body, next) => some (.bridge body, next)
      | none => none
    | 4 => -- ANN
      match deserializeTerm data (pos + 1) with
      | some (val, next1) =>
        match deserializeTerm data next1 with
        | some (typ, next2) => some (.ann val typ, next2)
        | none => none
      | none => none
    | _ => none
  else none

/-- Round-trip test: serialize then deserialize, verify equality. -/
def roundTrip (t : Term) : Bool :=
  match deserializeTerm (serializeTerm t) with
  | some (t', _) => t == t'
  | none => false

end LeanClef.FFI
