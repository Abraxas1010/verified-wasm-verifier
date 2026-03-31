import HeytingLean.Bridges.OneDimensionalCompression

/-!
# Bridges.LinearLogicBridge

This module adds a **compile-first** (conservative) bridge between:
- “resource sensitivity” intuitions from **linear logic**, and
- the repo’s already-landed **lossless encodings** (injective maps) used in 1D compression.

Scope note:
- We do **not** attempt to formalize full linear logic (proof nets, cut elimination, GoI) here.
  Instead, we package the minimal reusable facts needed to connect “lossless encoding” to a
  reconstruction principle (“no weakening” in the information-theoretic sense).
- Embedding experiments that model different “semantic regimes” live on the tooling side.
-/

namespace HeytingLean
namespace Bridges
namespace LinearLogic

universe u v

/-- A lossless encoding is an injection into some carrier type. -/
abbrev LosslessEncoding (T : Type u) (X : Type v) : Prop :=
  ∃ encode : T → X, Function.Injective encode

namespace LosslessEncoding

/--
Given an injective encoding, we can always “decode” values in its range.

This is the canonical reconstruction principle:
the encoding does not discard information (a computational analog of “no weakening”).
-/
noncomputable def decodeOfInj {T : Type u} {X : Type v} (encode : T → X) :
    Set.range encode → T :=
  fun y => Classical.choose y.property

theorem decodeOfInj_spec {T : Type u} {X : Type v} (encode : T → X) (y : Set.range encode) :
    encode (decodeOfInj (encode := encode) y) = y.1 :=
  Classical.choose_spec y.property

end LosslessEncoding

/-! ## Re-export concrete instances from OneDimensionalCompression -/

open HeytingLean.Bridges

theorem miranda_tape_lossless : LosslessEncoding HeytingLean.MirandaDynamics.Billiards.Tape ℝ :=
  ⟨HeytingLean.MirandaDynamics.Billiards.encodeTape,
    HeytingLean.MirandaDynamics.Billiards.encodeTape_injective⟩

theorem miranda_tapeHead_lossless :
    LosslessEncoding (HeytingLean.MirandaDynamics.Billiards.Tape × ℤ) ℝ :=
  ⟨fun p => HeytingLean.MirandaDynamics.Billiards.encodeWithHead p.1 p.2,
    HeytingLean.MirandaDynamics.Billiards.encodeWithHead_injective⟩

end LinearLogic
end Bridges
end HeytingLean

