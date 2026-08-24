/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyData

/-! # Exact separation of compact carrier-node source tags -/

namespace LeanTrominoes.PeriodicOrthocrossing.CarrierNodeSourceKeys

@[simp] theorem segmentEndTag_lt_eight (endpoint : SegmentEnd) :
    segmentEndTag endpoint < 8 := by
  cases endpoint <;> decide

@[simp] theorem crossingSideTag_lt_eight (side : CrossingSide) :
    crossingSideTag side < 8 := by
  cases side <;> decide

theorem segmentEndTag_injective : Function.Injective segmentEndTag := by
  intro first second equal
  cases first <;> cases second <;> simp_all [segmentEndTag]

theorem crossingSideTag_injective : Function.Injective crossingSideTag := by
  intro first second equal
  cases first <;> cases second <;> simp_all [crossingSideTag]

theorem segmentEndTag_ne_crossingSideTag
    (endpoint : SegmentEnd) (side : CrossingSide) :
    segmentEndTag endpoint ≠ crossingSideTag side := by
  cases endpoint <;> cases side <;> decide

/-- The reserved low three bits recover both the original segment index and
the node tag. -/
theorem taggedKey_eq
    (first second : CarrierKey) (firstTag secondTag : Nat)
    (firstTagLt : firstTag < 8) (secondTagLt : secondTag < 8)
    (equal : taggedKey first firstTag = taggedKey second secondTag) :
    first = second ∧ firstTag = secondTag := by
  rcases first with
    ⟨firstRoute, firstSegment, firstHorizontal, firstVertical⟩
  rcases second with
    ⟨secondRoute, secondSegment, secondHorizontal, secondVertical⟩
  simp only [taggedKey, Prod.mk.injEq] at equal
  have segmentEq : firstSegment = secondSegment := by omega
  have tagEq : firstTag = secondTag := by omega
  exact ⟨by simp [equal.1, equal.2.2.1, equal.2.2.2,
    segmentEq], tagEq⟩

end LeanTrominoes.PeriodicOrthocrossing.CarrierNodeSourceKeys
