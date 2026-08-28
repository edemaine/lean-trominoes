/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingGuardedCarrierSourcePairTrailingConstructorKeySemantics

/-! # Tagged source-pair semantics of delayed constructor classification -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace GuardedCarrierSourcePairTrailingConstructor

open DelimitedBinaryWords

/-- The guarded tagged source pair is reduced to its first key for a terminal
tag, retained whole for a boundary tag, and annotated by the corresponding
trailing constructor bit. -/
theorem scan_guardedTaggedPair
    (first second : CarrierKeyWords.CarrierKey) (tag : Nat) :
    let taggedFirst := CarrierNodeSourceKeys.taggedKey first tag
    let boundary := (TagRemainder.advance .zero tag).isBoundary
    FiniteStateTransducer.scan transition .between
        (wordTokens (true :: CarrierNodeSourceKeys.word
          (taggedFirst, second))) =
      (.between, wordTokens
        (if boundary then
          CarrierNodeSourceKeys.word (taggedFirst, second) ++ [true]
        else
          CarrierKeyWords.word taggedFirst ++ [false])) := by
  dsimp only
  unfold wordTokens CarrierNodeSourceKeys.word
  simp only [List.map_cons, List.map_append, List.cons_append,
    List.append_assoc, FiniteStateTransducer.scan, transition]
  rw [FiniteStateTransducer.scan_append, scan_taggedKey]
  simp only
  cases boundaryEq : (TagRemainder.advance .zero tag).isBoundary <;>
    simp [FiniteStateTransducer.scan, transition,
      scan_secondKey_wordEnd, List.map_append, List.append_assoc]

end GuardedCarrierSourcePairTrailingConstructor
end LeanTrominoes.PeriodicOrthocrossing
