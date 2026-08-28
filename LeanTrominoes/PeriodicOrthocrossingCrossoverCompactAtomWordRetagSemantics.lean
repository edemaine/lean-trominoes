/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyWordSemantics
import LeanTrominoes.PeriodicOrthocrossingCrossoverCompactAtomWordData

/-! # Exact boundary-side semantics of crossover source-pair retagging -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CrossoverCompactAtomWords

open CarrierNodeSourceKeys

@[simp] theorem retagFirstSegmentAfterRoute_natField
    (amount number : Nat) (suffix : List Bool) :
    retagFirstSegmentAfterRoute amount
        (CarrierKeyWords.natField number ++ suffix) =
      CarrierKeyWords.natField (number + amount) ++ suffix := by
  unfold CarrierKeyWords.natField
  induction number with
  | zero =>
      simp [retagFirstSegmentAfterRoute,
        List.append_assoc]
  | succ number induction =>
      rw [List.replicate_succ]
      simp only [List.cons_append, retagFirstSegmentAfterRoute]
      rw [induction, Nat.succ_add, List.replicate_succ]
      simp [List.append_assoc]

@[simp] theorem retagFirstSegment_natField
    (amount number : Nat) (suffix : List Bool) :
    retagFirstSegment amount
        (CarrierKeyWords.natField number ++ suffix) =
      CarrierKeyWords.natField number ++
        retagFirstSegmentAfterRoute amount suffix := by
  unfold CarrierKeyWords.natField
  induction number with
  | zero =>
      simp [retagFirstSegment]
  | succ number induction =>
      rw [List.replicate_succ]
      simp only [List.cons_append, retagFirstSegment]
      rw [induction]

/-- Retagging the first key word changes only its segment tag. -/
theorem retagFirstSegment_sourceKeyWord
    (amount route segment : Nat) (translate : Cell)
    (second : CarrierKeyWords.CarrierKey) :
    retagFirstSegment amount
        (CarrierNodeSourceKeys.word
          (CarrierNodeSourceKeys.taggedKey
              (route, segment, translate) 2,
            second)) =
      CarrierNodeSourceKeys.word
        (CarrierNodeSourceKeys.taggedKey
            (route, segment, translate) (2 + amount),
          second) := by
  simp [CarrierNodeSourceKeys.word, CarrierNodeSourceKeys.taggedKey,
    CarrierKeyWords.word, Nat.add_assoc]

@[simp] theorem crossingSideTag_eq_left_add_increment
    (side : CrossingSide) :
    CarrierNodeSourceKeys.crossingSideTag side =
      2 + sourceSideIncrement side := by
  cases side <;> rfl

/-- Starting from the canonical left-boundary pair, the fixed unary
increment produces exactly the compact source pair of the requested side. -/
theorem retagFirstSegment_crossingPair
    (crossing : CrossingRecord) (side : CrossingSide) :
    retagFirstSegment (sourceSideIncrement side)
        (CarrierNodeSourceKeys.word
          (RetainedCompactAtomWords.crossingPair crossing)) =
      CarrierNodeSourceKeys.word
        (RetainedCompactAtomWords.carrierPair
          (.boundary ⟨crossing, side⟩)) := by
  change retagFirstSegment (sourceSideIncrement side)
      (CarrierNodeSourceKeys.word
        (CarrierNodeSourceKeys.taggedKey
            (crossing.first.routeIndex, crossing.first.segmentIndex,
              crossing.firstTranslate) 2,
          (crossing.second.routeIndex, crossing.second.segmentIndex,
            crossing.secondTranslate))) =
    CarrierNodeSourceKeys.word
      (CarrierNodeSourceKeys.taggedKey
          (crossing.first.routeIndex, crossing.first.segmentIndex,
            crossing.firstTranslate)
          (CarrierNodeSourceKeys.crossingSideTag side),
        (crossing.second.routeIndex, crossing.second.segmentIndex,
          crossing.secondTranslate))
  rw [crossingSideTag_eq_left_add_increment]
  exact retagFirstSegment_sourceKeyWord
    (sourceSideIncrement side)
    crossing.first.routeIndex
    crossing.first.segmentIndex
    crossing.firstTranslate
    (crossing.second.routeIndex, crossing.second.segmentIndex,
      crossing.secondTranslate)

end CrossoverCompactAtomWords
end LeanTrominoes.PeriodicOrthocrossing
