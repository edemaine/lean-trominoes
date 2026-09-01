/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalBendRecordBlockSemantics

/-! # Decoded-record semantics of final retained-bend families -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNFStripReduction
open PeriodicOrthocrossing

attribute [local instance]
  finalBendIndexedOccurrenceThreeOccurrenceDecidableEq

/-- Per-bend correctness lifts to every indexed retained-bend family. -/
theorem finalBendSourceClauseRecordsFrom_eq_decodedRecords
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (sourceInput : FinalBendSourceInput source)
    (routeBends : List RouteBend)
    (start : Nat)
    (indexed : ∀ tagged ∈ (routeBends.product [true, false]).zipIdx start,
      finalBendTaggedBendIndexed source tagged.1 tagged.2) :
    finalBendSourceClauseRecordsFrom
        (PeriodicThreeSATThree.formula source) start routeBends =
      BinaryRouteTailRecordClockwiseRelabel.decodedRecords
        (finalBendNormalizedRecordBlocksFrom
          (PeriodicThreeSATThree.formula source) start routeBends) := by
  induction routeBends generalizing start with
  | nil => rfl
  | cons routeBend routeBends induction =>
      have forwardMember :
          ((routeBend, true), start) ∈
            ((routeBend :: routeBends).product [true, false]).zipIdx start := by
        simp [List.product]
      have backwardMember :
          ((routeBend, false), start + 1) ∈
            ((routeBend :: routeBends).product [true, false]).zipIdx start := by
        simp [List.product]
      let forwardInput : FinalBendTaggedBendInput source (routeBend, true)
          start :=
        { sourceInput := sourceInput
          taggedBendIndexed := indexed _ forwardMember }
      let backwardInput : FinalBendTaggedBendInput source (routeBend, false)
          (start + 1) :=
        { sourceInput := sourceInput
          taggedBendIndexed := indexed _ backwardMember }
      have tailIndexed :
          ∀ tagged ∈ (routeBends.product [true, false]).zipIdx (start + 2),
            finalBendTaggedBendIndexed source tagged.1 tagged.2 := by
        intro tagged taggedMember
        apply indexed tagged
        simpa [List.product, Nat.add_assoc] using
          (Or.inr (Or.inr taggedMember))
      rw [finalBendSourceClauseRecordsFrom,
        finalBendNormalizedRecordBlocksFrom,
        BinaryRouteTailRecordClockwiseRelabel.decodedRecords,
        List.flatMap_cons]
      rw [show
        finalBendSourceClauseRecordsAt
              (PeriodicThreeSATThree.formula source)
              ((routeBend, true), start) ++
            finalBendSourceClauseRecordsAt
              (PeriodicThreeSATThree.formula source)
              ((routeBend, false), start + 1) =
          BinaryRouteTailRecordClockwiseRelabel.decodedBlockRecords
            (finalBendNormalizedRecordBlockAt
              (PeriodicThreeSATThree.formula source) routeBend start
              (start + 1)) by
        exact finalBendSourceClauseRecords_pair_eq_decodedBlock
          forwardInput backwardInput]
      rw [induction (start + 2) tailIndexed]
      rfl

end PeriodicEightOccurrenceSplit
end LeanTrominoes
