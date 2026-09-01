/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingBendNormalizedFallbackClockwiseRecordSemantics
import LeanTrominoes.RetainedAngularFanFinalBendRecordFamilySemantics
import LeanTrominoes.RetainedAngularFanFinalBendSourceClauseRecordSemantics

/-! # Decoded record semantics of one final retained bend -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicOrthocrossing

attribute [local instance]
  finalBendIndexedOccurrenceThreeOccurrenceDecidableEq

/-- The forward and backward semantic clauses of one physical bend decode to
the compiler's corresponding normalized four-route block. -/
theorem finalBendSourceClauseRecords_pair_eq_decodedBlock
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {routeBend : RouteBend}
    {forwardClauseIndex backwardClauseIndex : Nat}
    (forwardInput : FinalBendTaggedBendInput source (routeBend, true)
      forwardClauseIndex)
    (backwardInput : FinalBendTaggedBendInput source (routeBend, false)
      backwardClauseIndex) :
    finalBendSourceClauseRecordsAt (PeriodicThreeSATThree.formula source)
          ((routeBend, true), forwardClauseIndex) ++
        finalBendSourceClauseRecordsAt (PeriodicThreeSATThree.formula source)
          ((routeBend, false), backwardClauseIndex) =
      BinaryRouteTailRecordClockwiseRelabel.decodedBlockRecords
        (finalBendNormalizedRecordBlockAt
          (PeriodicThreeSATThree.formula source) routeBend
          forwardClauseIndex backwardClauseIndex) := by
  unfold finalBendSourceClauseRecordsAt
    finalBendNormalizedRecordBlockAt
  rw [forwardInput.sourceClauseRecords_eq_modelTails,
    backwardInput.sourceClauseRecords_eq_modelTails,
    BendNormalizedFallbackRouteTailRecords.decodedBlockRecords_block]
  rfl

end PeriodicEightOccurrenceSplit
end LeanTrominoes
