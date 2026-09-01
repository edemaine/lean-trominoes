/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendNormalizedBlockSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendBatchedRecordSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendIndexedPresentation
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierSourceInput
import LeanTrominoes.RetainedAngularFanFinalBendDecodedRecordSemantics

/-! # Decoded-record semantics of direct final-bend blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendDecodedRecordStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local implicit_reducible]
  directSourceFinalOriginalBaseDecidableEq
attribute [local instance]
  directSourceFinalOriginalBaseDecidableEq

local instance directFinalBendDecodedRecordVariableDecidableEq :
    DecidableEq Variable :=
  directSourceFinalOriginalVariableDecidableEq

/-- Package the elementary direct source facts under the equality instance
used by the final-bend semantic presentation. -/
private noncomputable def directThreeCNFSourceFinalBendInput
    (symbols : List encoding.Γ) :
    FinalBendSourceInput (directThreeCNFSourceFormula decider symbols) where
  sourceFacts :=
    { nonemptyFacts :=
        { widthFacts :=
            { localFacts :=
                { sourceLocal :=
                    PeriodicThreeCNF.formula_isLocal
                      (formulaOfSymbols_sourceAdmissible
                        decider symbols).2.1 }
              sourceWidth := PeriodicThreeCNF.formula_widthAtMostThree _ }
          sourceClausesNonempty :=
            PeriodicThreeCNF.formula_clausesNonempty _
              (formulaOfSymbols_clauses_nonempty decider symbols) }
      positiveOffsets :=
        directThreeCNFSource_occurrenceIncidences_positiveOffsets
          decider symbols }

private theorem directSourceFinalBendSourceClauseRecords_eq_semanticDecoded
    (symbols : List encoding.Γ) :
    @finalBendSourceClauseRecordsFrom Variable
        (@PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
          (ThreeCNFVariable Nat) directSourceFinalOriginalBaseDecidableEq)
        (PeriodicThreeSATThree.formula
          (directThreeCNFSourceFormula decider symbols))
        (directSourceFinalBendStart decider symbols)
        (@baseRouteBends Variable
          (@PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
            (ThreeCNFVariable Nat) directSourceFinalOriginalBaseDecidableEq)
          (PeriodicThreeSATThree.formula
            (directThreeCNFSourceFormula decider symbols))) =
      BinaryRouteTailRecordClockwiseRelabel.decodedRecords
        (@finalBendNormalizedRecordBlocksFrom Variable
          (@PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
            (ThreeCNFVariable Nat) directSourceFinalOriginalBaseDecidableEq)
          (PeriodicThreeSATThree.formula
            (directThreeCNFSourceFormula decider symbols))
          (directSourceFinalBendStart decider symbols)
          (@baseRouteBends Variable
            (@PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
              (ThreeCNFVariable Nat) directSourceFinalOriginalBaseDecidableEq)
            (PeriodicThreeSATThree.formula
              (directThreeCNFSourceFormula decider symbols)))) := by
  exact @finalBendSourceClauseRecordsFrom_eq_decodedRecords
    (ThreeCNFVariable Nat) directSourceFinalOriginalBaseDecidableEq
    (directThreeCNFSourceFormula decider symbols)
    (directThreeCNFSourceFinalBendInput decider symbols)
    (@baseRouteBends Variable
      (@PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
        (ThreeCNFVariable Nat) directSourceFinalOriginalBaseDecidableEq)
      (PeriodicThreeSATThree.formula
        (directThreeCNFSourceFormula decider symbols)))
    (directSourceFinalBendStart decider symbols)
    (directSourceFinalBendIndexedPresentation_indexed decider symbols)

/-- Expanded semantic records of the direct bend family are exactly the
clockwise decoding of its declarative normalized compiler blocks. -/
theorem directSourceFinalBendSourceClauseRecords_eq_decodedRecords
    (symbols : List encoding.Γ) :
    finalBendSourceClauseRecordsFrom
        (directSourceFinalNormalizedFormula decider symbols)
        (directSourceFinalBendStart decider symbols)
        (baseRouteBends
          (directSourceFinalNormalizedFormula decider symbols)) =
      BinaryRouteTailRecordClockwiseRelabel.decodedRecords
        (directSourceFinalBendNormalizedFallbackRecordBlocks
          decider symbols) := by
  rw [directSourceFinalBendNormalizedFallbackRecordBlocks_eq_semantic
    decider symbols]
  unfold directSourceFinalNormalizedFormula
  let source := directThreeCNFSourceFormula decider symbols
  let retained := PeriodicThreeSATThree.formula source
  let routeBendsWith (equality : DecidableEq Variable) :=
    @baseRouteBends Variable equality retained
  let statement (equality : DecidableEq Variable) : Prop :=
    @finalBendSourceClauseRecordsFrom Variable equality retained
        (directSourceFinalBendStart decider symbols)
        (routeBendsWith equality) =
      BinaryRouteTailRecordClockwiseRelabel.decodedRecords
        (@finalBendNormalizedRecordBlocksFrom Variable equality retained
          (directSourceFinalBendStart decider symbols)
          (routeBendsWith equality))
  let derivedEquality : DecidableEq Variable :=
    @PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
      (ThreeCNFVariable Nat) directSourceFinalOriginalBaseDecidableEq
  have derived : statement derivedEquality := by
    simpa only [statement, routeBendsWith, source, retained,
      derivedEquality] using
      directSourceFinalBendSourceClauseRecords_eq_semanticDecoded
        decider symbols
  have equalityIrrel := decidableEq_application_irrel statement
    derivedEquality directSourceFinalOriginalVariableDecidableEq
  change statement directSourceFinalOriginalVariableDecidableEq
  exact equalityIrrel ▸ derived

/-- The existing batched semantic input therefore equals the decoding of the
declarative normalized bend blocks. -/
theorem directSourceFinalBendBatchedSemanticRecords_eq_decodedRecords
    (symbols : List encoding.Γ) :
    HorizontalRoutedRouteTailRecord.batchedRecords
        (retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
          (directSourceFormula decider symbols)
          (directSourceFinalBendStart decider symbols)
          (directSourceFinalBendClauses decider symbols)) =
      BinaryRouteTailRecordClockwiseRelabel.decodedRecords
        (directSourceFinalBendNormalizedFallbackRecordBlocks
          decider symbols) :=
  (directSourceFinalBendBatchedSemanticRecords_eq_sourceClauseRecords
    decider symbols).trans
      (directSourceFinalBendSourceClauseRecords_eq_decodedRecords
        decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
