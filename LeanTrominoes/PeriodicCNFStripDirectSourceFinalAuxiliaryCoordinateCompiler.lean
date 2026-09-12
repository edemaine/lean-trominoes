/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalTemplateVariableCoordinateCompiler
import LeanTrominoes.SignedUnaryCoordinateRefinementLookup
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceAuxiliaryPositions

/-! # Actual Figure 9 auxiliary coordinates from compiled affine fields -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
open PlanarOneInThreeNoUnitsFigureNine

private theorem pointValue_bools (horizontal positive : Bool) (point : Cell) :
    CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal positive) point =
      SignedUnaryCoordinateRefinement.field positive (DelimitedDirectionDisplacement.component horizontal point) := by
  cases horizontal <;> cases positive <;> rfl

private theorem component_affine (horizontal : Bool) (origin offset : Cell) :
    DelimitedDirectionDisplacement.component horizontal (Cell.add (Cell.scale 72 origin) offset) =
      (72 : Int) * DelimitedDirectionDisplacement.component horizontal origin +
        DelimitedDirectionDisplacement.component horizontal offset := by
  cases horizontal <;> rfl

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance composedOriginStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
attribute [local instance] directSourceVariableDecidableEqInstance

/-- Figure 9 scales by twelve and unit elimination by six. The finite local
variable offset is added to the resulting factor-72 clearance origin. -/
def directSourceFinalAuxiliaryCoordinates (horizontal keepPositive : Bool) (symbols : List encoding.Γ) : List Nat :=
  SignedUnaryCoordinateRefinement.values 72 keepPositive
    (fun positive => directSourceFinalOccurrenceClearanceClauseOrigins decider horizontal positive symbols)
    (fun positive => directSourceFinalTemplateVariableCoordinates decider horizontal positive symbols)

noncomputable def directSourceFinalAuxiliaryCoordinatesComputableInPolyTime (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalAuxiliaryCoordinates decider horizontal keepPositive) := by
  unfold directSourceFinalAuxiliaryCoordinates
  exact SignedUnaryCoordinateRefinement.nativeListComputableInPolyTime 72 keepPositive
    (fun positive => directSourceFinalOccurrenceClearanceClauseOrigins decider horizontal positive)
    (fun positive => directSourceFinalTemplateVariableCoordinates decider horizontal positive)
    (fun positive symbols => by rw [directSourceFinalOccurrenceClearanceClauseOrigins_length,
      directSourceFinalOccurrenceClearanceClauseOrigins_length])
    (fun positive symbols => by rw [directSourceFinalTemplateVariableCoordinates_length,
      directSourceFinalOccurrenceClearanceClauseOrigins_length])
    (fun positive => directSourceFinalOccurrenceClearanceClauseOriginsComputableInPolyTime decider horizontal positive)
    (fun positive => directSourceFinalTemplateVariableCoordinatesComputableInPolyTime decider horizontal positive)

@[simp] theorem directSourceFinalAuxiliaryCoordinates_length (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalAuxiliaryCoordinates decider horizontal keepPositive symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalAuxiliaryCoordinates
  rw [SignedUnaryCoordinateRefinement.values_length_of_aligned _ _ _ _
    (fun positive => by rw [directSourceFinalOccurrenceClearanceClauseOrigins_length,
      directSourceFinalOccurrenceClearanceClauseOrigins_length])
    (fun positive => by rw [directSourceFinalTemplateVariableCoordinates_length,
      directSourceFinalOccurrenceClearanceClauseOrigins_length]), directSourceFinalOccurrenceClearanceClauseOrigins_length]

/-- Each candidate is the affine position of this header's finite variable
role over its own clearance parent. Only auxiliary roles use this column. -/
theorem directSourceFinalAuxiliaryCoordinates_lookup (horizontal keepPositive : Bool) (symbols : List encoding.Γ)
    (index : Nat) (occurrence : SourceOccurrence)
    (lookup : (directSourceFinalOccurrences decider symbols)[index]? = some occurrence)
    (witness : OccurrenceWitness (directSourceFormula decider symbols) occurrence) :
    (directSourceFinalAuxiliaryCoordinates decider horizontal keepPositive symbols)[index]? =
      some (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
        (Cell.add (Cell.scale 72 witness.metadata.sourceClause.position)
          (headerTemplateVariablePosition occurrence.header))) := by
  unfold directSourceFinalAuxiliaryCoordinates
  rw [SignedUnaryCoordinateRefinement.values_lookup 72 keepPositive _ _ index
    (DelimitedDirectionDisplacement.component horizontal witness.metadata.sourceClause.position)
    (DelimitedDirectionDisplacement.component horizontal (headerTemplateVariablePosition occurrence.header))
    (fun positive => by simpa only [pointValue_bools] using
      directSourceFinalOccurrenceClearanceClauseOrigins_lookup decider horizontal positive symbols index occurrence lookup witness)
    (fun positive => by simpa only [pointValue_bools] using
      directSourceFinalTemplateVariableCoordinates_lookup decider horizontal positive symbols index occurrence lookup)]
  rw [pointValue_bools, component_affine]
  rfl

/-- Auxiliary fields are the actual final gauged variable positions of the
same instantiated atom selected by the occurrence's template query. -/
theorem directSourceFinalAuxiliaryCoordinates_finalGauged_lookup
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ)
    (sourceLocal : (directSourceFormula decider symbols).IsLocal)
    (sourceWidth : (directSourceFormula decider symbols).WidthAtMost 3)
    (sourceOccurrences : @PeriodicCNF.OccurrencesAtMost Variable
      (@instBEqOfDecidableEq Variable directSourceVariableDecidableEqInstance) (by infer_instance) 3
      (directSourceFormula decider symbols))
    (sourceNonempty : ∀ clause ∈ (directSourceFormula decider symbols).clauses, clause ≠ [])
    (index : Nat) (occurrence : SourceOccurrence)
    (lookup : (directSourceFinalOccurrences decider symbols)[index]? = some occurrence)
    (witness : OccurrenceWitness (directSourceFormula decider symbols) occurrence)
    (auxiliary : FormulaShapeFigureNineRoutePrefix.sourceSlot?
      ((templateDrawingOfClauseProfile occurrence.header.figurePrefix.localQuery.1).incidenceAt
        occurrence.header.figurePrefix.localQuery.2).literal.1 = none) :
    let role := ((templateDrawingOfClauseProfile occurrence.header.figurePrefix.localQuery.1).incidenceAt
      occurrence.header.figurePrefix.localQuery.2).literal.1
    (directSourceFinalAuxiliaryCoordinates decider horizontal keepPositive symbols)[index]? =
      some (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
        ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          (directSourceFormula decider symbols)).position
          (instantiatedVariableMap witness.metadata.sourceClauseIndex witness.metadata.figureNineClauseStart
            witness.metadata.sourceClause role))) := by
  dsimp only
  rw [witness.finalGaugedAuxiliaryPosition sourceLocal sourceWidth sourceOccurrences sourceNonempty auxiliary]
  exact directSourceFinalAuxiliaryCoordinates_lookup decider horizontal keepPositive symbols index occurrence lookup witness

end LeanTrominoes.PeriodicCNFStripReduction
end
