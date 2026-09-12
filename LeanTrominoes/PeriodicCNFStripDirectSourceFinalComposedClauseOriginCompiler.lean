/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalTemplateClauseCoordinateCompiler
import LeanTrominoes.SignedUnaryCoordinateRefinementLookup
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceClausePositions

/-! # Actual composed Figure 9 clause coordinates from compiled affine fields -/

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
clause offset is added to the resulting factor-72 clearance origin. -/
def directSourceFinalComposedClauseOrigins (horizontal keepPositive : Bool) (symbols : List encoding.Γ) : List Nat :=
  SignedUnaryCoordinateRefinement.values 72 keepPositive
    (fun positive => directSourceFinalOccurrenceClearanceClauseOrigins decider horizontal positive symbols)
    (fun positive => directSourceFinalTemplateClauseCoordinates decider horizontal positive symbols)

noncomputable def directSourceFinalComposedClauseOriginsComputableInPolyTime (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalComposedClauseOrigins decider horizontal keepPositive) := by
  unfold directSourceFinalComposedClauseOrigins
  exact SignedUnaryCoordinateRefinement.nativeListComputableInPolyTime 72 keepPositive
    (fun positive => directSourceFinalOccurrenceClearanceClauseOrigins decider horizontal positive)
    (fun positive => directSourceFinalTemplateClauseCoordinates decider horizontal positive)
    (fun positive symbols => by rw [directSourceFinalOccurrenceClearanceClauseOrigins_length,
      directSourceFinalOccurrenceClearanceClauseOrigins_length])
    (fun positive symbols => by rw [directSourceFinalTemplateClauseCoordinates_length,
      directSourceFinalOccurrenceClearanceClauseOrigins_length])
    (fun positive => directSourceFinalOccurrenceClearanceClauseOriginsComputableInPolyTime decider horizontal positive)
    (fun positive => directSourceFinalTemplateClauseCoordinatesComputableInPolyTime decider horizontal positive)

@[simp] theorem directSourceFinalComposedClauseOrigins_length (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalComposedClauseOrigins decider horizontal keepPositive symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalComposedClauseOrigins
  rw [SignedUnaryCoordinateRefinement.values_length_of_aligned _ _ _ _
    (fun positive => by rw [directSourceFinalOccurrenceClearanceClauseOrigins_length,
      directSourceFinalOccurrenceClearanceClauseOrigins_length])
    (fun positive => by rw [directSourceFinalTemplateClauseCoordinates_length,
      directSourceFinalOccurrenceClearanceClauseOrigins_length]), directSourceFinalOccurrenceClearanceClauseOrigins_length]

/-- Every emitted coordinate is the actual stored generated-clause position
carried by the occurrence's complete Figure 9 metadata witness. -/
theorem directSourceFinalComposedClauseOrigins_lookup (horizontal keepPositive : Bool) (symbols : List encoding.Γ)
    (index : Nat) (occurrence : SourceOccurrence)
    (lookup : (directSourceFinalOccurrences decider symbols)[index]? = some occurrence)
    (witness : OccurrenceWitness (directSourceFormula decider symbols) occurrence) :
    (directSourceFinalComposedClauseOrigins decider horizontal keepPositive symbols)[index]? =
      some (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive) witness.metadata.clause.position) := by
  unfold directSourceFinalComposedClauseOrigins
  rw [SignedUnaryCoordinateRefinement.values_lookup 72 keepPositive _ _ index
    (DelimitedDirectionDisplacement.component horizontal witness.metadata.sourceClause.position)
    (DelimitedDirectionDisplacement.component horizontal
      (templateClausePosition witness.metadata.parentProfileCoordinate.profile witness.metadata.localClauseIndex))
    (fun positive => by simpa only [pointValue_bools] using
      directSourceFinalOccurrenceClearanceClauseOrigins_lookup decider horizontal positive symbols index occurrence lookup witness)
    (fun positive => by simpa only [pointValue_bools] using
      directSourceFinalTemplateClauseCoordinates_lookup decider horizontal positive symbols index occurrence lookup witness)]
  have lengthEq : witness.metadata.sourceClause.literals.length = witness.refinedClause.literals.length := by
    rw [witness.metadataSource, PositionedPeriodicClause.scale_literals, PositionedPeriodicCNF.orderClauseByRouteDirection_length]
  have nonempty : witness.metadata.sourceClause.literals ≠ [] := by
    intro empty
    have zero : witness.refinedClause.literals.length = 0 := by rw [← lengthEq, empty]; rfl
    exact witness.refinedNonempty (List.length_eq_zero_iff.mp zero)
  have width : witness.metadata.sourceClause.literals.length ≤ 3 := by rw [lengthEq]; exact witness.refinedWidth
  have positionEq := witness.metadata.position_eq_template
    (retainedFigureNineClearancePositionedFormula (directSourceFormula decider symbols))
    (List.mem_iff_getElem?.mpr ⟨occurrence.generatedClauseIndex, witness.metadataLookup⟩) nonempty width
  change witness.metadata.clause.position = Cell.add (Cell.scale 72 witness.metadata.sourceClause.position)
    (templateClausePosition witness.metadata.parentProfileCoordinate.profile witness.metadata.localClauseIndex) at positionEq
  rw [positionEq, pointValue_bools, component_affine]
  rfl

/-- The same compiled fields are canonical clause origins after final
clockwise ordering and variable gauging, at the witness's generated index. -/
theorem directSourceFinalComposedClauseOrigins_finalGauged_lookup
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
    (clause : PositionedPeriodicClause
      (OneInThreeNoUnitVariable (PeriodicPlanarOneInThreeThreeRawVariable Variable)))
    (member : (clause, occurrence.generatedClauseIndex) ∈
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        (directSourceFormula decider symbols) sourceLocal sourceWidth sourceOccurrences sourceNonempty).clauses.zipIdx) :
    (directSourceFinalComposedClauseOrigins decider horizontal keepPositive symbols)[index]? =
      some (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
        (PositionedPeriodicCNF.canonicalClausePosition
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
            (directSourceFormula decider symbols)) clause)) := by
  rw [witness.finalGaugedClausePosition sourceLocal sourceWidth sourceOccurrences sourceNonempty clause member]
  exact directSourceFinalComposedClauseOrigins_lookup decider horizontal keepPositive symbols index occurrence lookup witness

end LeanTrominoes.PeriodicCNFStripReduction
end
