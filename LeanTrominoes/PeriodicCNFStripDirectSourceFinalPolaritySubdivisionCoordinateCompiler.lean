/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalHeaderCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalComposedClauseOriginCompiler
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceSubdivisionPositions

/-! # Compiled affine positions of polarity subdivision vertices -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
open HorizontalRoutedRouteHeader PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- Fixed many initial unit steps, selected by the finite source header. -/
def polaritySubdivisionOffset (steps : Nat) (header : PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader.Header) : Cell :=
  Cell.scale steps (sourceFirstDirection header).step

private theorem pointValue_bools (horizontal positive : Bool) (point : Cell) :
    CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal positive) point =
      SignedUnaryCoordinateRefinement.field positive (DelimitedDirectionDisplacement.component horizontal point) := by
  cases horizontal <;> cases positive <;> rfl

private theorem component_affine (horizontal : Bool) (origin offset : Cell) :
    DelimitedDirectionDisplacement.component horizontal (Cell.add (Cell.scale 3 origin) offset) =
      (3 : Int) * DelimitedDirectionDisplacement.component horizontal origin +
        DelimitedDirectionDisplacement.component horizontal offset := by
  cases horizontal <;> rfl

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance subdivisionCoordinateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
attribute [local instance] directSourceVariableDecidableEqInstance

/-- Threefold source-clause coordinates plus a finite initial-step offset.
Steps one and two are the new fresh variable and complement clause. -/
def directSourceFinalPolaritySubdivisionCoordinates (steps : Nat) (horizontal keepPositive : Bool)
    (symbols : List encoding.Γ) : List Nat :=
  SignedUnaryCoordinateRefinement.values 3 keepPositive
    (fun positive => directSourceFinalComposedClauseOrigins decider horizontal positive symbols)
    (fun positive => directSourceFinalHeaderPointCoordinates decider (polaritySubdivisionOffset steps) horizontal positive symbols)

noncomputable def directSourceFinalPolaritySubdivisionCoordinatesComputableInPolyTime
    (steps : Nat) (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalPolaritySubdivisionCoordinates decider steps horizontal keepPositive) := by
  unfold directSourceFinalPolaritySubdivisionCoordinates
  exact SignedUnaryCoordinateRefinement.nativeListComputableInPolyTime 3 keepPositive
    (fun positive => directSourceFinalComposedClauseOrigins decider horizontal positive)
    (fun positive => directSourceFinalHeaderPointCoordinates decider (polaritySubdivisionOffset steps) horizontal positive)
    (fun positive symbols => by rw [directSourceFinalComposedClauseOrigins_length, directSourceFinalComposedClauseOrigins_length])
    (fun positive symbols => by rw [directSourceFinalHeaderPointCoordinates_length, directSourceFinalComposedClauseOrigins_length])
    (fun positive => directSourceFinalComposedClauseOriginsComputableInPolyTime decider horizontal positive)
    (fun positive => directSourceFinalHeaderPointCoordinatesComputableInPolyTime decider (polaritySubdivisionOffset steps) horizontal positive)

@[simp] theorem directSourceFinalPolaritySubdivisionCoordinates_length
    (steps : Nat) (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalPolaritySubdivisionCoordinates decider steps horizontal keepPositive symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalPolaritySubdivisionCoordinates
  rw [SignedUnaryCoordinateRefinement.values_length_of_aligned _ _ _ _
    (fun positive => by rw [directSourceFinalComposedClauseOrigins_length, directSourceFinalComposedClauseOrigins_length])
    (fun positive => by rw [directSourceFinalHeaderPointCoordinates_length, directSourceFinalComposedClauseOrigins_length]),
    directSourceFinalComposedClauseOrigins_length]

/-- Each affine candidate is rooted at its own actual generated clause. -/
theorem directSourceFinalPolaritySubdivisionCoordinates_lookup
    (steps : Nat) (horizontal keepPositive : Bool) (symbols : List encoding.Γ)
    (index : Nat) (occurrence : SourceOccurrence)
    (lookup : (directSourceFinalOccurrences decider symbols)[index]? = some occurrence)
    (witness : OccurrenceWitness (directSourceFormula decider symbols) occurrence) :
    (directSourceFinalPolaritySubdivisionCoordinates decider steps horizontal keepPositive symbols)[index]? =
      some (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
        (Cell.add (Cell.scale 3 witness.metadata.clause.position) (polaritySubdivisionOffset steps occurrence.header))) := by
  unfold directSourceFinalPolaritySubdivisionCoordinates
  rw [SignedUnaryCoordinateRefinement.values_lookup 3 keepPositive _ _ index
    (DelimitedDirectionDisplacement.component horizontal witness.metadata.clause.position)
    (DelimitedDirectionDisplacement.component horizontal (polaritySubdivisionOffset steps occurrence.header))
    (fun positive => by simpa only [pointValue_bools] using
      directSourceFinalComposedClauseOrigins_lookup decider horizontal positive symbols index occurrence lookup witness)
    (fun positive => by simpa only [pointValue_bools] using
      directSourceFinalHeaderPointCoordinates_lookup decider (polaritySubdivisionOffset steps) horizontal positive symbols index occurrence lookup)]
  rw [pointValue_bools, component_affine]
  rfl

/-- The first two compiled candidates equal the actual point selectors of
the refined route at this same gauged clause/literal incidence. -/
theorem directSourceFinalPolaritySubdivisionCoordinates_one_two_lookup
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
    (clauseMember : (clause, occurrence.generatedClauseIndex) ∈
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        (directSourceFormula decider symbols) sourceLocal sourceWidth sourceOccurrences sourceNonempty).clauses.zipIdx)
    (literal : PeriodicLiteral
      (OneInThreeNoUnitVariable (PeriodicPlanarOneInThreeThreeRawVariable Variable)))
    (literalMember : (literal, occurrence.header.polarity.indexed.sourceLiteralIndex) ∈ clause.literals.zipIdx) :
    let points := refinedRoute
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes
        (directSourceFormula decider symbols) sourceLocal sourceWidth sourceOccurrences sourceNonempty)
      occurrence.generatedClauseIndex occurrence.header.polarity.indexed.sourceLiteralIndex
    (directSourceFinalPolaritySubdivisionCoordinates decider 1 horizontal keepPositive symbols)[index]? =
        some (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive) (points.getD 1 (0, 0))) ∧
      (directSourceFinalPolaritySubdivisionCoordinates decider 2 horizontal keepPositive symbols)[index]? =
        some (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive) (points.getD 2 (0, 0))) := by
  dsimp only
  obtain ⟨first, second⟩ := witness.polaritySubdivisionPositions sourceLocal sourceWidth sourceOccurrences sourceNonempty
    clause clauseMember literal literalMember
  rw [first, second]
  constructor
  · simpa only [polaritySubdivisionOffset, Nat.cast_one, Cell.scale, one_mul, Prod.eta] using
      directSourceFinalPolaritySubdivisionCoordinates_lookup decider 1 horizontal keepPositive symbols index occurrence lookup witness
  · exact directSourceFinalPolaritySubdivisionCoordinates_lookup decider 2 horizontal keepPositive symbols index occurrence lookup witness

end LeanTrominoes.PeriodicCNFStripReduction
end
