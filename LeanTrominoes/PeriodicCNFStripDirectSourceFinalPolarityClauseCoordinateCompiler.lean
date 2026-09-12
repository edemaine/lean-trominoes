/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalHeaderCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalComposedClauseOriginCompiler
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceSubdivisionPositions

/-! # Complete affine clause-coordinate compiler through polarity normalization -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
open HorizontalRoutedRouteHeader PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- Main clauses retain their origin; complement clauses use point two. -/
def polarityClauseOffset (header : PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader.Header) : Cell :=
  match header.polarity.operation with
  | .compatible | .incompatible => (0, 0)
  | .complementFresh | .complementOriginal => Cell.scale 2 (sourceFirstDirection header).step

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

noncomputable local instance polarityClauseCoordinateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
attribute [local instance] directSourceVariableDecidableEqInstance

/-- Exact scaled clause origins plus the finite polarity-clause offset. -/
def directSourceFinalPolarityClauseCoordinates (horizontal keepPositive : Bool)
    (symbols : List encoding.Γ) : List Nat :=
  SignedUnaryCoordinateRefinement.values 3 keepPositive
    (fun positive => directSourceFinalComposedClauseOrigins decider horizontal positive symbols)
    (fun positive => directSourceFinalHeaderPointCoordinates decider polarityClauseOffset horizontal positive symbols)

noncomputable def directSourceFinalPolarityClauseCoordinatesComputableInPolyTime
    (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalPolarityClauseCoordinates decider horizontal keepPositive) := by
  unfold directSourceFinalPolarityClauseCoordinates
  exact SignedUnaryCoordinateRefinement.nativeListComputableInPolyTime 3 keepPositive
    (fun positive => directSourceFinalComposedClauseOrigins decider horizontal positive)
    (fun positive => directSourceFinalHeaderPointCoordinates decider polarityClauseOffset horizontal positive)
    (fun positive symbols => by rw [directSourceFinalComposedClauseOrigins_length, directSourceFinalComposedClauseOrigins_length])
    (fun positive symbols => by rw [directSourceFinalHeaderPointCoordinates_length, directSourceFinalComposedClauseOrigins_length])
    (fun positive => directSourceFinalComposedClauseOriginsComputableInPolyTime decider horizontal positive)
    (fun positive => directSourceFinalHeaderPointCoordinatesComputableInPolyTime decider polarityClauseOffset horizontal positive)

@[simp] theorem directSourceFinalPolarityClauseCoordinates_length
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalPolarityClauseCoordinates decider horizontal keepPositive symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  unfold directSourceFinalPolarityClauseCoordinates
  rw [SignedUnaryCoordinateRefinement.values_length_of_aligned _ _ _ _
    (fun positive => by rw [directSourceFinalComposedClauseOrigins_length, directSourceFinalComposedClauseOrigins_length])
    (fun positive => by rw [directSourceFinalHeaderPointCoordinates_length, directSourceFinalComposedClauseOrigins_length]),
    directSourceFinalComposedClauseOrigins_length]

/-- Each affine candidate is rooted at its own actual generated clause. -/
theorem directSourceFinalPolarityClauseCoordinates_lookup
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ)
    (index : Nat) (occurrence : SourceOccurrence)
    (lookup : (directSourceFinalOccurrences decider symbols)[index]? = some occurrence)
    (witness : OccurrenceWitness (directSourceFormula decider symbols) occurrence) :
    (directSourceFinalPolarityClauseCoordinates decider horizontal keepPositive symbols)[index]? =
      some (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
        (Cell.add (Cell.scale 3 witness.metadata.clause.position) (polarityClauseOffset occurrence.header))) := by
  unfold directSourceFinalPolarityClauseCoordinates
  rw [SignedUnaryCoordinateRefinement.values_lookup 3 keepPositive _ _ index
    (DelimitedDirectionDisplacement.component horizontal witness.metadata.clause.position)
    (DelimitedDirectionDisplacement.component horizontal (polarityClauseOffset occurrence.header))
    (fun positive => by simpa only [pointValue_bools] using
      directSourceFinalComposedClauseOrigins_lookup decider horizontal positive symbols index occurrence lookup witness)
    (fun positive => by simpa only [pointValue_bools] using
      directSourceFinalHeaderPointCoordinates_lookup decider polarityClauseOffset horizontal positive symbols index occurrence lookup)]
  rw [pointValue_bools, component_affine]
  rfl

end LeanTrominoes.PeriodicCNFStripReduction
end
