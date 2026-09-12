/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseVertexCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalClauseGadgetOriginIndexSemantics

/-! # Native coordinate compiler for the actual clause-triple suffix -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing
open PeriodicPlanarOneInThreeToThreeDM PlanarThreeDM

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Expand the nine clause triples at each compiled clause origin. -/
def directSourceFinalClauseTripleCoordinates (horizontal keepPositive : Bool)
    (symbols : List encoding.Γ) : List Nat :=
  directSourceFinalClauseVertexCoordinates decider
    (allClauseSets.map X3CClauseOrthogonal.setPosition) horizontal keepPositive symbols

noncomputable def directSourceFinalClauseTripleCoordinatesComputableInPolyTime
    (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalClauseTripleCoordinates decider horizontal keepPositive) :=
  directSourceFinalClauseVertexCoordinatesComputableInPolyTime decider _ horizontal keepPositive

/-- The compiler preserves the canonical clause-major, triple-minor order. -/
theorem directSourceFinalClauseTripleCoordinates_eq_horizontal
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalClauseTripleCoordinates decider horizontal keepPositive symbols =
      (horizontalThreeDMClauseTriplePositionsComputed
        (PolySpaceCompiler.formulaOfSymbols decider symbols)).map
          (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)) := by
  unfold directSourceFinalClauseTripleCoordinates
  rw [directSourceFinalClauseVertexCoordinates_eq_horizontal,
    ← horizontalClauseGadgetOrigins_clauseTriplePositions]
  simp only [List.map_flatMap, List.map_map, Function.comp_def]

/-- An unconditional compiler for the actual semantic coordinate column. -/
noncomputable def directSourceFinalHorizontalClauseTripleCoordinatesComputableInPolyTime
    (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun symbols => (horizontalThreeDMClauseTriplePositionsComputed
        (PolySpaceCompiler.formulaOfSymbols decider symbols)).map
          (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive))) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (directSourceFinalClauseTripleCoordinatesComputableInPolyTime decider horizontal keepPositive)
    (fun symbols => congrArg UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalClauseTripleCoordinates_eq_horizontal decider horizontal keepPositive symbols))

@[simp] theorem directSourceFinalClauseTripleCoordinates_length
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalClauseTripleCoordinates decider horizontal keepPositive symbols).length =
      (horizontalRoutedFormulaComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).clauses.length * 9 := by
  rw [directSourceFinalClauseTripleCoordinates, directSourceFinalClauseVertexCoordinates_length,
    List.length_map]
  rfl

end LeanTrominoes.PeriodicCNFStripReduction
end
