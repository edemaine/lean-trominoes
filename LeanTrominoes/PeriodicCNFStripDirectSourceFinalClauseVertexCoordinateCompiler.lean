/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseGadgetOriginCompiler
import LeanTrominoes.SignedUnaryCoordinateTableExpansion

/-! # Exact coordinates from a fixed vertex table at every actual clause -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing

private theorem pointValue_function (horizontal positive : Bool) :
    CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal positive) =
      (fun point => SignedUnaryCoordinateRefinement.field positive
        (DelimitedDirectionDisplacement.component horizontal point)) := by
  funext point
  cases horizontal <;> cases positive <;> rfl

private theorem component_add (horizontal : Bool) (origin offset : Cell) :
    DelimitedDirectionDisplacement.component horizontal (Cell.add origin offset) =
      DelimitedDirectionDisplacement.component horizontal origin +
        DelimitedDirectionDisplacement.component horizontal offset := by
  cases horizontal <;> rfl

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Emit each finite local vertex table once per clause, in clause-major order. -/
def directSourceFinalClauseVertexCoordinates (table : List Cell) (horizontal keepPositive : Bool)
    (symbols : List encoding.Γ) : List Nat :=
  SignedUnaryCoordinateTableExpansion.values
    (table.map (DelimitedDirectionDisplacement.component horizontal)) keepPositive
    (fun positive => directSourceFinalClauseGadgetOriginCoordinates decider horizontal positive symbols)

noncomputable def directSourceFinalClauseVertexCoordinatesComputableInPolyTime
    (table : List Cell) (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalClauseVertexCoordinates decider table horizontal keepPositive) := by
  unfold directSourceFinalClauseVertexCoordinates
  exact SignedUnaryCoordinateTableExpansion.nativeListComputableInPolyTime _ keepPositive
    (fun positive => directSourceFinalClauseGadgetOriginCoordinates decider horizontal positive)
    (fun positive symbols => by rw [directSourceFinalClauseGadgetOriginCoordinates_length,
      directSourceFinalClauseGadgetOriginCoordinates_length])
    (fun positive => directSourceFinalClauseGadgetOriginCoordinatesComputableInPolyTime decider horizontal positive)

theorem directSourceFinalClauseVertexCoordinates_eq_horizontal
    (table : List Cell) (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalClauseVertexCoordinates decider table horizontal keepPositive symbols =
      (horizontalClauseGadgetOrigins (PolySpaceCompiler.formulaOfSymbols decider symbols)).flatMap
        (fun origin => table.map fun offset =>
          CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive) (Cell.add origin offset)) := by
  unfold directSourceFinalClauseVertexCoordinates
  simp only [directSourceFinalClauseGadgetOriginCoordinates_eq_horizontal, pointValue_function]
  rw [SignedUnaryCoordinateTableExpansion.values_map]
  simp only [List.map_map, Function.comp_def, component_add]

@[simp] theorem directSourceFinalClauseVertexCoordinates_length
    (table : List Cell) (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalClauseVertexCoordinates decider table horizontal keepPositive symbols).length =
      (horizontalRoutedFormulaComputed (PolySpaceCompiler.formulaOfSymbols decider symbols)).clauses.length * table.length := by
  unfold directSourceFinalClauseVertexCoordinates
  rw [SignedUnaryCoordinateTableExpansion.values_length _ _ _
    (fun positive => by rw [directSourceFinalClauseGadgetOriginCoordinates_length,
      directSourceFinalClauseGadgetOriginCoordinates_length]),
    directSourceFinalClauseGadgetOriginCoordinates_length, List.length_map]

end LeanTrominoes.PeriodicCNFStripReduction
end
