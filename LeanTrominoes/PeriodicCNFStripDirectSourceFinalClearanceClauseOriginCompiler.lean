/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceClauseOriginCompiler
import LeanTrominoes.UnaryFieldConstantScaleCompiler

/-! # Exact clearance-clause origins beside the final occurrence stream -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail

private theorem pointValue_double (field : CarrierCrossingPointField.Field) (point : Cell) :
    CarrierCrossingPointField.pointValue field (Cell.scale 2 point) =
      CarrierCrossingPointField.pointValue field point * 2 := by
  rcases point with ⟨x, y⟩
  cases field <;> simp only [CarrierCrossingPointField.pointValue, CarrierCrossingPointField.horizontal,
    CarrierCrossingPointField.keepPositive, Cell.scale, Bool.false_eq_true, ↓reduceIte] <;> omega

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance clearanceOriginStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
attribute [local instance] directSourceVariableDecidableEqInstance

/-- Clockwise sorting preserves stored positions; clearance doubles them. -/
def directSourceFinalOccurrenceClearanceClauseOrigins (horizontal keepPositive : Bool) (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldConstantScale.values 2 (directSourceFinalOccurrenceClauseOrigins decider horizontal keepPositive symbols)

noncomputable def directSourceFinalOccurrenceClearanceClauseOriginsComputableInPolyTime (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalOccurrenceClearanceClauseOrigins decider horizontal keepPositive) := by
  unfold directSourceFinalOccurrenceClearanceClauseOrigins
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalOccurrenceClauseOriginsComputableInPolyTime decider horizontal keepPositive)
    (UnaryFieldConstantScale.computableInPolyTime 2)

@[simp] theorem directSourceFinalOccurrenceClearanceClauseOrigins_length (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalOccurrenceClearanceClauseOrigins decider horizontal keepPositive symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  rw [directSourceFinalOccurrenceClearanceClauseOrigins, UnaryFieldConstantScale.values, List.length_map,
    directSourceFinalOccurrenceClauseOrigins_length]

/-- The compiled coordinate is the stored source-clause position in this
occurrence's own composed Figure 9 metadata. -/
theorem directSourceFinalOccurrenceClearanceClauseOrigins_lookup (horizontal keepPositive : Bool) (symbols : List encoding.Γ)
    (index : Nat) (occurrence : SourceOccurrence)
    (lookup : (directSourceFinalOccurrences decider symbols)[index]? = some occurrence)
    (witness : OccurrenceWitness (directSourceFormula decider symbols) occurrence) :
    (directSourceFinalOccurrenceClearanceClauseOrigins decider horizontal keepPositive symbols)[index]? =
      some (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
        witness.metadata.sourceClause.position) := by
  rw [directSourceFinalOccurrenceClearanceClauseOrigins, UnaryFieldConstantScale.values, List.getElem?_map,
    directSourceFinalOccurrenceClauseOrigins_lookup decider horizontal keepPositive symbols index occurrence lookup witness,
    Option.map_some, witness.metadataSource]
  change some (_ * 2) = some (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
    (Cell.scale 2 witness.refinedClause.position))
  rw [pointValue_double]

end LeanTrominoes.PeriodicCNFStripReduction
end
