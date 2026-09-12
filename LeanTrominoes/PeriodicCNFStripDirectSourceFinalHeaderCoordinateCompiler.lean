/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalTemplateClauseCoordinateCompiler

/-! # Unary coordinate columns from arbitrary finite header point tables -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance headerCoordinateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
attribute [local instance] directSourceVariableDecidableEqInstance

/-- Any fixed table of points on the finite header alphabet supplies one
coordinate field per coherent occurrence. -/
def directSourceFinalHeaderPointCoordinates
    (point : PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader.Header → Cell) (horizontal keepPositive : Bool) (symbols : List encoding.Γ) : List Nat :=
  FiniteUnaryFieldMap.values (fun header => CarrierCrossingPointField.pointValue
    (coordinateFieldOfBools horizontal keepPositive) (point header))
    (sourceHeaders (directSourceFinalClauseDescriptors decider symbols))

noncomputable def directSourceFinalHeaderPointCoordinatesComputableInPolyTime
    (point : PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader.Header → Cell) (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalHeaderPointCoordinates decider point horizontal keepPositive) := by
  unfold directSourceFinalHeaderPointCoordinates
  exact TM2CompositionMachine.computableInPolyTime
    (TM2CompositionMachine.computableInPolyTime (directSourceFinalClauseDescriptorsComputableInPolyTime decider)
      sourceHeadersComputableInPolyTime)
    (FiniteUnaryFieldMap.computableInPolyTime _)

theorem directSourceFinalHeaderPointCoordinates_eq_occurrences
    (point : PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader.Header → Cell) (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalHeaderPointCoordinates decider point horizontal keepPositive symbols =
      (directSourceFinalOccurrences decider symbols).map fun occurrence =>
        CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive) (point occurrence.header) := by
  unfold directSourceFinalHeaderPointCoordinates FiniteUnaryFieldMap.values
  rw [directSourceFinalHeaders_eq_occurrences, List.map_map]
  simp only [Function.comp_def]

@[simp] theorem directSourceFinalHeaderPointCoordinates_length
    (point : PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader.Header → Cell) (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalHeaderPointCoordinates decider point horizontal keepPositive symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  rw [directSourceFinalHeaderPointCoordinates_eq_occurrences, List.length_map,
    directSourceFinalCompiledOccurrenceData_eq_routePairs, List.length_map]
  simpa only [List.length_map] using congrArg List.length (directSourceFinalOccurrences_map_pair decider symbols)

theorem directSourceFinalHeaderPointCoordinates_lookup
    (point : PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader.Header → Cell) (horizontal keepPositive : Bool) (symbols : List encoding.Γ)
    (index : Nat) (occurrence : SourceOccurrence)
    (lookup : (directSourceFinalOccurrences decider symbols)[index]? = some occurrence) :
    (directSourceFinalHeaderPointCoordinates decider point horizontal keepPositive symbols)[index]? =
      some (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive) (point occurrence.header)) := by
  rw [directSourceFinalHeaderPointCoordinates_eq_occurrences, List.getElem?_map, lookup, Option.map_some]

end LeanTrominoes.PeriodicCNFStripReduction
end
