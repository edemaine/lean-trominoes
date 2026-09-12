/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalTemplateClauseCoordinateCompiler

/-! # Compiled finite Figure 9 variable coordinates -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PlanarOneInThreeNoUnitsFigureNine

/-- Local coordinate of the pre-polarity template role named by the header.
Inherited roles denote boundary ports; their actual source coordinates are
supplied by the inherited column. -/
def headerTemplateVariablePosition (header : PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader.Header) : Cell :=
  let query := header.figurePrefix.localQuery
  variablePosition ((templateDrawingOfClauseProfile query.1).incidenceAt query.2).literal.1

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance templateVariableStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
attribute [local instance] directSourceVariableDecidableEqInstance

def directSourceFinalTemplateVariableCoordinates (horizontal keepPositive : Bool) (symbols : List encoding.Γ) : List Nat :=
  FiniteUnaryFieldMap.values (fun header => CarrierCrossingPointField.pointValue
    (coordinateFieldOfBools horizontal keepPositive) (headerTemplateVariablePosition header))
    (sourceHeaders (directSourceFinalClauseDescriptors decider symbols))

noncomputable def directSourceFinalTemplateVariableCoordinatesComputableInPolyTime (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalTemplateVariableCoordinates decider horizontal keepPositive) := by
  unfold directSourceFinalTemplateVariableCoordinates
  exact TM2CompositionMachine.computableInPolyTime
    (TM2CompositionMachine.computableInPolyTime (directSourceFinalClauseDescriptorsComputableInPolyTime decider)
      sourceHeadersComputableInPolyTime)
    (FiniteUnaryFieldMap.computableInPolyTime _)

theorem directSourceFinalTemplateVariableCoordinates_eq_occurrences (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalTemplateVariableCoordinates decider horizontal keepPositive symbols =
      (directSourceFinalOccurrences decider symbols).map fun occurrence =>
        CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
          (headerTemplateVariablePosition occurrence.header) := by
  unfold directSourceFinalTemplateVariableCoordinates FiniteUnaryFieldMap.values
  rw [directSourceFinalHeaders_eq_occurrences, List.map_map]
  simp only [Function.comp_def]

@[simp] theorem directSourceFinalTemplateVariableCoordinates_length (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalTemplateVariableCoordinates decider horizontal keepPositive symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  rw [directSourceFinalTemplateVariableCoordinates_eq_occurrences, List.length_map,
    directSourceFinalCompiledOccurrenceData_eq_routePairs, List.length_map]
  simpa only [List.length_map] using congrArg List.length (directSourceFinalOccurrences_map_pair decider symbols)

theorem directSourceFinalTemplateVariableCoordinates_lookup (horizontal keepPositive : Bool) (symbols : List encoding.Γ)
    (index : Nat) (occurrence : SourceOccurrence)
    (lookup : (directSourceFinalOccurrences decider symbols)[index]? = some occurrence) :
    (directSourceFinalTemplateVariableCoordinates decider horizontal keepPositive symbols)[index]? =
      some (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
        (headerTemplateVariablePosition occurrence.header)) := by
  rw [directSourceFinalTemplateVariableCoordinates_eq_occurrences, List.getElem?_map, lookup, Option.map_some]

end LeanTrominoes.PeriodicCNFStripReduction
end
