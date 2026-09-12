/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClearanceClauseOriginCompiler
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineClausePositionSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteHeaderCompiler
import LeanTrominoes.FiniteUnaryFieldMapCompiler

/-! # Compiled finite template clause coordinates in actual occurrence order -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PeriodicCNF.FormulaShapeFigureNineRoutePrefix
open PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
open PlanarOneInThreeNoUnitsFigureNine

/-- The complete finite header selects one local composed-template clause. -/
def headerTemplateClausePosition (header : PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader.Header) : Cell :=
  let coordinate := headerTemplateProfileCoordinate header
  templateClausePosition coordinate.profile coordinate.coordinate.clauseIndex

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance templateCoordinateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
attribute [local instance] directSourceVariableDecidableEqInstance

def directSourceFinalTemplateClauseCoordinates (horizontal keepPositive : Bool) (symbols : List encoding.Γ) : List Nat :=
  FiniteUnaryFieldMap.values (fun header => CarrierCrossingPointField.pointValue
    (coordinateFieldOfBools horizontal keepPositive) (headerTemplateClausePosition header))
    (sourceHeaders (directSourceFinalClauseDescriptors decider symbols))

noncomputable def directSourceFinalTemplateClauseCoordinatesComputableInPolyTime (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalTemplateClauseCoordinates decider horizontal keepPositive) := by
  unfold directSourceFinalTemplateClauseCoordinates
  exact TM2CompositionMachine.computableInPolyTime
    (TM2CompositionMachine.computableInPolyTime (directSourceFinalClauseDescriptorsComputableInPolyTime decider)
      sourceHeadersComputableInPolyTime)
    (FiniteUnaryFieldMap.computableInPolyTime _)

theorem directSourceFinalHeaders_eq_occurrences (symbols : List encoding.Γ) :
    sourceHeaders (directSourceFinalClauseDescriptors decider symbols) =
      (directSourceFinalOccurrences decider symbols).map SourceOccurrence.header := by
  have headers := congrArg (List.map Prod.fst)
    (sourceOccurrences_map_pair (directSourceFinalClauseDescriptors decider symbols)
      (tailTables (directSourceFormula decider symbols)))
  rw [List.map_map, sourcePairs_map_fst] at headers
  have occurrencesEq : sourceOccurrences (directSourceFinalClauseDescriptors decider symbols)
      (tailTables (directSourceFormula decider symbols)) = directSourceFinalOccurrences decider symbols := by
    unfold directSourceFinalOccurrences occurrences
    rw [directSourceFinalClauseDescriptors_eq_source_prefix, sourceOccurrences_append_variables]
  rw [occurrencesEq] at headers
  simpa only [SourceOccurrence.pair, Function.comp_def] using headers.symm

theorem directSourceFinalTemplateClauseCoordinates_eq_occurrences (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalTemplateClauseCoordinates decider horizontal keepPositive symbols =
      (directSourceFinalOccurrences decider symbols).map fun occurrence =>
        CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
          (headerTemplateClausePosition occurrence.header) := by
  unfold directSourceFinalTemplateClauseCoordinates FiniteUnaryFieldMap.values
  rw [directSourceFinalHeaders_eq_occurrences, List.map_map]
  simp only [Function.comp_def]

@[simp] theorem directSourceFinalTemplateClauseCoordinates_length (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalTemplateClauseCoordinates decider horizontal keepPositive symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  rw [directSourceFinalTemplateClauseCoordinates_eq_occurrences, List.length_map,
    directSourceFinalCompiledOccurrenceData_eq_routePairs, List.length_map]
  simpa only [List.length_map] using congrArg List.length (directSourceFinalOccurrences_map_pair decider symbols)

/-- Header coordinates recover the local clause named by the same metadata
witness as the compiled source origin. -/
theorem directSourceFinalTemplateClauseCoordinates_lookup (horizontal keepPositive : Bool) (symbols : List encoding.Γ)
    (index : Nat) (occurrence : SourceOccurrence)
    (lookup : (directSourceFinalOccurrences decider symbols)[index]? = some occurrence)
    (witness : OccurrenceWitness (directSourceFormula decider symbols) occurrence) :
    (directSourceFinalTemplateClauseCoordinates decider horizontal keepPositive symbols)[index]? =
      some (CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
        (templateClausePosition witness.metadata.parentProfileCoordinate.profile witness.metadata.localClauseIndex)) := by
  rw [directSourceFinalTemplateClauseCoordinates_eq_occurrences, List.getElem?_map, lookup, Option.map_some]
  dsimp only [headerTemplateClausePosition]
  rw [witness.metadataCoordinates.1, witness.metadataCoordinates.2.1]

end LeanTrominoes.PeriodicCNFStripReduction
end
