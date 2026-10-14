/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeThreeDMFields
import LeanTrominoes.PeriodicCNFStripNativeThreeDMTargetCoordinates
import LeanTrominoes.TrichromaticGraphOrientationFlatEncoding
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalIncidenceValueSelection
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalElementDegreeHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripCountedContractedIncidenceTargetFilter
import LeanTrominoes.UnaryColumnSignedEncoding
import LeanTrominoes.UnaryFieldFixedCopiesCompiler
import LeanTrominoes.UnaryFieldThreeSlotRankCompiler

/-! # Polynomial-time source and target incidence columns for ordinary graph records -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Turing Gadget PeriodicThreeDM UnaryColumn
variable {Input : Type} {encoding : _root_.LeanTrominoes.FiniteEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language) [Inhabited encoding.Γ]
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 2048

def nativeContractedSourceCompiler {field : List encoding.Γ → IncidenceTag → Nat}
    (values : Compiler (nativeThreeDMIncidences decider) field) :
    Compiler (fun s => (nativeThreeDMProblem decider s).contractedEdges) (fun s edge => field s edge.sourceTag) := by
  let source := PeriodicCNF.ProgramSource.ofDecider decider
  let columns := fun s => (nativeThreeDMIncidences decider s).map (field s)
  let selected := directSourceFinalSelectedIncidenceValuesComputableInPolyTime source columns
    (fun s => List.length_map ..) values
  let controls := TM2CompositionMachine.computableInPolyTime
    (directSourceFinalCanonicalElementDegreesComputableInPolyTime source)
    CountedContractedIncidence.sourceControlsComputableInPolyTime
  let physical := UnaryFieldBooleanFilter.selectedValuesNativeListComputableInPolyTime _ _ controls selected
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  dsimp only [columns]
  have grouped := directSourceFinalSelectedIncidenceValues_map_eq_horizontal source s (field s)
  change directSourceFinalSelectedIncidenceValues source s ((nativeThreeDMIncidences decider s).map (field s)) = _ at grouped
  rw [grouped,directSourceFinalCanonicalElementDegrees_eq_horizontal]
  exact CountedContractedIncidence.selected_sources_eq_contracted _ (field s) (nativeThreeDMDegree decider s)

def nativeContractedTargetCompiler {field : List encoding.Γ → IncidenceTag → Nat}
    (values : Compiler (nativeThreeDMIncidences decider) field) :
    Compiler (fun s => (nativeThreeDMProblem decider s).contractedEdges) (fun s edge => field s edge.targetTag) := by
  let source := PeriodicCNF.ProgramSource.ofDecider decider
  let columns := fun s => (nativeThreeDMIncidences decider s).map (field s)
  let selected := directSourceFinalSelectedIncidenceValuesComputableInPolyTime source columns
    (fun s => List.length_map ..) values
  let controls := TM2CompositionMachine.computableInPolyTime
    (directSourceFinalCanonicalElementDegreesComputableInPolyTime source)
    CountedContractedIncidence.targetControlsComputableInPolyTime
  let physical := UnaryFieldBooleanFilter.selectedValuesNativeListComputableInPolyTime _ _ controls selected
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  dsimp only [columns]
  have grouped := directSourceFinalSelectedIncidenceValues_map_eq_horizontal source s (field s)
  change directSourceFinalSelectedIncidenceValues source s ((nativeThreeDMIncidences decider s).map (field s)) = _ at grouped
  rw [grouped,directSourceFinalCanonicalElementDegrees_eq_horizontal]
  exact CountedContractedIncidence.selected_targets_eq_contracted _ (field s) (nativeThreeDMDegree decider s)

def nativeIncidenceTripleIndexCompiler : Compiler (nativeThreeDMIncidences decider) (fun _ tag => tag.tripleIndex) := by
  let physical := TM2CompositionMachine.computableInPolyTime
    (naturalRange (nativeThreeDMTripleCountCompiler decider)) (UnaryFieldFixedCopies.computableInPolyTime 3)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  simp [UnaryFieldFixedCopies.values,nativeThreeDMIncidences,incidenceTags_eq_range_flatMap,
    tripleIncidenceTags,incidenceColors,List.map_flatMap]

def nativeIncidenceColorCompiler : Compiler (nativeThreeDMIncidences decider)
    (fun _ tag => TrichromaticGraphOrientation.FlatEncoding.colorField tag.color) := by
  let physical := TM2CompositionMachine.computableInPolyTime
    (naturalRange (nativeThreeDMTripleCountCompiler decider)) UnaryFieldThreeSlotRanks.computableInPolyTime
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  simp [UnaryFieldThreeSlotRanks.values,nativeThreeDMIncidences,incidenceTags_eq_range_flatMap,
    tripleIncidenceTags,incidenceColors,List.map_flatMap,TrichromaticGraphOrientation.FlatEncoding.colorField]

def nativeContractedSourceTripleCompiler : Compiler (fun s => (nativeThreeDMProblem decider s).contractedEdges)
    (fun _ edge => edge.sourceTag.tripleIndex) := nativeContractedSourceCompiler decider (nativeIncidenceTripleIndexCompiler decider)

def nativeContractedTargetTripleCompiler : Compiler (fun s => (nativeThreeDMProblem decider s).contractedEdges)
    (fun _ edge => edge.targetTag.tripleIndex) := nativeContractedTargetCompiler decider (nativeIncidenceTripleIndexCompiler decider)

def nativeContractedColorCompiler : Compiler (fun s => (nativeThreeDMProblem decider s).contractedEdges)
    (fun _ edge => TrichromaticGraphOrientation.FlatEncoding.colorField edge.color) := by
  let physical := nativeContractedSourceCompiler decider (nativeIncidenceColorCompiler decider)
  exact TM2ComputableInPolyTime.of_eq physical (fun s => by
    apply List.map_congr_left
    intro edge _
    cases edge <;> rfl)

end LeanTrominoes.PeriodicCNFStripReduction
end
