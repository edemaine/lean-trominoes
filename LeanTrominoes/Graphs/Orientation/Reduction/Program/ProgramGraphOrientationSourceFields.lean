/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.Reduction.Program.ProgramGraphOrientationElements
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientationFlatEncoding
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Incidence.PeriodicCNFStripDirectSourceFinalIncidenceValueSelection
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Canonical.PeriodicCNFStripDirectSourceFinalCanonicalElementDegreeHorizontalSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Counted.PeriodicCNFStripCountedContractedIncidenceTargetFilter
import LeanTrominoes.Computation.Encoding.Unary.UnaryColumnSignedEncoding
import LeanTrominoes.Computation.Encoding.Unary.UnaryFieldFixedCopiesCompiler
import LeanTrominoes.Computation.Encoding.Unary.UnaryFieldThreeSlotRankCompiler

/-! # Polynomial-time source and target incidence columns for ordinary graph records -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Turing Gadget PeriodicThreeDM UnaryColumn
variable {Input : Type} {encoding : _root_.LeanTrominoes.FiniteEncoding Input} {language : Input → Prop}
variable (source : PeriodicCNF.ProgramSource encoding language) [Inhabited encoding.Γ]
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 2048

def programContractedSourceCompiler {field : List encoding.Γ → IncidenceTag → Nat}
    (values : Compiler (programThreeDMIncidences source) field) :
    Compiler (fun s => (programThreeDMProblem source s).contractedEdges) (fun s edge => field s edge.sourceTag) := by
  let columns := fun s => (programThreeDMIncidences source s).map (field s)
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
  change directSourceFinalSelectedIncidenceValues source s ((programThreeDMIncidences source s).map (field s)) = _ at grouped
  rw [grouped,directSourceFinalCanonicalElementDegrees_eq_horizontal]
  exact CountedContractedIncidence.selected_sources_eq_contracted _ (field s) (programThreeDMDegree source s)

def programContractedTargetCompiler {field : List encoding.Γ → IncidenceTag → Nat}
    (values : Compiler (programThreeDMIncidences source) field) :
    Compiler (fun s => (programThreeDMProblem source s).contractedEdges) (fun s edge => field s edge.targetTag) := by
  let columns := fun s => (programThreeDMIncidences source s).map (field s)
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
  change directSourceFinalSelectedIncidenceValues source s ((programThreeDMIncidences source s).map (field s)) = _ at grouped
  rw [grouped,directSourceFinalCanonicalElementDegrees_eq_horizontal]
  exact CountedContractedIncidence.selected_targets_eq_contracted _ (field s) (programThreeDMDegree source s)

def programIncidenceTripleIndexCompiler : Compiler (programThreeDMIncidences source) (fun _ tag => tag.tripleIndex) := by
  let physical := TM2CompositionMachine.computableInPolyTime
    (naturalRange (programThreeDMTripleCountCompiler source)) (UnaryFieldFixedCopies.computableInPolyTime 3)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  simp [UnaryFieldFixedCopies.values,programThreeDMIncidences,incidenceTags_eq_range_flatMap,
    tripleIncidenceTags,incidenceColors,List.map_flatMap]

def programIncidenceColorCompiler : Compiler (programThreeDMIncidences source)
    (fun _ tag => TrichromaticGraphOrientation.FlatEncoding.colorField tag.color) := by
  let physical := TM2CompositionMachine.computableInPolyTime
    (naturalRange (programThreeDMTripleCountCompiler source)) UnaryFieldThreeSlotRanks.computableInPolyTime
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  simp [UnaryFieldThreeSlotRanks.values,programThreeDMIncidences,incidenceTags_eq_range_flatMap,
    tripleIncidenceTags,incidenceColors,List.map_flatMap,TrichromaticGraphOrientation.FlatEncoding.colorField]

def programContractedSourceTripleCompiler : Compiler (fun s => (programThreeDMProblem source s).contractedEdges)
    (fun _ edge => edge.sourceTag.tripleIndex) := programContractedSourceCompiler source (programIncidenceTripleIndexCompiler source)

def programContractedTargetTripleCompiler : Compiler (fun s => (programThreeDMProblem source s).contractedEdges)
    (fun _ edge => edge.targetTag.tripleIndex) := programContractedTargetCompiler source (programIncidenceTripleIndexCompiler source)

def programContractedColorCompiler : Compiler (fun s => (programThreeDMProblem source s).contractedEdges)
    (fun _ edge => TrichromaticGraphOrientation.FlatEncoding.colorField edge.color) := by
  let physical := programContractedSourceCompiler source (programIncidenceColorCompiler source)
  exact TM2ComputableInPolyTime.of_eq physical (fun s => by
    apply List.map_congr_left
    intro edge _
    cases edge <;> rfl)

end LeanTrominoes.PeriodicCNFStripReduction
end
