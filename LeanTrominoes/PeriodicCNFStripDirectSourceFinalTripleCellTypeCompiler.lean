/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalIncidenceEndpointSummaryHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTripleCellTypeDirections
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalTripleCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVertexPositionAtComputed

/-! # Actual triple cell types from the already compiled RGB endpoint summaries -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing Gadget PeriodicThreeDM

local instance : Inhabited OrthogonalCellType := ⟨.monochromaticVertex .red⟩

/-- The red summary carries the complete fan; the green and blue copies add no vertex. -/
def tripleCellTypeBlock (summary : IncidenceEndpointSummary.Summary) : List OrthogonalCellType :=
  if summary.color = .red then
    [horizontalTripleCellTypeFromDirections summary.redFirst summary.greenFirst summary.blueFirst]
  else []

private theorem cellTypeBlock_triple (endpoints : IncidenceTag → IncidenceEndpointSummary.Endpoints)
    (index : Nat) :
    ((tripleIncidenceTags index).map (IncidenceEndpointSummary.atTag endpoints)).flatMap tripleCellTypeBlock =
      [horizontalTripleCellTypeFromDirections
        (endpoints ⟨index, .red⟩).1 (endpoints ⟨index, .green⟩).1 (endpoints ⟨index, .blue⟩).1] := by
  simp [tripleIncidenceTags, incidenceColors, IncidenceEndpointSummary.atTag, tripleCellTypeBlock]

private theorem cellTypeBlock_incidenceTags (problem : PeriodicThreeDM)
    (endpoints : IncidenceTag → IncidenceEndpointSummary.Endpoints) :
    (problem.incidenceTags.map (IncidenceEndpointSummary.atTag endpoints)).flatMap tripleCellTypeBlock =
      (List.range problem.triples.length).map
        (fun index => horizontalTripleCellTypeFromDirections
          (endpoints ⟨index, .red⟩).1 (endpoints ⟨index, .green⟩).1 (endpoints ⟨index, .blue⟩).1) := by
  rw [incidenceTags_eq_range_flatMap, List.map_flatMap, List.flatMap_assoc]
  simp only [cellTypeBlock_triple, ← List.map_eq_flatMap]

private theorem actualTripleCellType (source : PeriodicCNF Nat) (index : Nat)
    (bound : index < (horizontalThreeDMProblemComputed source).triples.length) :
    horizontalTripleCellTypeFromDirections
        (horizontalIncidenceEndpoints source ⟨index, .red⟩).1
        (horizontalIncidenceEndpoints source ⟨index, .green⟩).1
        (horizontalIncidenceEndpoints source ⟨index, .blue⟩).1 =
      NormalizationCompiler.finalVertexCellType (horizontalNormalizationInputComputed source) (.triple index) := by
  have member (color : WireColor) : (⟨index, color⟩ : IncidenceTag) ∈
      (horizontalThreeDMProblemComputed source).incidenceTags :=
    tripleIncidenceTag_mem_incidenceTags _ index bound color
  simp only [horizontalIncidenceEndpoints]
  rw [horizontalFinalVertexCellType_eq_incidenceDirections source index (by
    simpa only [horizontalNormalizationInputComputed_problem] using bound),
    horizontalNormalizationIncidenceRouteComputed_eq_routeAtTag source _ (member .red),
    horizontalNormalizationIncidenceRouteComputed_eq_routeAtTag source _ (member .green),
    horizontalNormalizationIncidenceRouteComputed_eq_routeAtTag source _ (member .blue)]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- One compiled final cell type for each triple in canonical presentation order. -/
def directSourceFinalTripleCellTypes (symbols : List encoding.Γ) : List OrthogonalCellType :=
  (directSourceFinalIncidenceEndpointSummaries decider symbols).flatMap tripleCellTypeBlock

noncomputable def directSourceFinalTripleCellTypesComputableInPolyTime :
    TM2ComputableInPolyTime id id (directSourceFinalTripleCellTypes decider) := by
  unfold directSourceFinalTripleCellTypes
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalIncidenceEndpointSummariesComputableInPolyTime decider)
    (FiniteBlockTransducer.computableInPolyTime tripleCellTypeBlock)

theorem directSourceFinalTripleCellTypes_eq_range (symbols : List encoding.Γ) :
    directSourceFinalTripleCellTypes decider symbols =
      (List.range (horizontalThreeDMProblemComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).triples.length).map
          (fun index => NormalizationCompiler.finalVertexCellType
            (horizontalNormalizationInputComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))
              (.triple index)) := by
  unfold directSourceFinalTripleCellTypes
  rw [directSourceFinalIncidenceEndpointSummaries_eq_horizontal]
  unfold horizontalIncidenceEndpointSummary
  rw [cellTypeBlock_incidenceTags]
  apply List.map_congr_left
  intro index member
  exact actualTripleCellType _ index (List.mem_range.mp member)

/-- Cell types align with the computed positions and stable indices consumed by the vertex scan. -/
theorem directSourceFinalTripleCellTypes_eq_indexedPositions (symbols : List encoding.Γ) :
    directSourceFinalTripleCellTypes decider symbols =
      (horizontalThreeDMTriplePositionsComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).zipIdx.map
          (fun tagged => NormalizationCompiler.finalVertexCellType
            (horizontalNormalizationInputComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))
              (.triple tagged.2)) := by
  rw [directSourceFinalTripleCellTypes_eq_range]
  have lengthEq : (horizontalThreeDMProblemComputed
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).triples.length =
      (horizontalThreeDMTriplePositionsComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).length := by
    rw [← horizontalThreeDMPositionProblemComputed_eq]
    exact (horizontalThreeDMTriplePositionsComputed_length _).symm
  rw [lengthEq]
  have mapped := congrArg
    (List.map (fun index => NormalizationCompiler.finalVertexCellType
      (horizontalNormalizationInputComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))
        (.triple index)))
    (List.zipIdx_map_snd 0
      (horizontalThreeDMTriplePositionsComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)))
  simpa only [List.map_map, Function.comp_def, ← List.range_eq_range'] using mapped.symm

end LeanTrominoes.PeriodicCNFStripReduction
end
