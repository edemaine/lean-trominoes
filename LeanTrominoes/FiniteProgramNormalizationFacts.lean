/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteProgramSparseTrominoRegion
import LeanTrominoes.FiniteNormalizationPaddedVertexBounds
import LeanTrominoes.PeriodicThreeDMNormalizationRouteDirectionConditions

/-! # Verified geometry for the finite program-source emitter -/
noncomputable section
namespace LeanTrominoes.FiniteProgramSparseTrominoRegion
open Gadget PeriodicCNF PeriodicCNFStripReduction
open PeriodicThreeDM.NormalizationCompiler
variable {Source : Type} {encoding : _root_.Computability.FinEncoding Source} {language : Source → Prop}
variable (source : ProgramSource encoding language)
variable (zero : ∀ symbols,FiniteCNF.ZeroOffsets (source.formulaOfSymbols symbols))

include zero in
theorem inputs_zero (symbols : List encoding.Γ) : (inputs source symbols).problem.ZeroOffsets := by
  rw [inputs,directSparseComputedNormalizationInputOfSymbols_eq]
  change (normalizationInput (source.formulaOfSymbols symbols)).problem.ZeroOffsets
  rw [normalizationInput_problem]
  exact problemZero source zero symbols

theorem inputs_vertexLength (symbols : List encoding.Γ) :
    (inputs source symbols).drawing.vertexPositions.length=
      (inputs source symbols).problem.incidenceGraph.vertices.length := by
  rw [inputs,directSparseComputedNormalizationInputOfSymbols_eq]
  change (normalizationInput (source.formulaOfSymbols symbols)).drawing.vertexPositions.length=
    (normalizationInput (source.formulaOfSymbols symbols)).problem.incidenceGraph.vertices.length
  rw [normalizationInput_problem,normalizationInput_drawing]
  exact (presentation (source.formulaOfSymbols symbols)).compatible.2.1

theorem inputs_vertexBounds (symbols : List encoding.Γ) (vertex : PeriodicThreeDMVertex)
    (member : vertex∈(inputs source symbols).problem.contractedGraph.vertices) :
    let point := (inputs source symbols).drawing.vertexPosition (inputs source symbols).problem.incidenceGraph vertex
    0≤point.1 ∧ point.1<((inputs source symbols).drawing.gridSize:Int) ∧
    0≤point.2 ∧ point.2<((inputs source symbols).drawing.gridSize:Int) :=
  directSparseComputedInput_vertexPosition_bounds source symbols member

theorem paddedInputs_vertexBounds (symbols : List encoding.Γ) (vertex : PeriodicThreeDMVertex)
    (member : vertex∈(paddedInputs source symbols).problem.contractedGraph.vertices) :
    let point := (paddedInputs source symbols).drawing.vertexPosition (paddedInputs source symbols).problem.incidenceGraph vertex
    0≤point.1 ∧ point.1<((paddedInputs source symbols).drawing.gridSize:Int) ∧
    0≤point.2 ∧ point.2<((paddedInputs source symbols).drawing.gridSize:Int) :=
  Input.finitePad_vertexPosition_bounds _ (inputs_vertexLength source symbols) member
    (inputs_vertexBounds source symbols vertex member)

include zero in
theorem paddedInputs_routeConditions (symbols : List encoding.Γ) (edge : PeriodicThreeDM.ContractedEdge)
    (member : edge∈(paddedInputs source symbols).problem.contractedEdges) :
    RouteDirectionConditions (paddedInputs source symbols) edge := by
  rw [paddedInputs_eq_presentation source zero] at member ⊢
  exact ((presentation (source.formulaOfSymbols symbols)).finitePad
    (problemZero source zero symbols) (endpointBounds source symbols)).routeDirectionConditions
    (presentation (source.formulaOfSymbols symbols)).problemWellFormed
    (problem_degreeTwoOrThree _) member

include zero in
theorem paddedAssignments_positive (symbols : List encoding.Γ) (assignment : Cell × OrthogonalCellType)
    (member : assignment∈finalStripCellAssignments (paddedInputs source symbols)) :
    0<assignment.1.1 ∧ 0<assignment.1.2 := by
  rw [paddedInputs_eq_presentation source zero,finalStripCellAssignments_inputOfPresentation] at member
  have facts := (presentation (source.formulaOfSymbols symbols)).finitePaddedSparseFacts
    (problemZero source zero symbols) (endpointBounds source symbols)
    (presentation (source.formulaOfSymbols symbols)).problemWellFormed
    (problem_degreeTwoOrThree _) (presentation_separated _) (presentation_routesSimple _)
  have bounds := facts.2.1 assignment member
  exact ⟨bounds.1,bounds.2.2.1⟩
end LeanTrominoes.FiniteProgramSparseTrominoRegion
