/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ProgramGraphOrientationVertexFields
import LeanTrominoes.TrichromaticGraphOrientationNativeEndpointFields
import LeanTrominoes.UnaryColumnChoiceCompiler
import LeanTrominoes.UnaryColumnDenseLookupCompiler

/-! # Dense source and target fields emitted by polynomial-time machines -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Turing Gadget PeriodicThreeDM UnaryColumn
variable {Input : Type} {encoding : _root_.LeanTrominoes.FiniteEncoding Input} {language : Input → Prop}
variable (source : PeriodicCNF.ProgramSource encoding language) [Inhabited encoding.Γ]
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 2048

def programSourceKeyCompiler : Compiler (fun s => (programThreeDMProblem source s).contractedEdges)
    (fun s edge => programVertexKey source s edge.toPeriodicEdge.source) := by
  let physical := scale (programContractedSourceTripleCompiler source) 2
  exact TM2ComputableInPolyTime.of_eq physical (fun s => by
    apply List.map_congr_left
    intro edge _
    cases edge <;> simp [programVertexKey,ContractedEdge.toPeriodicEdge,ContractedEdge.sourceTag,Nat.mul_comm])

def programTargetKeyCompiler : Compiler (fun s => (programThreeDMProblem source s).contractedEdges)
    (fun s edge => programVertexKey source s edge.toPeriodicEdge.target) := by
  let triple := scale (programIncidenceTripleIndexCompiler source) 2
  let element := add (scale (programThreeDMIncidenceKeyCompiler source) 2)
    (constant (programThreeDMIncidenceKeyCompiler source) 1)
  let candidates := chooseThree (programIncidenceDegreeCompiler source) triple element
  let physical := programContractedTargetCompiler source candidates
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  apply List.map_congr_left
  intro edge member
  have data := contractedEdge_incidence_members_of_mem (programThreeDMProblem source s) member
  have atTarget : (programThreeDMProblem source s).incidenceElement edge.targetTag = (edge.color,edge.atom) := by
    cases edge <;> exact incidenceElement_of_mem data.2.1
  change (if (programThreeDMProblem source s).degree edge.targetTag.color
      ((programThreeDMProblem source s).incidenceElement edge.targetTag).2 = 3 then
      programElementKey source s ((programThreeDMProblem source s).incidenceElement edge.targetTag)*2+1
    else edge.targetTag.tripleIndex*2) = programVertexKey source s edge.toPeriodicEdge.target
  rw [atTarget]
  cases edge with
  | retained color atom incidence =>
    have degree : (programThreeDMProblem source s).degree color atom = 3 := by
      simpa [ContractedEdge.color,ContractedEdge.atom,ContractedEdge.targetIsElement] using data.2.2
    simp [ContractedEdge.targetTag,ContractedEdge.atom,ContractedEdge.toPeriodicEdge,programVertexKey,degree,Nat.mul_comm]
  | through color atom first second =>
    have degree : (programThreeDMProblem source s).degree color atom = 2 := by
      simpa [ContractedEdge.color,ContractedEdge.atom,ContractedEdge.targetIsElement] using data.2.2
    simp [ContractedEdge.targetTag,ContractedEdge.atom,ContractedEdge.toPeriodicEdge,programVertexKey,degree,Nat.mul_comm]

def programDenseVertexCompiler {Row : Type} {rows : List encoding.Γ → List Row}
    {vertex : List encoding.Γ → Row → PeriodicThreeDMVertex}
    (queries : Compiler rows (fun s row => programVertexKey source s (vertex s row)))
    (listed : ∀ s row, row ∈ rows s → vertex s row ∈ (programThreeDMProblem source s).contractedGraph.vertices) :
    Compiler rows (fun s row => (programThreeDMProblem source s).contractedGraph.vertices.idxOf (vertex s row)) :=
  denseLookup (rows := rows)
    (entries := fun s => (programThreeDMProblem source s).contractedGraph.vertices)
    (key := programVertexKey source) (entry := vertex)
    queries (programVertexKeyCompiler source) (programVertexOrdinalCompiler source)
    (programVertexKey_injective_on source) listed

def programSourceFieldCompiler : Compiler (fun s => (programThreeDMProblem source s).contractedEdges)
    (fun s edge => (programThreeDMProblem source s).contractedGraph.vertices.idxOf edge.toPeriodicEdge.source) := by
  apply programDenseVertexCompiler source
    (rows := fun s => (programThreeDMProblem source s).contractedEdges)
    (vertex := fun _ edge => edge.toPeriodicEdge.source) (programSourceKeyCompiler source)
  intro s edge member
  exact (contractedEdge_endpoints_mem (problem := programThreeDMProblem source s) (edge := edge) member).1

def programTargetFieldCompiler : Compiler (fun s => (programThreeDMProblem source s).contractedEdges)
    (fun s edge => (programThreeDMProblem source s).contractedGraph.vertices.idxOf edge.toPeriodicEdge.target) := by
  apply programDenseVertexCompiler source
    (rows := fun s => (programThreeDMProblem source s).contractedEdges)
    (vertex := fun _ edge => edge.toPeriodicEdge.target) (programTargetKeyCompiler source)
  intro s edge member
  exact (contractedEdge_endpoints_mem (problem := programThreeDMProblem source s) (edge := edge) member).2

end LeanTrominoes.PeriodicCNFStripReduction
end
