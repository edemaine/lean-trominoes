/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticGraphOrientationNativeVertexFields
import LeanTrominoes.UnaryColumnChoiceCompiler
import LeanTrominoes.UnaryColumnDenseLookupCompiler

/-! # Dense source and target fields emitted by polynomial-time machines -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Turing Gadget PeriodicThreeDM UnaryColumn
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language) [Inhabited encoding.Γ]
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 2048

theorem incidenceElement_of_mem {problem : PeriodicThreeDM} {color : WireColor} {atom : Nat} {incidence : Incidence}
    (member : incidence ∈ problem.incidences color atom) :
    problem.incidenceElement ⟨incidence.tripleIndex,color⟩ = (color,atom) := by
  simp only [incidences,List.mem_filterMap] at member
  obtain ⟨index,_,equal⟩ := member
  split at equal
  · rename_i matchesAtom
    simp only [Option.some.injEq] at equal
    subst incidence
    simp only [List.getD_eq_getElem?_getD] at matchesAtom
    simp [incidenceElement,matchesAtom]
  · contradiction

def nativeSourceKeyCompiler : Compiler (fun s => (nativeThreeDMProblem decider s).contractedEdges)
    (fun s edge => nativeVertexKey decider s edge.toPeriodicEdge.source) := by
  let physical := scale (nativeContractedSourceTripleCompiler decider) 2
  exact TM2ComputableInPolyTime.of_eq physical (fun s => by
    apply List.map_congr_left
    intro edge _
    cases edge <;> simp [nativeVertexKey,ContractedEdge.toPeriodicEdge,ContractedEdge.sourceTag,Nat.mul_comm])

def nativeTargetKeyCompiler : Compiler (fun s => (nativeThreeDMProblem decider s).contractedEdges)
    (fun s edge => nativeVertexKey decider s edge.toPeriodicEdge.target) := by
  let triple := scale (nativeIncidenceTripleIndexCompiler decider) 2
  let element := add (scale (nativeThreeDMIncidenceKeyCompiler decider) 2)
    (constant (nativeThreeDMIncidenceKeyCompiler decider) 1)
  let candidates := chooseThree (nativeIncidenceDegreeCompiler decider) triple element
  let physical := nativeContractedTargetCompiler decider candidates
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  apply List.map_congr_left
  intro edge member
  have data := contractedEdge_incidence_members_of_mem (nativeThreeDMProblem decider s) member
  have atTarget : (nativeThreeDMProblem decider s).incidenceElement edge.targetTag = (edge.color,edge.atom) := by
    cases edge <;> exact incidenceElement_of_mem data.2.1
  change (if (nativeThreeDMProblem decider s).degree edge.targetTag.color
      ((nativeThreeDMProblem decider s).incidenceElement edge.targetTag).2 = 3 then
      nativeElementKey decider s ((nativeThreeDMProblem decider s).incidenceElement edge.targetTag)*2+1
    else edge.targetTag.tripleIndex*2) = nativeVertexKey decider s edge.toPeriodicEdge.target
  rw [atTarget]
  cases edge with
  | retained color atom incidence =>
    have degree : (nativeThreeDMProblem decider s).degree color atom = 3 := by
      simpa [ContractedEdge.color,ContractedEdge.atom,ContractedEdge.targetIsElement] using data.2.2
    simp [ContractedEdge.targetTag,ContractedEdge.atom,ContractedEdge.toPeriodicEdge,nativeVertexKey,degree,Nat.mul_comm]
  | through color atom first second =>
    have degree : (nativeThreeDMProblem decider s).degree color atom = 2 := by
      simpa [ContractedEdge.color,ContractedEdge.atom,ContractedEdge.targetIsElement] using data.2.2
    simp [ContractedEdge.targetTag,ContractedEdge.atom,ContractedEdge.toPeriodicEdge,nativeVertexKey,degree,Nat.mul_comm]

def nativeDenseVertexCompiler {Row : Type} {rows : List encoding.Γ → List Row}
    {vertex : List encoding.Γ → Row → PeriodicThreeDMVertex}
    (queries : Compiler rows (fun s row => nativeVertexKey decider s (vertex s row)))
    (listed : ∀ s row, row ∈ rows s → vertex s row ∈ (nativeThreeDMProblem decider s).contractedGraph.vertices) :
    Compiler rows (fun s row => (nativeThreeDMProblem decider s).contractedGraph.vertices.idxOf (vertex s row)) :=
  denseLookup (rows := rows)
    (entries := fun s => (nativeThreeDMProblem decider s).contractedGraph.vertices)
    (key := nativeVertexKey decider) (entry := vertex)
    queries (nativeVertexKeyCompiler decider) (nativeVertexOrdinalCompiler decider)
    (nativeVertexKey_injective_on decider) listed

theorem contractedEdge_endpoints_mem {problem : PeriodicThreeDM} {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges) :
    edge.toPeriodicEdge.source ∈ problem.contractedGraph.vertices ∧
      edge.toPeriodicEdge.target ∈ problem.contractedGraph.vertices := by
  apply (contractedGraph_isWellFormed problem).2 edge.toPeriodicEdge
  change edge.toPeriodicEdge ∈ problem.contractedEdges.map ContractedEdge.toPeriodicEdge
  exact List.mem_map.mpr ⟨edge,member,rfl⟩

def nativeSourceFieldCompiler : Compiler (fun s => (nativeThreeDMProblem decider s).contractedEdges)
    (fun s edge => (nativeThreeDMProblem decider s).contractedGraph.vertices.idxOf edge.toPeriodicEdge.source) := by
  apply nativeDenseVertexCompiler decider
    (rows := fun s => (nativeThreeDMProblem decider s).contractedEdges)
    (vertex := fun _ edge => edge.toPeriodicEdge.source) (nativeSourceKeyCompiler decider)
  intro s edge member
  exact (contractedEdge_endpoints_mem (problem := nativeThreeDMProblem decider s) (edge := edge) member).1

def nativeTargetFieldCompiler : Compiler (fun s => (nativeThreeDMProblem decider s).contractedEdges)
    (fun s edge => (nativeThreeDMProblem decider s).contractedGraph.vertices.idxOf edge.toPeriodicEdge.target) := by
  apply nativeDenseVertexCompiler decider
    (rows := fun s => (nativeThreeDMProblem decider s).contractedEdges)
    (vertex := fun _ edge => edge.toPeriodicEdge.target) (nativeTargetKeyCompiler decider)
  intro s edge member
  exact (contractedEdge_endpoints_mem (problem := nativeThreeDMProblem decider s) (edge := edge) member).2

end LeanTrominoes.PeriodicCNFStripReduction
end
