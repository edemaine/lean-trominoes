/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientationNativeEndpointFields
import LeanTrominoes.Computation.Encoding.Unary.UnaryColumnBoundedSignedDifference
import LeanTrominoes.Tiling.Tromino.Strip.Native.PeriodicCNFStripNativeThreeDMLocality

/-! # Polynomial-time signed offset columns for the contracted graph -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Turing Gadget PeriodicThreeDM UnaryColumn DelimitedDirectionDisplacement
variable {Input : Type} {encoding : _root_.LeanTrominoes.FiniteEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language) [Inhabited encoding.Γ]
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 2048

theorem incidence_offset_reference_of_mem {problem : PeriodicThreeDM} {color : WireColor} {atom : Nat}
    {incidence : Incidence} (member : incidence ∈ problem.incidences color atom) :
    ((problem.triples.getD incidence.tripleIndex default).reference color).offset = incidence.offset := by
  simp only [incidences,List.mem_filterMap] at member
  obtain ⟨index,_,equal⟩ := member
  split at equal
  · simp only [Option.some.injEq] at equal
    subst incidence
    rfl
  · contradiction

def nativeSourceOffsetCompiler (horizontal : Bool) :
    Compiler (fun s => (nativeThreeDMProblem decider s).contractedEdges)
      (fun _ edge => Encodable.encode (component horizontal edge.sourceIncidence.offset)) := by
  apply TM2ComputableInPolyTime.of_eq (nativeContractedSourceCompiler decider (nativeThreeDMOffsetCompiler decider horizontal))
  intro s
  apply List.map_congr_left
  intro edge member
  have data := contractedEdge_incidence_members_of_mem (nativeThreeDMProblem decider s) member
  have offset := incidence_offset_reference_of_mem data.1
  cases edge <;> exact congrArg (fun point => Encodable.encode (component horizontal point)) offset

def nativeTargetSubtrahend (horizontal : Bool) (edge : ContractedEdge) : Int :=
  if edge.targetIsElement then 0 else component horizontal edge.targetIncidence.offset

def nativeTargetOffsetCompiler (horizontal : Bool) :
    Compiler (fun s => (nativeThreeDMProblem decider s).contractedEdges)
      (fun _ edge => Encodable.encode (nativeTargetSubtrahend horizontal edge)) := by
  let offsets := nativeThreeDMOffsetCompiler decider horizontal
  let candidates := chooseThree (nativeIncidenceDegreeCompiler decider) offsets (constant offsets 0)
  apply TM2ComputableInPolyTime.of_eq (nativeContractedTargetCompiler decider candidates)
  intro s
  apply List.map_congr_left
  intro edge member
  have data := contractedEdge_incidence_members_of_mem (nativeThreeDMProblem decider s) member
  have atTarget : (nativeThreeDMProblem decider s).incidenceElement edge.targetTag = (edge.color,edge.atom) := by
    cases edge <;> exact incidenceElement_of_mem data.2.1
  have offset := incidence_offset_reference_of_mem data.2.1
  change (if (nativeThreeDMProblem decider s).degree edge.targetTag.color
      ((nativeThreeDMProblem decider s).incidenceElement edge.targetTag).2 = 3 then 0
    else Encodable.encode (component horizontal (nativeThreeDMReference decider s edge.targetTag).offset)) = _
  rw [atTarget]
  cases edge with
  | retained color atom incidence =>
    have degree : (nativeThreeDMProblem decider s).degree color atom = 3 := by
      simpa [ContractedEdge.color,ContractedEdge.atom,ContractedEdge.targetIsElement] using data.2.2
    simp [ContractedEdge.targetTag,ContractedEdge.atom,nativeTargetSubtrahend,ContractedEdge.targetIsElement,degree]
    rfl
  | through color atom first second =>
    have degree : (nativeThreeDMProblem decider s).degree color atom = 2 := by
      simpa [ContractedEdge.color,ContractedEdge.atom,ContractedEdge.targetIsElement] using data.2.2
    simp only [ContractedEdge.targetTag,ContractedEdge.atom,degree,show (2:Nat) ≠ 3 by decide,if_false]
    change Encodable.encode (component horizontal _) = Encodable.encode (component horizontal second.offset)
    exact congrArg (fun point => Encodable.encode (component horizontal point)) offset

def nativeEdgeOffsetCompiler (horizontal : Bool) :
    Compiler (fun s => (nativeThreeDMProblem decider s).contractedEdges)
      (fun _ edge => Encodable.encode (component horizontal edge.toPeriodicEdge.offset)) := by
  let physical := boundedSignedDifference (nativeSourceOffsetCompiler decider horizontal)
    (nativeTargetOffsetCompiler decider horizontal)
    (fun s edge member => by
      have data := contractedEdge_incidence_members_of_mem (nativeThreeDMProblem decider s) member
      have bound := incidence_offset_local (nativeThreeDM_local decider s) _ _ data.1
      cases horizontal <;> simp only [component] <;> omega)
    (fun s edge member => by
      have data := contractedEdge_incidence_members_of_mem (nativeThreeDMProblem decider s) member
      have bound := incidence_offset_local (nativeThreeDM_local decider s) _ _ data.2.1
      unfold nativeTargetSubtrahend
      split
      · decide
      · cases horizontal <;> simp only [component] <;> omega)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  apply List.map_congr_left
  intro edge _
  cases edge <;> cases horizontal <;>
    simp [ContractedEdge.sourceIncidence,ContractedEdge.targetIncidence,nativeTargetSubtrahend,
      ContractedEdge.targetIsElement,ContractedEdge.toPeriodicEdge,component,Cell.sub]

end LeanTrominoes.PeriodicCNFStripReduction
end
