/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.Reduction.Program.ProgramGraphOrientationSourceFields
import LeanTrominoes.Graphs.Orientation.Normalization.PeriodicThreeDMGraphOrientationEncodingCorrect
import LeanTrominoes.Computation.Encoding.Unary.UnaryColumnFilterCompiler
import LeanTrominoes.Computation.Encoding.Unary.UnaryColumnOrdinalCompiler
import LeanTrominoes.Computation.Encoding.Unary.UnaryColumnKeyedRelation

/-! # Compiled vertex tables and dense names for the program graph reduction -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Turing Gadget PeriodicThreeDM UnaryColumn
variable {Input : Type} {encoding : _root_.LeanTrominoes.FiniteEncoding Input} {language : Input → Prop}
variable (source : PeriodicCNF.ProgramSource encoding language) [Inhabited encoding.Γ]
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 2048

abbrev programElementKey (s : List encoding.Γ) (element : WireColor × Nat) : Nat :=
  directSourceFinalHorizontalElementCode source s element

def programRetainedElements (s : List encoding.Γ) : List (WireColor × Nat) :=
  (programThreeDMElements source s).filter fun element => (programThreeDMProblem source s).degree element.1 element.2 = 3

omit [Inhabited encoding.Γ] in
theorem programElementKeys_nodup (s : List encoding.Γ) :
    ((programThreeDMElements source s).map (programElementKey source s)).Nodup := by
  have unique := directSourceFinalCanonicalElementCodes_nodup source s
  rw [directSourceFinalCanonicalElementCodes_eq_horizontal] at unique
  exact unique

omit [Inhabited encoding.Γ] in
theorem programElement_eq_of_key_eq (s : List encoding.Γ) {first second : WireColor × Nat}
    (firstMember : first ∈ programThreeDMElements source s) (secondMember : second ∈ programThreeDMElements source s)
    (equal : programElementKey source s first = programElementKey source s second) : first = second :=
  List.inj_on_of_nodup_map (programElementKeys_nodup source s) firstMember secondMember equal

def programElementDegreeCompiler : Compiler (programThreeDMElements source)
    (fun s element => (programThreeDMProblem source s).degree element.1 element.2) := by
  apply TM2ComputableInPolyTime.of_eq
    (directSourceFinalCanonicalElementDegreesComputableInPolyTime source)
  intro s
  exact directSourceFinalCanonicalElementDegrees_eq_horizontal source s

def programRetainedElementKeyCompiler : Compiler (programRetainedElements source) (programElementKey source) :=
  filterThree (programElementDegreeCompiler source) (programThreeDMElementKeyCompiler source)

def programVertexKey (s : List encoding.Γ) : PeriodicThreeDMVertex → Nat
  | .triple index => 2*index
  | .element color atom => 2*programElementKey source s (color,atom)+1

omit [Inhabited encoding.Γ] in
theorem programVertices_eq (s : List encoding.Γ) : (programThreeDMProblem source s).contractedGraph.vertices =
    (List.range (programThreeDMProblem source s).triples.length).map PeriodicThreeDMVertex.triple ++
      (programRetainedElements source s).map (fun element => PeriodicThreeDMVertex.element element.1 element.2) := by
  simp only [contractedGraph,tripleVertices,contractedElementVertices]
  unfold contractedElementVerticesForColor
  simp [programRetainedElements,programThreeDMElements,CountedContractedIncidence.horizontalElementPairs,
    List.filter_flatMap,List.filter_map,List.map_flatMap,Function.comp_def]

def programVertexKeyCompiler : Compiler (fun s => (programThreeDMProblem source s).contractedGraph.vertices)
    (programVertexKey source) := by
  let triples := scale (naturalRange (programThreeDMTripleCountCompiler source)) 2
  let elements := add (scale (programRetainedElementKeyCompiler source) 2)
    (constant (programRetainedElementKeyCompiler source) 1)
  let physical := UnaryFieldClosure.appendCompiler id _ _ triples elements
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  dsimp only
  rw [programVertices_eq source s]
  simp [programVertexKey,List.map_map,Function.comp_def,Nat.mul_comm]

def programVertexOrdinalCompiler : Compiler (fun s => (programThreeDMProblem source s).contractedGraph.vertices)
    (fun s vertex => (programThreeDMProblem source s).contractedGraph.vertices.idxOf vertex) :=
  ordinal (programVertexKeyCompiler source) (fun s => contractedGraph_vertices_nodup (programThreeDMProblem source s))

def programVertexKindCompiler : Compiler (fun s => (programThreeDMProblem source s).contractedGraph.vertices)
    (fun _ vertex => (GraphOrientationEncoding.vertexKind vertex).toNat) := by
  let triples := constant (naturalRange (programThreeDMTripleCountCompiler source)) 1
  let elements := constant (programRetainedElementKeyCompiler source) 0
  let physical := UnaryFieldClosure.appendCompiler id _ _ triples elements
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  dsimp only
  rw [programVertices_eq source s]
  simp [GraphOrientationEncoding.vertexKind,List.map_map,Function.comp_def]

def programVertexCountCompiler : ScalarCompiler (fun s => (programThreeDMProblem source s).contractedGraph.vertices.length) :=
  countRows (programVertexKeyCompiler source)

omit [Inhabited encoding.Γ] in
theorem programVertexKey_injective_on (s : List encoding.Γ) :
    Set.InjOn (programVertexKey source s) {vertex | vertex ∈ (programThreeDMProblem source s).contractedGraph.vertices} := by
  intro first firstMember second secondMember equal
  rw [programVertices_eq] at firstMember secondMember
  cases first with
  | triple firstIndex =>
    cases second with
    | triple secondIndex =>
      have same : firstIndex = secondIndex := by
        simp only [programVertexKey] at equal
        omega
      rw [same]
    | element color atom => simp only [programVertexKey] at equal; omega
  | element firstColor firstAtom =>
    cases second with
    | triple index => simp only [programVertexKey] at equal; omega
    | element secondColor secondAtom =>
      have elementMember {color : WireColor} {atom : Nat}
          (member : PeriodicThreeDMVertex.element color atom ∈
            (List.range (programThreeDMProblem source s).triples.length).map PeriodicThreeDMVertex.triple ++
              (programRetainedElements source s).map (fun element => PeriodicThreeDMVertex.element element.1 element.2)) :
          (color,atom) ∈ programThreeDMElements source s := by
        simp only [List.mem_append,List.mem_map] at member
        rcases member with ⟨index,_,impossible⟩ | ⟨element,elementMember,equal⟩
        · cases impossible
        · have same : element = (color,atom) := by cases element; simpa using equal
          subst element
          exact (List.mem_filter.mp elementMember).1
      have same : (firstColor,firstAtom) = (secondColor,secondAtom) :=
        programElement_eq_of_key_eq source s (elementMember firstMember) (elementMember secondMember)
          (by simp only [programVertexKey] at equal; omega)
      cases same
      rfl

def programIncidenceDegreeCompiler : Compiler (programThreeDMIncidences source)
    (fun s tag => (programThreeDMProblem source s).degree tag.color
      ((programThreeDMProblem source s).incidenceElement tag).2) := by
  apply keyedRelation (programThreeDMIncidenceKeyCompiler source)
    (programThreeDMElementKeyCompiler source) (programElementDegreeCompiler source)
  · intro s first firstMember second secondMember equal
    have same := programElement_eq_of_key_eq source s firstMember secondMember equal
    rw [same]
  · intro s tag member
    exact ⟨_,programThreeDMIncidenceElement_mem source s tag member,rfl⟩
  · intro s tag member element elementMember equal
    have same := programElement_eq_of_key_eq source s elementMember
      (programThreeDMIncidenceElement_mem source s tag member) equal
    rw [same]
    rfl

end LeanTrominoes.PeriodicCNFStripReduction
end
