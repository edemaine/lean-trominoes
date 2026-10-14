/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticGraphOrientationNativeSourceFields
import LeanTrominoes.PeriodicThreeDMGraphOrientationEncodingCorrect
import LeanTrominoes.UnaryColumnFilterCompiler
import LeanTrominoes.UnaryColumnOrdinalCompiler
import LeanTrominoes.UnaryColumnKeyedRelation

/-! # Compiled vertex tables and dense names for the native graph reduction -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Turing Gadget PeriodicThreeDM UnaryColumn
variable {Input : Type} {encoding : _root_.LeanTrominoes.FiniteEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language) [Inhabited encoding.Γ]
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 2048

abbrev nativeElementKey (s : List encoding.Γ) (element : WireColor × Nat) : Nat :=
  directSourceFinalHorizontalElementCode (PeriodicCNF.ProgramSource.ofDecider decider) s element

def nativeRetainedElements (s : List encoding.Γ) : List (WireColor × Nat) :=
  (nativeThreeDMElements decider s).filter fun element => (nativeThreeDMProblem decider s).degree element.1 element.2 = 3

omit [Inhabited encoding.Γ] in
theorem nativeElementKeys_nodup (s : List encoding.Γ) :
    ((nativeThreeDMElements decider s).map (nativeElementKey decider s)).Nodup := by
  have unique := directSourceFinalCanonicalElementCodes_nodup (PeriodicCNF.ProgramSource.ofDecider decider) s
  rw [directSourceFinalCanonicalElementCodes_eq_horizontal] at unique
  exact unique

omit [Inhabited encoding.Γ] in
theorem nativeElement_eq_of_key_eq (s : List encoding.Γ) {first second : WireColor × Nat}
    (firstMember : first ∈ nativeThreeDMElements decider s) (secondMember : second ∈ nativeThreeDMElements decider s)
    (equal : nativeElementKey decider s first = nativeElementKey decider s second) : first = second :=
  List.inj_on_of_nodup_map (nativeElementKeys_nodup decider s) firstMember secondMember equal

def nativeElementDegreeCompiler : Compiler (nativeThreeDMElements decider)
    (fun s element => (nativeThreeDMProblem decider s).degree element.1 element.2) := by
  apply TM2ComputableInPolyTime.of_eq
    (directSourceFinalCanonicalElementDegreesComputableInPolyTime (PeriodicCNF.ProgramSource.ofDecider decider))
  intro s
  exact directSourceFinalCanonicalElementDegrees_eq_horizontal (PeriodicCNF.ProgramSource.ofDecider decider) s

def nativeRetainedElementKeyCompiler : Compiler (nativeRetainedElements decider) (nativeElementKey decider) :=
  filterThree (nativeElementDegreeCompiler decider) (nativeThreeDMElementKeyCompiler decider)

def nativeVertexKey (s : List encoding.Γ) : PeriodicThreeDMVertex → Nat
  | .triple index => 2*index
  | .element color atom => 2*nativeElementKey decider s (color,atom)+1

omit [Inhabited encoding.Γ] in
theorem nativeVertices_eq (s : List encoding.Γ) : (nativeThreeDMProblem decider s).contractedGraph.vertices =
    (List.range (nativeThreeDMProblem decider s).triples.length).map PeriodicThreeDMVertex.triple ++
      (nativeRetainedElements decider s).map (fun element => PeriodicThreeDMVertex.element element.1 element.2) := by
  simp only [contractedGraph,tripleVertices,contractedElementVertices]
  unfold contractedElementVerticesForColor
  simp [nativeRetainedElements,nativeThreeDMElements,CountedContractedIncidence.horizontalElementPairs,
    List.filter_flatMap,List.filter_map,List.map_flatMap,Function.comp_def]

def nativeVertexKeyCompiler : Compiler (fun s => (nativeThreeDMProblem decider s).contractedGraph.vertices)
    (nativeVertexKey decider) := by
  let triples := scale (naturalRange (nativeThreeDMTripleCountCompiler decider)) 2
  let elements := add (scale (nativeRetainedElementKeyCompiler decider) 2)
    (constant (nativeRetainedElementKeyCompiler decider) 1)
  let physical := UnaryFieldClosure.appendCompiler id _ _ triples elements
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  dsimp only
  rw [nativeVertices_eq decider s]
  simp [nativeVertexKey,List.map_map,Function.comp_def,Nat.mul_comm]

def nativeVertexOrdinalCompiler : Compiler (fun s => (nativeThreeDMProblem decider s).contractedGraph.vertices)
    (fun s vertex => (nativeThreeDMProblem decider s).contractedGraph.vertices.idxOf vertex) :=
  ordinal (nativeVertexKeyCompiler decider) (fun s => contractedGraph_vertices_nodup (nativeThreeDMProblem decider s))

def nativeVertexKindCompiler : Compiler (fun s => (nativeThreeDMProblem decider s).contractedGraph.vertices)
    (fun _ vertex => (GraphOrientationEncoding.vertexKind vertex).toNat) := by
  let triples := constant (naturalRange (nativeThreeDMTripleCountCompiler decider)) 1
  let elements := constant (nativeRetainedElementKeyCompiler decider) 0
  let physical := UnaryFieldClosure.appendCompiler id _ _ triples elements
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  dsimp only
  rw [nativeVertices_eq decider s]
  simp [GraphOrientationEncoding.vertexKind,List.map_map,Function.comp_def]

def nativeVertexCountCompiler : ScalarCompiler (fun s => (nativeThreeDMProblem decider s).contractedGraph.vertices.length) :=
  countRows (nativeVertexKeyCompiler decider)

omit [Inhabited encoding.Γ] in
theorem nativeVertexKey_injective_on (s : List encoding.Γ) :
    Set.InjOn (nativeVertexKey decider s) {vertex | vertex ∈ (nativeThreeDMProblem decider s).contractedGraph.vertices} := by
  intro first firstMember second secondMember equal
  rw [nativeVertices_eq] at firstMember secondMember
  cases first with
  | triple firstIndex =>
    cases second with
    | triple secondIndex =>
      have same : firstIndex = secondIndex := by
        simp only [nativeVertexKey] at equal
        omega
      rw [same]
    | element color atom => simp only [nativeVertexKey] at equal; omega
  | element firstColor firstAtom =>
    cases second with
    | triple index => simp only [nativeVertexKey] at equal; omega
    | element secondColor secondAtom =>
      have elementMember {color : WireColor} {atom : Nat}
          (member : PeriodicThreeDMVertex.element color atom ∈
            (List.range (nativeThreeDMProblem decider s).triples.length).map PeriodicThreeDMVertex.triple ++
              (nativeRetainedElements decider s).map (fun element => PeriodicThreeDMVertex.element element.1 element.2)) :
          (color,atom) ∈ nativeThreeDMElements decider s := by
        simp only [List.mem_append,List.mem_map] at member
        rcases member with ⟨index,_,impossible⟩ | ⟨element,elementMember,equal⟩
        · cases impossible
        · have same : element = (color,atom) := by cases element; simpa using equal
          subst element
          exact (List.mem_filter.mp elementMember).1
      have same : (firstColor,firstAtom) = (secondColor,secondAtom) :=
        nativeElement_eq_of_key_eq decider s (elementMember firstMember) (elementMember secondMember)
          (by simp only [nativeVertexKey] at equal; omega)
      cases same
      rfl

def nativeIncidenceDegreeCompiler : Compiler (nativeThreeDMIncidences decider)
    (fun s tag => (nativeThreeDMProblem decider s).degree tag.color
      ((nativeThreeDMProblem decider s).incidenceElement tag).2) := by
  apply keyedRelation (nativeThreeDMIncidenceKeyCompiler decider)
    (nativeThreeDMElementKeyCompiler decider) (nativeElementDegreeCompiler decider)
  · intro s first firstMember second secondMember equal
    have same := nativeElement_eq_of_key_eq decider s firstMember secondMember equal
    rw [same]
  · intro s tag member
    exact ⟨_,nativeThreeDMIncidenceElement_mem decider s tag member,rfl⟩
  · intro s tag member element elementMember equal
    have same := nativeElement_eq_of_key_eq decider s elementMember
      (nativeThreeDMIncidenceElement_mem decider s tag member) equal
    rw [same]
    rfl

end LeanTrominoes.PeriodicCNFStripReduction
end
