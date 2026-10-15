/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientation
import LeanTrominoes.ThreeDM.FiniteThreeDMContractionOffsets
import LeanTrominoes.Graphs.Orientation.Normalization.PeriodicThreeDMGraphOrientationEncodingCorrect
import LeanTrominoes.ThreeDM.FiniteThreeDMSemantics

/-! # Ordinary finite colored graph orientation -/
namespace LeanTrominoes.TrichromaticGraphOrientation
open Gadget

def ZeroOffsets (graph : Input) : Prop := ∀ record ∈ graph.2, record.1.offset = (0,0)

def FiniteIsOrientation (graph : Input) (assignment : Nat → Bool) : Prop :=
  IsOrientation graph (fun edge _ => assignment edge)

def FiniteHasOrientation (graph : Input) : Prop := ∃ assignment, FiniteIsOrientation graph assignment

def FiniteProblem (graph : Input) : Prop :=
  IsWellFormed graph ∧ ZeroOffsets graph ∧ FiniteHasOrientation graph

theorem ends_offset_eq_zero {graph : Input} (zero : ZeroOffsets graph) {incidence : End}
    (member : incidence ∈ ends graph) : incidence.2.1.offset = (0,0) := by
  obtain ⟨tagged,taggedMember,incidenceMember⟩ := List.mem_flatMap.mp member
  have data := List.mem_zipIdx' taggedMember
  have recordMember : tagged.1 ∈ graph.2 := by
    rw [data.2]
    exact List.getElem_mem data.1
  simp only [edgeEnds,List.mem_cons,List.not_mem_nil,or_false] at incidenceMember
  rcases incidenceMember with rfl | rfl
  · rfl
  · change Cell.sub (0,0) tagged.1.1.offset = (0,0)
    rw [zero _ recordMember]
    rfl

theorem incoming_offset_eq_zero {graph : Input} (zero : ZeroOffsets graph) {vertex : Nat}
    {literal : PeriodicLiteral Nat} (member : literal ∈ incoming graph vertex) : literal.offset = (0,0) := by
  obtain ⟨incidence,incidenceMember,rfl⟩ := List.mem_map.mp member
  exact ends_offset_eq_zero zero (List.mem_of_mem_filter incidenceMember)

theorem freeze_orientation {graph : Input} (zero : ZeroOffsets graph) {assignment : Nat → Cell → Bool}
    (oriented : IsOrientation graph assignment) :
    FiniteIsOrientation graph (fun edge => assignment edge (0,0)) := by
  intro cell vertex bound
  have original := oriented (0,0) vertex bound
  have literalEq (literal : PeriodicLiteral Nat) (member : literal ∈ incoming graph vertex) :
      literal.Holds (fun edge _ => assignment edge (0,0)) cell ↔ literal.Holds assignment (0,0) := by
    simp [PeriodicLiteral.Holds,incoming_offset_eq_zero zero member,Cell.add]
  cases kind : graph.1.getD vertex false with
  | true =>
    simp only [kind,if_true] at original ⊢
    intro first firstMember second secondMember
    exact (literalEq first firstMember).trans ((original first firstMember second secondMember).trans
      (literalEq second secondMember).symm)
  | false =>
    simp only [kind,Bool.false_eq_true,if_false] at original ⊢
    have values : PeriodicOneInThree.clauseValues (fun edge _ => assignment edge (0,0)) cell (incoming graph vertex) =
        PeriodicOneInThree.clauseValues assignment (0,0) (incoming graph vertex) := by
      apply List.map_congr_left
      intro literal member
      simp [incoming_offset_eq_zero zero member,Cell.add]
    unfold PeriodicOneInThree.ClauseHolds
    rw [values]
    exact original

theorem finiteHasOrientation_iff {graph : Input} (zero : ZeroOffsets graph) :
    FiniteHasOrientation graph ↔ HasOrientation graph := by
  constructor
  · rintro ⟨assignment,oriented⟩
    exact ⟨fun edge _ => assignment edge,oriented⟩
  · rintro ⟨assignment,oriented⟩
    exact ⟨_,freeze_orientation zero oriented⟩

theorem finiteProblem_iff {graph : Input} (zero : ZeroOffsets graph) : FiniteProblem graph ↔ Problem graph := by
  simp only [FiniteProblem,Problem,and_iff_right zero,finiteHasOrientation_iff zero]

end LeanTrominoes.TrichromaticGraphOrientation

namespace LeanTrominoes.PeriodicThreeDM.GraphOrientationEncoding
open TrichromaticGraphOrientation

theorem input_zeroOffsets {problem : PeriodicThreeDM} (zero : problem.ZeroOffsets) :
    TrichromaticGraphOrientation.ZeroOffsets (input problem) := by
  intro record member
  obtain ⟨edge,edgeMember,rfl⟩ := List.mem_map.mp member
  exact contractedEdge_offset_eq_zero zero edgeMember

theorem finiteProblem_iff (problem : PeriodicThreeDM) (zero : problem.ZeroOffsets)
    (wellFormed : problem.IsWellFormed) (degree : problem.DegreeTwoOrThree) :
    FiniteProblem (input problem) ↔ problem.FiniteSatisfiable := by
  rw [TrichromaticGraphOrientation.finiteProblem_iff (input_zeroOffsets zero),
    problem_iff problem wellFormed degree,PeriodicThreeDM.finiteSatisfiable_iff problem zero]

end LeanTrominoes.PeriodicThreeDM.GraphOrientationEncoding
