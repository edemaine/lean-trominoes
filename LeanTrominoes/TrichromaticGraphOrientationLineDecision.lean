/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticGraphOrientationLocalCoRE
import LeanTrominoes.PeriodicCNFEdgeLocalization
import LeanTrominoes.PeriodicCNFLineSearch

/-! # A total cycle-search decision procedure for ordinary 1D orientation -/
namespace LeanTrominoes.TrichromaticGraphOrientation
open Gadget PeriodicOneInThree
set_option maxHeartbeats 1000000

def IsOneDimensional (input : Input) : Prop := ∀ edge ∈ input.2, edge.1.offset.2 = 0

instance (input : Input) : Decidable (IsOneDimensional input) := by
  unfold IsOneDimensional
  infer_instance

instance (input : Input) : Decidable (IsLocal input) := by
  unfold IsLocal
  infer_instance

instance (input : Input) : Decidable (IsWellFormed input) := by
  unfold IsWellFormed
  infer_instance

theorem incoming_offset {input : Input} {vertex : Nat} {literal : PeriodicLiteral Nat}
    (member : literal ∈ incoming input vertex) :
    ∃ record ∈ input.2, literal.offset = (0,0) ∨ literal.offset = Cell.sub (0,0) record.1.offset := by
  obtain ⟨incidence,incidenceMember,rfl⟩ := List.mem_map.mp member
  have endMember := (List.mem_filter.mp incidenceMember).1
  obtain ⟨tagged,taggedMember,endMember⟩ := List.mem_flatMap.mp endMember
  simp only [edgeEnds,List.mem_cons,List.not_mem_nil,or_false] at endMember
  rcases endMember with rfl | rfl
  · exact ⟨tagged.1,List.fst_mem_of_mem_zipIdx taggedMember,Or.inl rfl⟩
  · exact ⟨tagged.1,List.fst_mem_of_mem_zipIdx taggedMember,Or.inr rfl⟩

private theorem mutex_offsets {V : Type} (predicate : Cell → Prop) (literals : PeriodicClause V)
    (bounds : ∀ literal ∈ literals, predicate literal.offset) :
    ∀ clause ∈ PeriodicExactOneCNF.mutex literals, ∀ literal ∈ clause, predicate literal.offset := by
  induction literals with
  | nil => simp [PeriodicExactOneCNF.mutex]
  | cons first rest ih =>
    intro clause member literal literalMember
    rcases List.mem_append.mp member with pair | tail
    · obtain ⟨second,secondMember,rfl⟩ := List.mem_map.mp pair
      simp only [List.mem_cons,List.not_mem_nil,or_false] at literalMember
      rcases literalMember with rfl | rfl
      · exact bounds first (by simp)
      · exact bounds second (by simp [secondMember])
    · exact ih (fun l hl => bounds l (by simp [hl])) clause tail literal literalMember

theorem vertexClauses_offsets (input : Input) (vertex : Nat) (predicate : Cell → Prop)
    (bounds : ∀ literal ∈ incoming input vertex, predicate literal.offset) :
    ∀ clause ∈ vertexClauses input vertex, ∀ literal ∈ clause, predicate literal.offset := by
  intro clause member literal literalMember
  unfold vertexClauses at member
  split at member
  · obtain ⟨first,firstMember,member⟩ := List.mem_flatMap.mp member
    obtain ⟨second,secondMember,rfl⟩ := List.mem_map.mp member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at literalMember
    rcases literalMember with equal | equal
    · rw [equal]; exact bounds first firstMember
    · rw [equal]; exact bounds second secondMember
  · rcases List.mem_cons.mp member with rfl | mutexMember
    · exact bounds literal literalMember
    · exact mutex_offsets predicate _ bounds clause mutexMember literal literalMember

theorem formula_edgeLocal (input : Input) (locality : IsLocal input) :
    PeriodicCNF.EdgeLocalization.EdgeLocal (formula input) := by
  intro clause member literal literalMember
  obtain ⟨vertex,_,member⟩ := List.mem_flatMap.mp member
  apply vertexClauses_offsets input vertex (fun offset => offset.1.natAbs + offset.2.natAbs ≤ 1) ?_ clause member literal literalMember
  intro l hl
  obtain ⟨record,recordMember,zero | reversed⟩ := incoming_offset hl
  · simp [zero]
  · simpa [reversed,Cell.sub,PeriodicEdge.span] using locality record recordMember

theorem formula_horizontal (input : Input) (horizontal : IsOneDimensional input) :
    (formula input).IsOneDimensional := by
  intro clause member literal literalMember
  obtain ⟨vertex,_,member⟩ := List.mem_flatMap.mp member
  apply vertexClauses_offsets input vertex (fun offset => offset.2 = 0) ?_ clause member literal literalMember
  intro l hl
  obtain ⟨record,recordMember,zero | reversed⟩ := incoming_offset hl
  · simp [zero]
  · simp [reversed,Cell.sub,horizontal record recordMember]

def localFormula (input : Input) : PeriodicCNF (Nat × Cell) :=
  PeriodicCNF.EdgeLocalization.formula (formula input)

theorem localFormula_satisfiable (input : Input) : (localFormula input).Satisfiable ↔ HasOrientation input :=
  (PeriodicCNF.EdgeLocalization.satisfiable_iff _).trans (formula_satisfiable_iff input)

def LocalLineProblem (input : Input) : Prop := LocalProblem input ∧ IsOneDimensional input

def lineCheck (input : Input) : Bool :=
  decide (IsWellFormed input) && decide (IsLocal input) && decide (IsOneDimensional input) &&
    PeriodicCNF.LineWindow.check (localFormula input)

theorem lineCheck_correct (input : Input) : lineCheck input = true ↔ LocalLineProblem input := by
  simp only [lineCheck,Bool.and_eq_true,decide_eq_true_eq,PeriodicCNF.LineWindow.check_correct,
    localFormula_satisfiable,LocalLineProblem,LocalProblem,Problem]
  constructor
  · rintro ⟨⟨⟨wf,locality⟩,horizontal⟩,_,_,oriented⟩
    exact ⟨⟨locality,wf,oriented⟩,horizontal⟩
  · rintro ⟨⟨locality,wf,oriented⟩,horizontal⟩
    exact ⟨⟨⟨wf,locality⟩,horizontal⟩,
      PeriodicCNF.EdgeLocalization.isOneDimensional _ (formula_horizontal input horizontal),
      PeriodicCNF.EdgeLocalization.isLocal _ (formula_edgeLocal input locality),oriented⟩

end LeanTrominoes.TrichromaticGraphOrientation
