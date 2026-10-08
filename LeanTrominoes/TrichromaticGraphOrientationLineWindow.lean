/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticGraphOrientationLineDecision
import LeanTrominoes.LocalWindowCycle

/-! # Three-column windows with one bit per colored edge -/
namespace LeanTrominoes.TrichromaticGraphOrientation.LineWindow
open Gadget PeriodicOneInThree
set_option maxHeartbeats 1000000

abbrev Column (input : Input) := Fin input.2.length → Bool
abbrev Window (input : Input) := LocalWindow.Window (Column input) 2

def value (input : Input) (edge : Nat) (column : Column input) : Bool :=
  if bound : edge < input.2.length then column ⟨edge,bound⟩ else false

def position (offset : Int) : Fin 3 := ⟨(offset+1).toNat%3,Nat.mod_lt _ (by decide)⟩

def assignment (input : Input) (window : Window input) : Nat → Cell → Bool :=
  fun edge cell => value input edge (window (position cell.1))

def Valid (input : Input) (window : Window input) : Prop :=
  ∀ vertex, vertex < input.1.length →
    if input.1.getD vertex false then Coherent (assignment input window) (0,0) (incoming input vertex)
    else ClauseHolds (assignment input window) (0,0) (incoming input vertex)

theorem incoming_atom_lt {input : Input} {vertex : Nat} {literal : PeriodicLiteral Nat}
    (member : literal ∈ incoming input vertex) : literal.atom < input.2.length := by
  obtain ⟨incidence,incidenceMember,rfl⟩ := List.mem_map.mp member
  obtain ⟨tagged,taggedMember,endMember⟩ := List.mem_flatMap.mp ((List.mem_filter.mp incidenceMember).1)
  simp only [edgeEnds,List.mem_cons,List.not_mem_nil,or_false] at endMember
  rcases endMember with rfl | rfl <;> exact List.snd_lt_of_mem_zipIdx taggedMember

theorem incoming_horizontal {input : Input} (horizontal : IsOneDimensional input)
    {vertex : Nat} {literal : PeriodicLiteral Nat} (member : literal ∈ incoming input vertex) :
    literal.offset.2 = 0 := by
  obtain ⟨record,recordMember,zero | reversed⟩ := incoming_offset member
  · simp [zero]
  · simp [reversed,Cell.sub,horizontal record recordMember]

theorem position_eq {input : Input} (locality : IsLocal input)
    {vertex : Nat} {literal : PeriodicLiteral Nat} (member : literal ∈ incoming input vertex) :
    (position literal.offset.1).val = literal.offset.1+1 := by
  have small : literal.offset.1.natAbs ≤ 1 := by
    obtain ⟨record,recordMember,zero | reversed⟩ := incoming_offset member
    · simp [zero]
    · have bounds := locality record recordMember
      simp only [PeriodicEdge.span] at bounds
      simp only [reversed,Cell.sub,Int.zero_sub,Int.natAbs_neg]
      omega
  have positive : 0 ≤ literal.offset.1+1 := by omega
  have bound : (literal.offset.1+1).toNat < 3 := by omega
  simp only [position,Nat.mod_eq_of_lt bound,Int.toNat_of_nonneg positive]

private theorem coherent_bool (a : Nat → Cell → Bool) (cell : Cell) (literals : PeriodicClause Nat) :
    Coherent a cell literals ↔ ∀ l ∈ literals, ∀ r ∈ literals,
      (a l.atom (Cell.add cell l.offset) == l.value) = (a r.atom (Cell.add cell r.offset) == r.value) := by
  have holds (l : PeriodicLiteral Nat) : l.Holds a cell ↔ (a l.atom (Cell.add cell l.offset) == l.value) = true := by
    simp [PeriodicLiteral.Holds]
  have boolEq (first second : Bool) : (first = true ↔ second = true) ↔ first = second := by
    cases first <;> cases second <;> decide
  simp only [Coherent]
  simp_rw [holds,boolEq]

theorem vertex_constraint_congr (input : Input) (vertex : Nat) (a b : Nat → Cell → Bool) (firstCell secondCell : Cell)
    (equal : ∀ literal ∈ incoming input vertex,
      (a literal.atom (Cell.add firstCell literal.offset) == literal.value) =
        (b literal.atom (Cell.add secondCell literal.offset) == literal.value)) :
    (if input.1.getD vertex false then Coherent a firstCell (incoming input vertex)
      else ClauseHolds a firstCell (incoming input vertex)) ↔
    (if input.1.getD vertex false then Coherent b secondCell (incoming input vertex)
      else ClauseHolds b secondCell (incoming input vertex)) := by
  split
  · rw [coherent_bool,coherent_bool]
    constructor <;> intro h first firstMember second secondMember
    · rw [← equal first firstMember,← equal second secondMember]; exact h first firstMember second secondMember
    · rw [equal first firstMember,equal second secondMember]; exact h first firstMember second secondMember
  · unfold ClauseHolds clauseValues
    rw [List.map_congr_left equal]

theorem hasOrientation_iff (input : Input) (horizontal : IsOneDimensional input) (locality : IsLocal input) :
    HasOrientation input ↔ LocalWindow.Satisfiable 2 (Valid input) := by
  constructor
  · rintro ⟨a,oriented⟩
    refine ⟨fun x edge => a edge.val (x,0),?_⟩
    intro x vertex vertexBound
    apply (vertex_constraint_congr input vertex a _ (x+1,0) (0,0) ?_).mp
      (oriented (x+1,0) vertex vertexBound)
    intro literal member
    have index := incoming_atom_lt member
    have place := position_eq locality member
    have vertical := incoming_horizontal horizontal member
    simp only [assignment,value,dif_pos index,LocalWindow.windowAt,Cell.add,Int.zero_add,vertical]
    congr 2
    apply Prod.ext <;> omega
  · rintro ⟨configuration,valid⟩
    refine ⟨fun edge cell => value input edge (configuration cell.1),?_⟩
    intro cell vertex vertexBound
    apply (vertex_constraint_congr input vertex _ _ (0,0) cell ?_).mp
      (valid (cell.1-1) vertex vertexBound)
    intro literal member
    have place := position_eq locality member
    simp only [assignment,LocalWindow.windowAt,Cell.add,Int.zero_add]
    congr 3
    omega

theorem hasOrientation_iff_cycle (input : Input) (horizontal : IsOneDimensional input) (locality : IsLocal input) :
    HasOrientation input ↔ FiniteState.HasCycle (LocalWindow.Transition (Valid input)) := by
  rw [hasOrientation_iff input horizontal locality,LocalWindow.satisfiable_iff_cycle]

theorem card_window (input : Input) : Fintype.card (Window input) = 2^(3*input.2.length) := by
  simp only [Window,LocalWindow.Window,Column,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
  rw [← pow_mul,Nat.mul_comm]

end LeanTrominoes.TrichromaticGraphOrientation.LineWindow
