/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticGraphOrientation
import Mathlib.Tactic

/-! # A planar cubic colored fragment with a forced inward boundary edge

Two trichromatic vertices connect through three monochromatic channels.
The red channel has one vertex and the dangling boundary edge. The green
and blue channels each have two vertices joined by two parallel edges.
Each double channel forces its two outer edges toward the trichromatic
vertices. Coherence then forces the dangling red edge inward.

This supplies a third incidence when subdividing a colored wire: connecting
the new monochromatic vertex to a sink leaves exactly one of its two wire
incidences inward.
-/
namespace LeanTrominoes.TrichromaticGraphOrientation.ForcedSink
open Gadget PeriodicOneInThree

def graph : Input :=
  ([true,true,false,false,false,false,false,false],
   [(⟨0,2,(0,0)⟩,.red),(⟨1,2,(0,0)⟩,.red),
    (⟨0,3,(0,0)⟩,.green),(⟨1,4,(0,0)⟩,.green),
    (⟨3,4,(0,0)⟩,.green),(⟨3,4,(0,0)⟩,.green),
    (⟨0,5,(0,0)⟩,.blue),(⟨1,6,(0,0)⟩,.blue),
    (⟨5,6,(0,0)⟩,.blue),(⟨5,6,(0,0)⟩,.blue),
    (⟨7,2,(0,0)⟩,.red)])

/-- Vertex seven names the external end and is constrained by the surrounding
graph. The seven genuine vertices all have three correctly colored ends. -/
theorem internal_degrees :
    ∀ vertex < 7, (colors graph vertex).length = 3 ∧
      if graph.1.getD vertex false then
        ∀ color : WireColor, (colors graph vertex).count color = 1
      else ∃ color : WireColor, ∀ c ∈ colors graph vertex, c = color := by
  intro vertex bound
  interval_cases vertex <;>
    simp [graph,colors,endsAt,ends,edgeEnds]
  all_goals intro color; cases color <;> decide +kernel

def Constraints (values : Nat → Bool) : Prop :=
  (values 0 = values 2 ∧ values 2 = values 6) ∧
  (values 1 = values 3 ∧ values 3 = values 7) ∧
  ExactlyOne [values 0,values 1,values 10] ∧
  ExactlyOne [values 2,!values 4,!values 5] ∧
  ExactlyOne [values 3,values 4,values 5] ∧
  ExactlyOne [values 6,!values 8,!values 9] ∧
  ExactlyOne [values 7,values 8,values 9]

theorem constraints_force_inward {values : Nat → Bool} (valid : Constraints values) : values 10 = true := by
  obtain ⟨first,second,red,greenFirst,greenSecond,_,_⟩ := valid
  have green : values 2 = false ∧ values 3 = false := by
    cases h2 : values 2 <;> cases h3 : values 3 <;>
      cases h4 : values 4 <;> cases h5 : values 5 <;>
      simp [ExactlyOne,h2,h3,h4,h5] at greenFirst greenSecond ⊢
  have firstRed : values 0 = false := first.1.trans green.1
  have secondRed : values 1 = false := second.1.trans green.2
  cases boundary : values 10 <;> simp [ExactlyOne,firstRed,secondRed,boundary] at red ⊢

def witness (index : Nat) : Bool := index = 5 ∨ index = 9 ∨ index = 10

theorem witness_valid : Constraints witness := by unfold Constraints; decide +kernel
theorem witness_inward : witness 10 = true := by rfl

def IsInternalOrientation (assignment : Nat → Cell → Bool) : Prop :=
  ∀ cell vertex, vertex < 7 →
    if graph.1.getD vertex false then Coherent assignment cell (incoming graph vertex)
    else ClauseHolds assignment cell (incoming graph vertex)

private theorem coherent_three_false (assignment : Nat → Cell → Bool) (cell : Cell)
    (first second third : Nat) :
    Coherent assignment cell [⟨first,(0,0),false⟩,⟨second,(0,0),false⟩,⟨third,(0,0),false⟩] ↔
      assignment first cell = assignment second cell ∧ assignment second cell = assignment third cell := by
  simp only [Coherent,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    PeriodicLiteral.Holds,Cell.add]
  simp only [Int.add_zero,Prod.mk.eta]
  cases assignment first cell <;> cases assignment second cell <;> cases assignment third cell <;> decide

theorem internal_orientation_iff (assignment : Nat → Cell → Bool) :
    IsInternalOrientation assignment ↔ ∀ cell, Constraints (fun edge => assignment edge cell) := by
  have mono (cell : Cell) (vertex : Nat) (bound : vertex < 7) :
      (if graph.1.getD vertex false then Coherent assignment cell (incoming graph vertex)
       else ClauseHolds assignment cell (incoming graph vertex)) ↔
      match vertex with
      | 0 => assignment 0 cell = assignment 2 cell ∧ assignment 2 cell = assignment 6 cell
      | 1 => assignment 1 cell = assignment 3 cell ∧ assignment 3 cell = assignment 7 cell
      | 2 => ExactlyOne [assignment 0 cell,assignment 1 cell,assignment 10 cell]
      | 3 => ExactlyOne [assignment 2 cell,!assignment 4 cell,!assignment 5 cell]
      | 4 => ExactlyOne [assignment 3 cell,assignment 4 cell,assignment 5 cell]
      | 5 => ExactlyOne [assignment 6 cell,!assignment 8 cell,!assignment 9 cell]
      | _ => ExactlyOne [assignment 7 cell,assignment 8 cell,assignment 9 cell] := by
    interval_cases vertex <;>
      simp [graph,incoming,endsAt,ends,edgeEnds,coherent_three_false,ClauseHolds,clauseValues,Cell.add,Cell.sub]
  constructor
  · intro valid cell
    exact ⟨(mono cell 0 (by decide)).mp (valid cell 0 (by decide)),
      (mono cell 1 (by decide)).mp (valid cell 1 (by decide)),
      (mono cell 2 (by decide)).mp (valid cell 2 (by decide)),
      (mono cell 3 (by decide)).mp (valid cell 3 (by decide)),
      (mono cell 4 (by decide)).mp (valid cell 4 (by decide)),
      (mono cell 5 (by decide)).mp (valid cell 5 (by decide)),
      (mono cell 6 (by decide)).mp (valid cell 6 (by decide))⟩
  · intro valid cell vertex bound
    apply (mono cell vertex bound).mpr
    have constraints := valid cell
    interval_cases vertex
    · exact constraints.1
    · exact constraints.2.1
    · exact constraints.2.2.1
    · exact constraints.2.2.2.1
    · exact constraints.2.2.2.2.1
    · exact constraints.2.2.2.2.2.1
    · exact constraints.2.2.2.2.2.2

theorem internal_orientation_forces_boundary {assignment : Nat → Cell → Bool}
    (valid : IsInternalOrientation assignment) (cell : Cell) : assignment 10 cell = true :=
  constraints_force_inward ((internal_orientation_iff assignment).mp valid cell)

theorem internal_orientation_exists : IsInternalOrientation (fun edge _ => witness edge) :=
  (internal_orientation_iff _).mpr (fun _ => witness_valid)

theorem wire_vertex_iff (sourceIn targetIn : Bool) :
    ExactlyOne [sourceIn,targetIn,false] ↔ sourceIn = !targetIn := by
  cases sourceIn <;> cases targetIn <;> decide +kernel

end LeanTrominoes.TrichromaticGraphOrientation.ForcedSink
