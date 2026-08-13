/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRoutedTriples

/-!
# Local and routed incidences in the planar 3DM assembly

The geometric reduction draws each variable module and each clause core
inside a small neighborhood of one source vertex.  The only incidences that
leave such a neighborhood are the three colored connector incidences for a
used variable occurrence.

This file makes that partition precise.  Each typed triple and element has a
gadget site.  A colored incidence is local when its element has the same site
as its triple and its periodic offset is zero.  Every incidence of every
listed triple is then either local or exactly one of the routed occurrence
incidences named in `PeriodicPlanarOneInThreeToThreeDMRoutedTriples`.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

/-- The source gadget neighborhood containing a typed 3DM vertex. -/
inductive GadgetSite (Variable : Type*)
  | variable (atom : Variable)
  | clause (clauseIndex : Nat)
  deriving DecidableEq, Repr

/-- Every triple belongs to its variable module or clause core. -/
def tripleSite {Variable : Type*} : Triple Variable → GadgetSite Variable
  | .ordinary atom _ _ _ => .variable atom
  | .fixedRed atom _ _ => .variable atom
  | .clause clauseIndex _ => .clause clauseIndex

/-- Site containing a red element. -/
def redElementSite {Variable : Type*} :
    RedElement Variable → GadgetSite Variable
  | .cycleLink atom _ => .variable atom
  | .fixedRedInternal atom _ _ => .variable atom
  | .clauseInternal clauseIndex => .clause clauseIndex
  | .clauseTerminal clauseIndex _ => .clause clauseIndex

/-- Site containing a green element. -/
def greenElementSite {Variable : Type*} :
    GreenElement Variable → GadgetSite Variable
  | .ordinaryInternal atom _ _ => .variable atom
  | .fixedRedInternal atom _ _ => .variable atom
  | .clauseInternal clauseIndex => .clause clauseIndex
  | .clauseTerminal clauseIndex _ => .clause clauseIndex

/-- Site containing a blue element. -/
def blueElementSite {Variable : Type*} :
    BlueElement Variable → GadgetSite Variable
  | .ordinaryInternal atom _ _ => .variable atom
  | .fixedRedInternal atom _ _ => .variable atom
  | .clauseInternal clauseIndex => .clause clauseIndex
  | .clauseTerminal clauseIndex _ => .clause clauseIndex

/-- A colored incidence stays inside one gadget neighborhood. -/
def IncidenceIsLocal {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (color : WireColor)
    (triple : Triple Variable) : Prop :=
  match color with
  | .red =>
      redElementSite (tripleReferences source triple).red.atom =
          tripleSite triple ∧
        (tripleReferences source triple).red.offset = (0, 0)
  | .green =>
      greenElementSite (tripleReferences source triple).green.atom =
          tripleSite triple ∧
        (tripleReferences source triple).green.offset = (0, 0)
  | .blue =>
      blueElementSite (tripleReferences source triple).blue.atom =
          tripleSite triple ∧
        (tripleReferences source triple).blue.offset = (0, 0)

/-- A colored incidence is one of the three strands attached to a used
source occurrence. -/
def IncidenceIsRouted {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (color : WireColor)
    (triple : Triple Variable) : Prop :=
  ∃ atom slot,
    atom ∈ occurringVariables source ∧
      slot ∈ usedSlots source atom ∧
      triple = routedOccurrenceTriple source atom slot color

/-- Inside one listed variable-occurrence block, each colored incidence is
local except for the uniquely designated routed connector incidence. -/
theorem occurrenceTriple_incidence_local_or_routed
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (triple : Triple Variable)
    (member : triple ∈ occurrenceTriples source atom slot)
    (color : WireColor) :
    IncidenceIsLocal source color triple ∨
      triple = routedOccurrenceTriple source atom slot color := by
  cases kindEq : occurrenceConnectorKind source atom slot <;>
    cases color <;>
    simp [occurrenceTriples, kindEq, allFixedRedTriples,
      allOrdinaryTriples] at member
  all_goals
    rcases member with
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp [IncidenceIsLocal, routedOccurrenceTriple, kindEq,
        tripleSite, redElementSite, greenElementSite, blueElementSite,
        tripleReferences, ordinaryTripleReferences,
        fixedRedTripleReferences,
        VariableOccurrenceTriple.references,
        FixedRedConnectorTriple.references,
        ordinaryRedElement, ordinaryGreenElement, ordinaryBlueElement,
        fixedRedRedElement, fixedRedGreenElement, fixedRedBlueElement]

/-- Every colored incidence in a clause-core triple is local. -/
theorem clauseTriple_incidence_local
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex : Nat) (set : X3CClauseSet)
    (color : WireColor) :
    IncidenceIsLocal source color (.clause clauseIndex set) := by
  cases color <;> cases set <;>
    simp [IncidenceIsLocal, tripleSite, redElementSite,
      greenElementSite, blueElementSite, tripleReferences,
      clauseTripleReferences, clauseRedElement,
      clauseGreenElement, clauseBlueElement,
      X3CClauseSet.coloredReferences]

/-- Exhaustive incidence partition for the complete typed 3DM problem. -/
theorem triple_incidence_local_or_routed
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (triple : Triple Variable)
    (member : triple ∈ triples source)
    (color : WireColor) :
    IncidenceIsLocal source color triple ∨
      IncidenceIsRouted source color triple := by
  rw [triples, List.mem_append] at member
  rcases member with variableMember | clauseMember
  · rw [variableTriples_eq_occurrenceEntries_flatMap] at variableMember
    rcases List.mem_flatMap.mp variableMember with
      ⟨entry, entryMember, blockMember⟩
    rcases occurrenceTriple_incidence_local_or_routed
        source entry.1 entry.2 triple blockMember color with
      localCase | routed
    · exact Or.inl localCase
    · right
      rcases (mem_occurrenceEntries_iff
        source entry.1 entry.2).mp entryMember with
        ⟨atomMember, slotMember⟩
      exact
        ⟨entry.1, entry.2, atomMember, slotMember, routed⟩
  · rw [clauseTriples] at clauseMember
    rcases List.mem_flatMap.mp clauseMember with
      ⟨clauseIndex, clauseIndexMember, blockMember⟩
    rcases List.mem_map.mp blockMember with
      ⟨set, setMember, rfl⟩
    exact Or.inl
      (clauseTriple_incidence_local
        source clauseIndex set color)

/-- Routed incidences are actual listed triples. -/
theorem triple_mem_of_incidenceIsRouted
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (color : WireColor) (triple : Triple Variable)
    (routed : IncidenceIsRouted source color triple) :
    triple ∈ triples source := by
  rcases routed with
    ⟨atom, slot, atomMember, slotMember, rfl⟩
  exact routedOccurrenceTriple_mem_triples
    source atom slot atomMember slotMember color

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
