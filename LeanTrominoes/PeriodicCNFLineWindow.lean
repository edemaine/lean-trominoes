/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFOneDimensional
import LeanTrominoes.PeriodicOccurrences
import LeanTrominoes.LocalWindowCycle

/-! # Three-column windows for local one-dimensional CNF

Columns use one bit per literal occurrence, irrespective of the numerical
size of atom names or offsets. Clauses are evaluated relative to their first
literal, so large common offsets do not enlarge the window.
-/
namespace LeanTrominoes.PeriodicCNF.LineWindow
variable {V : Type} [DecidableEq V]

def anchor (c : PeriodicClause V) : Int := ((c.head?).map fun l => l.offset.1).getD 0

def position (c : PeriodicClause V) (l : PeriodicLiteral V) : Fin 3 :=
  ⟨(l.offset.1-anchor c+1).toNat % 3, Nat.mod_lt _ (by decide)⟩

abbrev Column (f : PeriodicCNF V) := Fin f.variableOccurrences.length → Bool
abbrev Window (f : PeriodicCNF V) := LocalWindow.Window (Column f) 2

def value (f : PeriodicCNF V) (a : V) (column : Column f) : Bool :=
  if h : f.variableOccurrences.idxOf a < f.variableOccurrences.length then
    column ⟨f.variableOccurrences.idxOf a,h⟩ else false

def Valid (f : PeriodicCNF V) (window : Window f) : Prop :=
  ∀ c ∈ f.clauses, ∃ l ∈ c, value f l.atom (window (position c l)) = l.value

omit [DecidableEq V] in
theorem position_eq {c : PeriodicClause V} (locality : c.IsLocalOnLine)
    {l : PeriodicLiteral V} (member : l ∈ c) :
    (position c l).val = l.offset.1-anchor c+1 := by
  cases c with
  | nil => simp at member
  | cons first rest =>
    have bound := locality l member first (by simp)
    have absBound : -1 ≤ l.offset.1-first.offset.1 ∧ l.offset.1-first.offset.1 ≤ 1 := by
      change (l.offset.1-first.offset.1).natAbs ≤ 1 at bound
      omega
    simp only [anchor,List.head?_cons,Option.map_some,Option.getD_some]
    have nonneg : 0 ≤ l.offset.1-first.offset.1+1 := by omega
    have small : (l.offset.1-first.offset.1+1).toNat < 3 := by omega
    simp only [position,anchor,List.head?_cons,Option.map_some,Option.getD_some,
      Nat.mod_eq_of_lt small,Int.toNat_of_nonneg nonneg]

omit [DecidableEq V] in
private theorem atom_mem (f : PeriodicCNF V) {c : PeriodicClause V} (hc : c ∈ f.clauses)
    {l : PeriodicLiteral V} (hl : l ∈ c) : l.atom ∈ f.variableOccurrences := by
  exact List.mem_flatMap.mpr ⟨c,hc,List.mem_map.mpr ⟨l,hl,rfl⟩⟩

theorem value_of_assignment (f : PeriodicCNF V) (a : V) (h : a ∈ f.variableOccurrences)
    (assignment : V → Bool) :
    value f a (fun i => assignment f.variableOccurrences[i]) = assignment a := by
  simp only [value,dif_pos (List.idxOf_lt_length_of_mem h)]
  have bound := List.idxOf_lt_length_of_mem h
  change assignment f.variableOccurrences[f.variableOccurrences.idxOf a] = assignment a
  rw [List.getElem_idxOf]

theorem satisfiable_iff (f : PeriodicCNF V) (locality : f.IsLocalOnLine) :
    f.SatisfiableOnLine ↔ LocalWindow.Satisfiable 2 (Valid f) := by
  constructor
  · rintro ⟨assignment,satisfies⟩
    refine ⟨fun x i => assignment f.variableOccurrences[i] x,?_⟩
    intro x c hc
    obtain ⟨l,hl,holds⟩ := satisfies (x+1-anchor c) c hc
    refine ⟨l,hl,?_⟩
    change value f l.atom (fun i => assignment f.variableOccurrences[i]
      (x+(position c l).val)) = l.value
    rw [value_of_assignment f l.atom (atom_mem f hc hl)
      (fun a => assignment a (x+(position c l).val))]
    have pos := position_eq (locality c hc) hl
    change assignment l.atom ((x+1-anchor c)+l.offset.1) = l.value at holds
    have coordinates : x+(position c l).val = (x+1-anchor c)+l.offset.1 := by omega
    rw [coordinates]
    exact holds
  · rintro ⟨configuration,valid⟩
    refine ⟨fun a x => value f a (configuration x),?_⟩
    intro x c hc
    obtain ⟨l,hl,holds⟩ := valid (x+anchor c-1) c hc
    refine ⟨l,hl,?_⟩
    have pos := position_eq (locality c hc) hl
    change value f l.atom (configuration ((x+anchor c-1)+(position c l).val)) = l.value at holds
    change value f l.atom (configuration (x+l.offset.1)) = l.value
    have coordinates : (x+anchor c-1)+(position c l).val = x+l.offset.1 := by omega
    rw [coordinates] at holds
    exact holds

theorem satisfiable_iff_cycle (f : PeriodicCNF V) (horizontal : f.IsOneDimensional)
    (locality : f.IsLocalOnLine) :
    f.Satisfiable ↔ FiniteState.HasCycle (LocalWindow.Transition (Valid f)) := by
  rw [PeriodicCNF.satisfiable_iff_satisfiableOnLine horizontal,
    satisfiable_iff f locality,LocalWindow.satisfiable_iff_cycle]

omit [DecidableEq V] in
/-- The number of state bits depends on occurrences, not on atom identifiers. -/
theorem card_window (f : PeriodicCNF V) :
    Fintype.card (Window f) = 2 ^ (3*f.variableOccurrences.length) := by
  simp only [Window,LocalWindow.Window,Column,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
  rw [← pow_mul,Nat.mul_comm]

end LeanTrominoes.PeriodicCNF.LineWindow
