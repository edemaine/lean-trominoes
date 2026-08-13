/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTransition

/-!
# Forward-local CNF gate library

This file supplies constant-size Tseitin encodings for the Boolean gates used
to compile a bounded machine transition into horizontal periodic CNF.  A wire
may read an atom from the current or next time slice; gate outputs live in the
current slice and therefore serve as edge-local auxiliary variables.
-/

namespace LeanTrominoes

namespace PeriodicCNF

/-- Which endpoint of one transition a Boolean wire reads. -/
inductive TransitionSlice
  | current
  | next
  deriving DecidableEq, Repr

/-- A Boolean atom read from the current or next time slice. -/
structure TransitionWire where
  slice : TransitionSlice
  atom : Nat
  deriving DecidableEq, Repr

namespace TransitionWire

/-- Value carried by a transition wire under two consecutive assignments. -/
def value (wire : TransitionWire) (current next : Nat → Bool) : Bool :=
  match wire.slice with
  | .current => current wire.atom
  | .next => next wire.atom

/-- Convert a transition wire and desired polarity to a periodic literal. -/
def literal (wire : TransitionWire) (desired : Bool) :
    PeriodicLiteral Nat where
  atom := wire.atom
  offset := match wire.slice with
    | .current => (0, 0)
    | .next => (1, 0)
  value := desired

@[simp]
theorem literal_isForwardLocal (wire : TransitionWire) (desired : Bool) :
    (wire.literal desired).IsForwardLocal := by
  cases wire with
  | mk slice atom =>
      cases slice <;> simp [literal, PeriodicLiteral.IsForwardLocal]

@[simp]
theorem literal_holdsBetween_iff (wire : TransitionWire)
    (desired : Bool) (current next : Nat → Bool) :
    (wire.literal desired).HoldsBetween current next ↔
      wire.value current next = desired := by
  cases wire with
  | mk slice atom =>
      cases slice <;>
        simp [literal, value, PeriodicLiteral.HoldsBetween]

end TransitionWire

/-- A conjunction of clauses evaluated between two consecutive states. -/
def ClausesHoldBetween (current next : Nat → Bool)
    (clauses : List (PeriodicClause Nat)) : Prop :=
  ∀ clause ∈ clauses, clause.HoldsBetween current next

/-- A gate output is always an edge-local current-slice atom. -/
def gateOutput (atom : Nat) : TransitionWire :=
  ⟨.current, atom⟩

@[simp]
theorem gateOutput_value (atom : Nat) (current next : Nat → Bool) :
    (gateOutput atom).value current next = current atom :=
  rfl

/-- Unit clause fixing an output atom to a constant. -/
def constantClauses (output : Nat) (value : Bool) :
    List (PeriodicClause Nat) :=
  [[(gateOutput output).literal value]]

/-- Tseitin clauses for `output = input`. -/
def equalityClauses (output : Nat) (input : TransitionWire) :
    List (PeriodicClause Nat) :=
  [[(gateOutput output).literal false, input.literal true],
    [(gateOutput output).literal true, input.literal false]]

/-- Tseitin clauses for `output = !input`. -/
def notClauses (output : Nat) (input : TransitionWire) :
    List (PeriodicClause Nat) :=
  [[(gateOutput output).literal false, input.literal false],
    [(gateOutput output).literal true, input.literal true]]

/-- Tseitin clauses for `output = first && second`. -/
def andClauses (output : Nat) (first second : TransitionWire) :
    List (PeriodicClause Nat) :=
  [[(gateOutput output).literal false, first.literal true],
    [(gateOutput output).literal false, second.literal true],
    [(gateOutput output).literal true, first.literal false,
      second.literal false]]

/-- Tseitin clauses for `output = first || second`. -/
def orClauses (output : Nat) (first second : TransitionWire) :
    List (PeriodicClause Nat) :=
  [[(gateOutput output).literal true, first.literal false],
    [(gateOutput output).literal true, second.literal false],
    [(gateOutput output).literal false, first.literal true,
      second.literal true]]

private theorem clauses_forward
    (clauses : List (PeriodicClause Nat))
    (all : ∀ clause ∈ clauses, ∀ literal ∈ clause,
      literal.IsForwardLocal) :
    (⟨clauses⟩ : PeriodicCNF Nat).IsForwardLocal :=
  all

@[simp]
theorem constantClauses_forward (output : Nat) (value : Bool) :
    (⟨constantClauses output value⟩ : PeriodicCNF Nat).IsForwardLocal := by
  apply clauses_forward
  simp [constantClauses]

@[simp]
theorem equalityClauses_forward (output : Nat) (input : TransitionWire) :
    (⟨equalityClauses output input⟩ : PeriodicCNF Nat).IsForwardLocal := by
  apply clauses_forward
  simp [equalityClauses]

@[simp]
theorem notClauses_forward (output : Nat) (input : TransitionWire) :
    (⟨notClauses output input⟩ : PeriodicCNF Nat).IsForwardLocal := by
  apply clauses_forward
  simp [notClauses]

@[simp]
theorem andClauses_forward (output : Nat)
    (first second : TransitionWire) :
    (⟨andClauses output first second⟩ : PeriodicCNF Nat).IsForwardLocal := by
  apply clauses_forward
  simp [andClauses]

@[simp]
theorem orClauses_forward (output : Nat)
    (first second : TransitionWire) :
    (⟨orClauses output first second⟩ : PeriodicCNF Nat).IsForwardLocal := by
  apply clauses_forward
  simp [orClauses]

@[simp]
theorem constantClauses_hold_iff (output : Nat) (value : Bool)
    (current next : Nat → Bool) :
    ClausesHoldBetween current next (constantClauses output value) ↔
      current output = value := by
  simp [ClausesHoldBetween, constantClauses,
    PeriodicClause.HoldsBetween]

@[simp]
theorem equalityClauses_hold_iff (output : Nat)
    (input : TransitionWire) (current next : Nat → Bool) :
    ClausesHoldBetween current next (equalityClauses output input) ↔
      current output = input.value current next := by
  cases outputValue : current output <;>
    cases inputValue : input.value current next <;>
    simp [ClausesHoldBetween, equalityClauses,
      PeriodicClause.HoldsBetween,
      outputValue, inputValue]

@[simp]
theorem notClauses_hold_iff (output : Nat)
    (input : TransitionWire) (current next : Nat → Bool) :
    ClausesHoldBetween current next (notClauses output input) ↔
      current output = !(input.value current next) := by
  cases outputValue : current output <;>
    cases inputValue : input.value current next <;>
    simp [ClausesHoldBetween, notClauses,
      PeriodicClause.HoldsBetween,
      outputValue, inputValue]

@[simp]
theorem andClauses_hold_iff (output : Nat)
    (first second : TransitionWire) (current next : Nat → Bool) :
    ClausesHoldBetween current next (andClauses output first second) ↔
      current output =
        (first.value current next && second.value current next) := by
  cases outputValue : current output <;>
    cases firstValue : first.value current next <;>
    cases secondValue : second.value current next <;>
    simp [ClausesHoldBetween, andClauses,
      PeriodicClause.HoldsBetween,
      outputValue, firstValue, secondValue]

@[simp]
theorem orClauses_hold_iff (output : Nat)
    (first second : TransitionWire) (current next : Nat → Bool) :
    ClausesHoldBetween current next (orClauses output first second) ↔
      current output =
        (first.value current next || second.value current next) := by
  cases outputValue : current output <;>
    cases firstValue : first.value current next <;>
    cases secondValue : second.value current next <;>
    simp [ClausesHoldBetween, orClauses,
      PeriodicClause.HoldsBetween,
      outputValue, firstValue, secondValue]

end PeriodicCNF

end LeanTrominoes
