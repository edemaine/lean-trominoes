/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFlatEncoding
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

/-! # A streaming scanner for flat CNF fields

The scanner marks clause headers and literal starts in two binary masks.
It retains the unread field suffix rather than constructing nested lists.
The structured state below is only a proof model for the flat machine state.
-/
namespace LeanTrominoes.PeriodicCNF.FlatScanner
open PeriodicCNFFlatEncoding

structure State where
  cursor : Nat
  current : List (PeriodicLiteral Nat)
  clauses : List (PeriodicClause Nat)
  clauseMask : Nat
  literalMask : Nat
  deriving DecidableEq

def State.pending (s : State) : List Nat :=
  s.current.flatMap literalFields ++ s.clauses.flatMap clauseFields

def State.fields (s : State) : List Nat :=
  [s.cursor,s.current.length,s.clauses.length,s.clauseMask,s.literalMask] ++ s.pending

def State.step (s : State) : State :=
  match s.current with
  | _ :: rest => { s with cursor := s.cursor+4, current := rest, literalMask := s.literalMask+2^s.cursor }
  | [] => match s.clauses with
    | [] => s
    | c :: rest => { s with cursor := s.cursor+1, current := c, clauses := rest, clauseMask := s.clauseMask+2^s.cursor }

/-- The actual transition reads only five scalar fields and the unread suffix. -/
def step (v : List Nat) : List Nat :=
  if v[1]?.getD 0 = 0 then
    if v[2]?.getD 0 = 0 then v
    else [v[0]?.getD 0+1,v[5]?.getD 0,v[2]?.getD 0-1,
      v[3]?.getD 0+2^(v[0]?.getD 0),v[4]?.getD 0] ++ v.drop 6
  else [v[0]?.getD 0+4,v[1]?.getD 0-1,v[2]?.getD 0,
    v[3]?.getD 0,v[4]?.getD 0+2^(v[0]?.getD 0)] ++ v.drop 9

theorem step_fields (s : State) : step s.fields = s.step.fields := by
  rcases s with ⟨cursor,current,clauses,cm,lm⟩
  cases current with
  | cons l ls => simp [step,State.step,State.fields,State.pending,literalFields]
  | nil => cases clauses <;> simp [step,State.step,State.fields,State.pending,clauseFields]

theorem iterate_fields (s : State) (n : Nat) :
    (step^[n]) s.fields = ((State.step^[n]) s).fields := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',Function.iterate_succ_apply',ih,step_fields]

def State.remainingSteps (s : State) : Nat :=
  s.current.length + (s.clauses.map fun c => c.length+1).sum

theorem remainingSteps_step (s : State) : s.step.remainingSteps = s.remainingSteps-1 := by
  rcases s with ⟨cursor,current,clauses,cm,lm⟩
  cases current with
  | cons l ls => simp [State.step,State.remainingSteps]
  | nil => cases clauses <;> simp [State.step,State.remainingSteps]

theorem remainingSteps_iterate (s : State) (n : Nat) :
    ((State.step^[n]) s).remainingSteps = s.remainingSteps-n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply',remainingSteps_step,ih]; omega

theorem pending_length (s : State) :
    s.pending.length = 4*s.current.length + (s.clauses.map fun c => 1+4*c.length).sum := by
  have lits (ls : List (PeriodicLiteral Nat)) : (ls.flatMap literalFields).length = 4*ls.length := by
    induction ls with
    | nil => simp
    | cons l ls ih => simp [literalFields,ih]; omega
  simp only [State.pending,List.length_append,lits,List.length_flatMap]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro c hc
  simp [clauseFields,lits,Nat.add_comm]

theorem cursor_pending_invariant (s : State) :
    s.step.cursor+s.step.pending.length = s.cursor+s.pending.length := by
  rcases s with ⟨cursor,current,clauses,cm,lm⟩
  cases current with
  | cons l ls => simp [State.step,pending_length]; omega
  | nil => cases clauses <;> simp [State.step,pending_length] <;> omega

theorem cursor_pending_iterate (s : State) (n : Nat) :
    ((State.step^[n]) s).cursor+((State.step^[n]) s).pending.length = s.cursor+s.pending.length := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',cursor_pending_invariant,ih]

def State.BoundedMasks (s : State) : Prop := s.clauseMask < 2^s.cursor ∧ s.literalMask < 2^s.cursor

theorem boundedMasks_step (s : State) (h : s.BoundedMasks) : s.step.BoundedMasks := by
  rcases s with ⟨cursor,current,clauses,cm,lm⟩
  change cm < 2^cursor ∧ lm < 2^cursor at h
  cases current with
  | cons l ls =>
    change cm < 2^(cursor+4) ∧ lm+2^cursor < 2^(cursor+4)
    rw [Nat.pow_add]
    norm_num
    constructor <;> omega
  | nil => cases clauses with
    | nil => exact h
    | cons c cs =>
      change cm+2^cursor < 2^(cursor+1) ∧ lm < 2^(cursor+1)
      rw [Nat.pow_succ]
      constructor <;> omega

theorem boundedMasks_iterate (s : State) (h : s.BoundedMasks) (n : Nat) :
    ((State.step^[n]) s).BoundedMasks := by
  induction n with
  | zero => exact h
  | succ n ih => rw [Function.iterate_succ_apply']; exact boundedMasks_step _ ih

def initial (f : PeriodicCNF Nat) : State := ⟨1,[],f.clauses,0,0⟩

theorem initial_budget (f : PeriodicCNF Nat) :
    (initial f).cursor+(initial f).pending.length = (formulaFields f).length := by
  simp [initial,State.pending,formulaFields,Nat.add_comm]

theorem initial_masks (f : PeriodicCNF Nat) : (initial f).BoundedMasks := by
  change 0 < 2^1 ∧ 0 < 2^1
  decide

/-- Neither mask grows beyond the number of fields in the original input. -/
theorem masks_bound (f : PeriodicCNF Nat) (n : Nat) :
    let s := (State.step^[n]) (initial f)
    s.cursor ≤ (formulaFields f).length ∧
    s.clauseMask < 2^(formulaFields f).length ∧ s.literalMask < 2^(formulaFields f).length := by
  dsimp only
  have budget := cursor_pending_iterate (initial f) n
  rw [initial_budget] at budget
  have cursor : ((State.step^[n]) (initial f)).cursor ≤ (formulaFields f).length := by omega
  have masks := boundedMasks_iterate (initial f) (initial_masks f) n
  exact ⟨cursor,masks.1.trans_le (Nat.pow_le_pow_right (by decide) cursor),
    masks.2.trans_le (Nat.pow_le_pow_right (by decide) cursor)⟩

/-- Each productive step consumes at least one flat field. -/
theorem remainingSteps_le_pending (s : State) : s.remainingSteps ≤ s.pending.length := by
  rw [pending_length]
  unfold State.remainingSteps
  have h : (s.clauses.map fun c => c.length+1).sum ≤
      (s.clauses.map fun c => 1+4*c.length).sum := by
    induction s.clauses with
    | nil => simp
    | cons c cs ih => simp only [List.map_cons,List.sum_cons]; omega
  omega

theorem remainingSteps_eq_zero (s : State) :
    s.remainingSteps = 0 ↔ s.current = [] ∧ s.clauses = [] := by
  cases s with
  | mk cursor current clauses cm lm =>
    cases current <;> cases clauses <;> simp [State.remainingSteps]

def scan (f : PeriodicCNF Nat) : State :=
  (State.step^[(formulaFields f).length]) (initial f)

theorem scan_finished (f : PeriodicCNF Nat) :
    (scan f).current = [] ∧ (scan f).clauses = [] := by
  apply (remainingSteps_eq_zero _).mp
  rw [scan,remainingSteps_iterate]
  have h := remainingSteps_le_pending (initial f)
  have b := initial_budget f
  omega

theorem scan_cursor (f : PeriodicCNF Nat) : (scan f).cursor = (formulaFields f).length := by
  have h := cursor_pending_iterate (initial f) (formulaFields f).length
  rw [initial_budget] at h
  change (scan f).cursor+(scan f).pending.length = _ at h
  simpa [State.pending,(scan_finished f).1,(scan_finished f).2] using h

theorem scan_fixed (f : PeriodicCNF Nat) : (scan f).step = scan f := by
  simp [State.step,(scan_finished f).1,(scan_finished f).2]

/-- Clause-header addresses in the flat encoding, represented as a binary sum. -/
def clauseMarks (start : Nat) : List (PeriodicClause Nat) → Nat
  | [] => 0
  | c :: cs => 2^start+clauseMarks (start+1+4*c.length) cs

/-- Consecutive literals occupy four fields each. -/
def literalRunMarks (start : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => 2^start+literalRunMarks (start+4) n

def literalMarks (start : Nat) : List (PeriodicClause Nat) → Nat
  | [] => 0
  | c :: cs => literalRunMarks (start+1) c.length+literalMarks (start+1+4*c.length) cs

def State.finalClauseMask (s : State) : Nat :=
  s.clauseMask+clauseMarks (s.cursor+4*s.current.length) s.clauses

def State.finalLiteralMask (s : State) : Nat :=
  s.literalMask+literalRunMarks s.cursor s.current.length+
    literalMarks (s.cursor+4*s.current.length) s.clauses

theorem finalMasks_step (s : State) :
    s.step.finalClauseMask = s.finalClauseMask ∧
    s.step.finalLiteralMask = s.finalLiteralMask := by
  rcases s with ⟨cursor,current,clauses,cm,lm⟩
  cases current with
  | cons l ls =>
    have he : cursor+4+4*ls.length = cursor+4*(ls.length+1) := by omega
    simp [State.step,State.finalClauseMask,State.finalLiteralMask,literalRunMarks,he,Nat.add_assoc]
  | nil => cases clauses with
    | nil => simp [State.step]
    | cons c cs =>
      simp [State.step,State.finalClauseMask,State.finalLiteralMask,clauseMarks,literalMarks,
        literalRunMarks,Nat.add_assoc]

theorem finalMasks_iterate (s : State) (n : Nat) :
    ((State.step^[n]) s).finalClauseMask = s.finalClauseMask ∧
    ((State.step^[n]) s).finalLiteralMask = s.finalLiteralMask := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨(finalMasks_step _).1.trans ih.1,(finalMasks_step _).2.trans ih.2⟩

/-- The executable scan returns precisely the clause-header and literal-start masks. -/
theorem scan_masks (f : PeriodicCNF Nat) :
    (scan f).clauseMask = clauseMarks 1 f.clauses ∧
    (scan f).literalMask = literalMarks 1 f.clauses := by
  have h := finalMasks_iterate (initial f) (formulaFields f).length
  change (scan f).finalClauseMask = _ ∧ (scan f).finalLiteralMask = _ at h
  simpa [State.finalClauseMask,State.finalLiteralMask,(scan_finished f).1,
    (scan_finished f).2,initial,clauseMarks,literalMarks,literalRunMarks] using h

end LeanTrominoes.PeriodicCNF.FlatScanner
