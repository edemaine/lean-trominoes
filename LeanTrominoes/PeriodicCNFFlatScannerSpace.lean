/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFlatScanner
import LeanTrominoes.PartrecBinaryLengthSpace

/-! # Linear binary storage for flat CNF scanner states -/
namespace LeanTrominoes.PeriodicCNF.FlatScanner
open Turing.PartrecToTM2 PeriodicCNFFlatEncoding

private theorem space_append (a b : List Nat) :
    encodedListSpace (a++b) = encodedListSpace a+encodedListSpace b := by
  induction a with
  | nil => simp
  | cons x xs ih => simp [ih]; omega

theorem pending_space_step (s : State) :
    encodedListSpace s.step.pending ≤ encodedListSpace s.pending := by
  rcases s with ⟨cursor,current,clauses,cm,lm⟩
  cases current with
  | cons l ls => simp [State.step,State.pending,literalFields]; omega
  | nil => cases clauses <;> simp [State.step,State.pending,clauseFields]

theorem pending_space_iterate (s : State) (n : Nat) :
    encodedListSpace ((State.step^[n]) s).pending ≤ encodedListSpace s.pending := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply']; exact (pending_space_step _).trans ih

theorem counts_le_pending (s : State) :
    s.current.length ≤ s.pending.length ∧ s.clauses.length ≤ s.pending.length := by
  have h := remainingSteps_le_pending s
  have hc : s.clauses.length ≤ (s.clauses.map fun c => c.length+1).sum := by
    induction s.clauses with
    | nil => simp
    | cons c cs ih => simp only [List.length_cons,List.map_cons,List.sum_cons]; omega
  unfold State.remainingSteps at h
  omega

/-- All five scalar fields and the unread input occupy linear binary space,
independently of identifier and offset magnitudes. -/
theorem state_space_bound (f : PeriodicCNF Nat) (n : Nat) :
    encodedListSpace ((State.step^[n]) (initial f)).fields ≤
      6*encodedListSpace (formulaFields f)+5 := by
  let s := (State.step^[n]) (initial f)
  let input := encodedListSpace (formulaFields f)
  have len : (formulaFields f).length ≤ input := list_length_le_encodedListSpace _
  have inv := cursor_pending_iterate (initial f) n
  rw [initial_budget] at inv
  change s.cursor+s.pending.length = (formulaFields f).length at inv
  have cnt := counts_le_pending s
  have masks := masks_bound f n
  change s.cursor ≤ _ ∧ s.clauseMask < _ ∧ s.literalMask < _ at masks
  have bc : (Computability.encodeNat s.cursor).length ≤ input :=
    (encodeNat_length_le_self _).trans (masks.1.trans len)
  have bl : (Computability.encodeNat s.current.length).length ≤ input :=
    (encodeNat_length_le_self _).trans (by omega)
  have bn : (Computability.encodeNat s.clauses.length).length ≤ input :=
    (encodeNat_length_le_self _).trans (by omega)
  have bm := (encodeNat_length_le_of_lt_pow _ _ masks.2.1).trans len
  have bk := (encodeNat_length_le_of_lt_pow _ _ masks.2.2).trans len
  have bp : encodedListSpace s.pending ≤ input := by
    have h := pending_space_iterate (initial f) n
    have h0 : encodedListSpace (initial f).pending ≤ input := by
      simp [input,initial,State.pending,formulaFields]
    exact h.trans h0
  change encodedListSpace s.fields ≤ 6*input+5
  simp only [State.fields,space_append,encodedListSpace_cons,encodedListSpace_nil]
  omega

theorem state_space_bound_encoding (f : PeriodicCNF Nat) (n : Nat) :
    encodedListSpace ((State.step^[n]) (initial f)).fields ≤
      6*(finEncoding.encode f).length+5 := by
  simpa only [finEncoding_encode_length,encodedListSpace_eq_sum] using state_space_bound f n

end LeanTrominoes.PeriodicCNF.FlatScanner
