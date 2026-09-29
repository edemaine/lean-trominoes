/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.HornIndexedInput
import LeanTrominoes.HornWorklistSemantics

/-! # Correctness of the dense-index worklist solver, including negative clauses -/
namespace LeanTrominoes.Horn.Indexed
open Worklist
variable {n : Nat}

def extension (model : Fin n → Prop) : Option (Fin n) → Prop
  | none => False
  | some a => model a

theorem satisfies_indexed (input : Input n) (model : Fin n → Prop) :
    Satisfies input.rules.toList model ↔ ∀ r : RuleId input, input.rules[r].Holds model := by
  constructor
  · intro h r
    exact h _ (Array.getElem_mem_toList r.isLt)
  · intro h rule member
    obtain ⟨i,hi,rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
    exact h ⟨i,hi⟩

theorem premises_extension (input : Input n) (model : Fin n → Prop) (r : RuleId input) :
    (∀ a, (a,r) ∈ edges input → extension model a) ↔ ∀ a ∈ input.rules[r].premises, model a := by
  constructor
  · intro h a ha
    exact h (some a) ((mem_edges input (some a) r).mpr ⟨a,ha,rfl⟩)
  · intro h a ha
    obtain ⟨v,hv,rfl⟩ := (mem_edges input a r).mp ha
    exact h v hv

theorem closed_extension (input : Input n) (model : Fin n → Prop) :
    Closed (edges input) (head input) (extension model) ↔ Satisfies input.rules.toList model := by
  rw [satisfies_indexed]
  unfold Closed
  apply forall_congr'
  intro r
  rw [premises_extension]
  unfold head Rule.Holds
  cases input.rules[r.val].conclusion <;> rfl

def state (input : Input n) : State (Option (Fin n)) (RuleId input) := solve (edges input) (head input)
def check (input : Input n) : Bool := !(state input).seen none
def model (input : Input n) (a : Fin n) : Bool := (state input).seen (some a)

theorem model_correct (input : Input n) (accepted : check input=true) :
    Satisfies input.rules.toList (fun a => model input a=true) := by
  have bottom : (state input).seen none=false := by simpa [check] using accepted
  apply (closed_extension input _).mp
  have same : extension (fun a => model input a=true)=(fun a => (state input).seen a=true) := by
    funext a
    cases a <;> simp [extension,model,bottom]
  rw [same]
  exact solve_closed (edges input) (head input)

theorem check_correct (input : Input n) : check input=true ↔ Satisfiable input.rules.toList := by
  constructor
  · intro h
    exact ⟨_,model_correct input h⟩
  · rintro ⟨model,satisfied⟩
    have closed := (closed_extension input model).mpr satisfied
    have absent : (state input).seen none ≠ true := by
      intro known
      exact solve_least (edges input) (head input) (extension model) closed none known
    unfold check
    cases seen : (state input).seen none <;> simp_all

theorem agrees_with_scan (input : Input n) : check input=Horn.check input.rules.toList := by
  have iff := (check_correct input).trans (Horn.check_correct input.rules.toList).symm
  cases ha : check input <;> cases hb : Horn.check input.rules.toList <;> simp_all

theorem model_least (input : Input n) (other : Fin n → Prop) (h : Satisfies input.rules.toList other)
    (a : Fin n) (known : model input a=true) : other a :=
  solve_least (edges input) (head input) (extension other) ((closed_extension input other).mpr h) (some a) known

end LeanTrominoes.Horn.Indexed
