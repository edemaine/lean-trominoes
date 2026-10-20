/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMCircuitExpressions

/-! # Arithmetic-expression compiler correctness and execution -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Circuit
open ComplexityAbstract.RAM

theorem Expression.eval_congr {arity : ℕ} {R : Type} [Ring R] (e : Expression arity)
    {first second : Fin arity → R} (same : ∀ i, first i=second i) : e.eval first=e.eval second := by
  induction e with
  | input index => exact same index
  | constant bit => rfl
  | arithmetic op a b ihA ihB => simp only [Expression.eval,ihA,ihB]

/-- Evaluating the postorder node list computes the original ring expression. -/
theorem Expression.compile_correct {arity : ℕ} {R : Type} [Ring R] (e : Expression arity) :
    ∀ (start : ℕ) (values : ℕ → R), arity≤start →
    evaluate (e.compile start).nodes start values (e.compile start).output=
      e.eval (fun index => values index.val) := by
  induction e with
  | input index => intros; rfl
  | constant bit => intro start values enough; simp [Expression.compile,evaluate,Node.advance,Node.eval,Expression.eval]
  | arithmetic op a b ihA ihB =>
    intro start values enough
    let left := a.compile start
    let right := b.compile (start+left.nodes.length)
    let afterLeft := evaluate left.nodes start values
    have leftBound : left.output<start+left.nodes.length := a.output_lt start enough
    have leftEq : afterLeft left.output=a.eval (fun i => values i.val) := ihA start values enough
    have oldInputs : ∀ i : Fin arity, afterLeft i.val=values i.val := by
      intro i
      exact evaluate_before left.nodes start values i.val (i.isLt.trans_le enough)
    have rightEq : evaluate right.nodes (start+left.nodes.length) afterLeft right.output=
        b.eval (fun i => values i.val) :=
      (ihB (start+left.nodes.length) afterLeft (by omega)).trans (b.eval_congr oldInputs)
    have leftRead : evaluate right.nodes (start+left.nodes.length) afterLeft left.output=
        a.eval (fun i => values i.val) :=
      (evaluate_before right.nodes (start+left.nodes.length) afterLeft left.output leftBound).trans leftEq
    change evaluate (left.nodes++right.nodes++[.arithmetic op left.output right.output]) start values
      (start+left.nodes.length+right.nodes.length)=op.eval (a.eval _) (b.eval _)
    rw [evaluate_append,evaluate_append]
    simp only [List.length_append,evaluate,Node.advance,Node.eval,Nat.add_assoc,Function.update_self]
    exact congrArg₂ op.eval leftRead rightEq

/-- A fixed arithmetic expression has one fixed ordinary RAM implementation.
Its input slots contain binary digits, and its fresh output slots are zero.
The checked execution bound includes all pointer arithmetic and digit loops. -/
theorem Expression.program_exec {arity w base length : ℕ} (e : Expression arity)
    (data : Data) (values : ℕ → ZMod (2^length))
    (known : Represents base length arity values data) (positive : 0< length)
    (zero : ∀ slot, arity≤slot → slot< arity+(e.compile arity).nodes.length →
      ∀ i< length, data.2 (slotBase base length slot+i)=0)
    (fits : Fits w (resourceBound base length (arity+(e.compile arity).nodes.length))) :
    ∃ result cost,
      NaturalData.Exec w (program (e.compile arity).nodes arity) data result cost ∧
      cost≤(26*length^2+26*length+16)*(e.compile arity).nodes.length+1 ∧
      Represents base length (arity+(e.compile arity).nodes.length)
        (evaluate (e.compile arity).nodes arity values) result ∧
      (Binary.value result.2 (slotBase base length (e.compile arity).output) length : ZMod (2^length))=
        e.eval (fun index => values index.val) ∧
      ∀ address, (address< slotBase base length arity ∨
        slotBase base length (arity+(e.compile arity).nodes.length)≤address) → result.2 address=data.2 address := by
  obtain ⟨result,cost,run,bound,correct,frame⟩ := Circuit.program_exec (e.compile arity).nodes arity values data
    known (e.compile_valid arity (le_refl _)) positive (le_refl _) zero fits
  refine ⟨result,cost,run,bound,correct,?_,frame⟩
  exact (correct.value _ (e.output_lt arity (le_refl _))).trans (e.compile_correct arity values (le_refl _))

/-- Ring homomorphisms commute with the expression, including its signs. -/
theorem Expression.eval_map {arity : ℕ} {R S : Type} [Ring R] [Ring S]
    (e : Expression arity) (f : R →+* S) (inputs : Fin arity → R) :
    e.eval (fun i => f (inputs i))=f (e.eval inputs) := by
  induction e with
  | input index => rfl
  | constant bit => simp [Expression.eval]
  | arithmetic op a b ihA ihB =>
    cases op <;> simp [Expression.eval,Operation.eval,ihA,ihB]

end LeanTrominoes.Domino.WordRAM.Binary.Circuit
