/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMCircuitProgram

/-! # Compiling integer arithmetic expressions to fixed binary circuits -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Circuit

theorem valid_append (first second : List Node) (start : ℕ) :
    Valid (first++second) start ↔ Valid first start ∧ Valid second (start+first.length) := by
  induction first generalizing start with
  | nil => simp [Valid]
  | cons node rest ih =>
    simp only [List.cons_append,Valid,ih,List.length_cons]
    simp [and_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem evaluate_append {R : Type} [Ring R] (first second : List Node) (start : ℕ) (values : ℕ → R) :
    evaluate (first++second) start values=
      evaluate second (start+first.length) (evaluate first start values) := by
  induction first generalizing start values with
  | nil => simp [evaluate]
  | cons node rest ih =>
    simpa only [List.cons_append,evaluate,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      ih (start+1) (node.advance start values)

theorem evaluate_before {R : Type} [Ring R] (nodes : List Node) (start : ℕ) (values : ℕ → R)
    (i : ℕ) (earlier : i< start) : evaluate nodes start values i=values i := by
  induction nodes generalizing start values with
  | nil => rfl
  | cons node rest ih =>
    change evaluate rest (start+1) (node.advance start values) i=values i
    rw [ih (start+1) (node.advance start values) (by omega)]
    exact Function.update_of_ne (by omega : i≠start) _ _

inductive Expression (arity : ℕ)
  | input (index : Fin arity)
  | constant (bit : Bool)
  | arithmetic (op : Operation) (first second : Expression arity)

def Expression.eval {arity : ℕ} {R : Type} [Ring R] (inputs : Fin arity → R) : Expression arity → R
  | .input index => inputs index
  | .constant bit => (bitValue bit : R)
  | .arithmetic op first second => op.eval (first.eval inputs) (second.eval inputs)

structure Compilation where
  nodes : List Node
  output : ℕ

def Expression.compile {arity : ℕ} : Expression arity → ℕ → Compilation
  | .input index, _ => ⟨[],index.val⟩
  | .constant bit, start => ⟨[.constant bit],start⟩
  | .arithmetic op first second, start =>
    let left := first.compile start
    let right := second.compile (start+left.nodes.length)
    ⟨left.nodes++right.nodes++[.arithmetic op left.output right.output],
      start+left.nodes.length+right.nodes.length⟩

theorem Expression.output_lt {arity : ℕ} (e : Expression arity) (start : ℕ) (enough : arity≤start) :
    (e.compile start).output<start+(e.compile start).nodes.length := by
  cases e with
  | input index => simpa only [Expression.compile,List.length_nil,Nat.add_zero] using index.isLt.trans_le enough
  | constant bit => simp [Expression.compile]
  | arithmetic op first second => simp [Expression.compile,List.length_append]; omega

/-- The postorder compiler never refers to an unwritten circuit value. -/
theorem Expression.compile_valid {arity : ℕ} (e : Expression arity) :
    ∀ start, arity≤start → Valid (e.compile start).nodes start := by
  induction e with
  | input index => intros; trivial
  | constant bit => intro start enough; simp [Expression.compile,Valid,Node.Valid]
  | arithmetic op a b ihA ihB =>
    intro start enough
    let left := a.compile start
    let right := b.compile (start+left.nodes.length)
    change Valid (left.nodes++right.nodes++[.arithmetic op left.output right.output]) start
    rw [valid_append,valid_append]
    refine ⟨⟨ihA start enough,ihB (start+left.nodes.length) (by omega)⟩,?_⟩
    have leftBound := a.output_lt start enough
    have rightBound := b.output_lt (start+left.nodes.length) (by omega)
    change left.output<start+left.nodes.length at leftBound
    change right.output<(start+left.nodes.length)+right.nodes.length at rightBound
    simp only [Valid,Node.Valid,List.length_append]
    exact ⟨⟨by omega,by omega⟩,trivial⟩

end LeanTrominoes.Domino.WordRAM.Binary.Circuit
