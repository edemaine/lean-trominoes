import LeanTrominoes.IndexedSavitch
import Mathlib.Computability.Primrec.List

/-!
# Computability combinators for indexed search

The arithmetic search loops are used with an input-dependent predicate.  This
file records the first-order closure theorem needed by the compiled strip
decider: direct bounded existential search preserves primitive recursiveness
and is implemented by `Nat.rec`, not by constructing a list of all indices.
-/

namespace LeanTrominoes.FiniteState

theorem boundedAny_primrec {α : Type*} [Primcodable α]
    {predicate : α → Nat → Bool}
    (predicatePrimrec : Primrec₂ predicate) :
    Primrec₂ fun input bound => boundedAny (predicate input) bound := by
  let step : α → Nat × Bool → Bool :=
    fun input state => predicate input state.1 || state.2
  have stepPrimrec : Primrec₂ step := by
    exact Primrec.or.comp₂
      (predicatePrimrec.comp₂ Primrec₂.left
        (Primrec.fst.comp₂ Primrec₂.right))
      (Primrec.snd.comp₂ Primrec₂.right)
  exact (Primrec.nat_rec (Primrec.const false) stepPrimrec).of_eq
    (fun input bound => by
      induction bound with
      | zero => rfl
      | succ bound induction =>
          simp [boundedAny, step, induction])

theorem nestedBoundedAny_primrec {α : Type*} [Primcodable α]
    {predicate : α → Nat → Nat → Bool}
    (predicatePrimrec : Primrec fun
      input : (α × Nat) × Nat =>
        predicate input.1.1 input.1.2 input.2) :
    Primrec₂ fun input bound =>
      boundedAny (fun first =>
        boundedAny (predicate input first) bound) bound := by
  have inner : Primrec₂ fun (input : α × Nat) bound =>
      boundedAny (predicate input.1 input.2) bound := by
    apply boundedAny_primrec
    exact predicatePrimrec
  have outerPredicate : Primrec₂ fun (input : α × Nat) first =>
      boundedAny (predicate input.1 first) input.2 := by
    exact inner.comp₂
      (Primrec₂.pair.comp₂
        (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.left)
  have outer : Primrec₂ fun (input : α × Nat) bound =>
      boundedAny (fun first =>
        boundedAny (predicate input.1 first) input.2) bound :=
    boundedAny_primrec outerPredicate
  exact outer.comp₂
    (Primrec₂.pair.comp₂ Primrec₂.left Primrec₂.right)
    Primrec₂.right

end LeanTrominoes.FiniteState
