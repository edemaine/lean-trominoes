/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2EndDelimitedBlockMapConfigurations

/-! # Stack transformation used while preparing an inner block -/

noncomputable section

namespace LeanTrominoes
namespace TM2EndDelimitedBlockMap

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

/-- Pop source symbols in order and push their decoded forms onto the inner
input stack. -/
def transferredContents {Source : Type} (inner : FinTM2)
    (decode : Source → inner.Γ inner.k₀) :
    List Source → (∀ stack, List (inner.Γ stack)) →
      (∀ stack, List (inner.Γ stack))
  | [], innerContents => innerContents
  | symbol :: remaining, innerContents =>
      transferredContents inner decode remaining
        (@Function.update _ _ inner.kDecidableEq innerContents inner.k₀
          (decode symbol :: innerContents inner.k₀))

theorem transferredContents_input {Source : Type} (inner : FinTM2)
    (decode : Source → inner.Γ inner.k₀) (symbols : List Source)
    (innerContents : ∀ stack, List (inner.Γ stack)) :
    (transferredContents inner decode symbols innerContents) inner.k₀ =
      symbols.reverse.map decode ++ innerContents inner.k₀ := by
  induction symbols generalizing innerContents with
  | nil => simp [transferredContents]
  | cons symbol remaining induction =>
      rw [transferredContents, induction]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem transferredContents_other {Source : Type} (inner : FinTM2)
    (decode : Source → inner.Γ inner.k₀) (symbols : List Source)
    (innerContents : ∀ stack, List (inner.Γ stack))
    (stack : inner.K) (other : stack ≠ inner.k₀) :
    (transferredContents inner decode symbols innerContents) stack =
      innerContents stack := by
  induction symbols generalizing innerContents with
  | nil => rfl
  | cons symbol remaining induction =>
      rw [transferredContents, induction]
      exact Function.update_of_ne other _ _

theorem transferredContents_reverse_empty_eq_initList
    {Source : Type} (inner : FinTM2)
    (decode : Source → inner.Γ inner.k₀) (block : List Source) :
    transferredContents inner decode block.reverse (emptyInnerStacks inner) =
      (initList inner (block.map decode)).stk := by
  funext stack
  by_cases equal : stack = inner.k₀
  · subst stack
    rw [transferredContents_input]
    simp [emptyInnerStacks, initList]
  · rw [transferredContents_other inner decode block.reverse
      (emptyInnerStacks inner) stack equal]
    simp [emptyInnerStacks, initList, equal]

theorem transferredCfg_reverse_empty_eq_initList
    {Source : Type} (inner : FinTM2)
    (decode : Source → inner.Γ inner.k₀) (block : List Source) :
    (⟨some inner.main, inner.initialState,
      transferredContents inner decode block.reverse
        (emptyInnerStacks inner)⟩ : inner.Cfg) =
      initList inner (block.map decode) := by
  rw [transferredContents_reverse_empty_eq_initList inner decode block]
  rfl

end TM2EndDelimitedBlockMap
end LeanTrominoes
