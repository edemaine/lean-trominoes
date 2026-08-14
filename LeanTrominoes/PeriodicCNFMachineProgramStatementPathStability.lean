/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineProgramStatementPaths
import LeanTrominoes.PeriodicCNFMachineStatementSize

/-!
# Width stabilization of program-valued statement paths

The only width-dependent choice in symbolic statement execution is whether a
still-unknown source cell exists.  The initial discard plus the remaining
observation depth bounds every such test.  Consequently identity-transform
execution depends only on the represented width capped at the fixed
`statementObservationDepth + 1` cutoff.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace BoundedMachineProgram

open BoundedMachineAtom

variable {tm : FinTM2}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

@[simp]
theorem push_discard {Symbol : Type} (symbol : Symbol)
    (transform : StackTransform Symbol) :
    (transform.push symbol).discard = transform.discard := by
  rfl

theorem pop_discard_le {Symbol : Type} (transform : StackTransform Symbol) :
    transform.pop.discard ≤ transform.discard + 1 := by
  cases transform with
  | mk added discard =>
      cases added <;> simp [StackTransform.pop]

/-- If every initial discard plus the remaining observation depth fits at two
widths, symbolic execution produces exactly the same program-valued paths at
those widths. -/
theorem statementProgramPaths_eq_of_depth_lt
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ)
    (transforms : ∀ stack, StackTransform (tm.Γ stack))
    (firstSpace secondSpace : Nat)
    (firstFits : ∀ stack,
      (transforms stack).discard + statementObservationDepth statement <
        firstSpace)
    (secondFits : ∀ stack,
      (transforms stack).discard + statementObservationDepth statement <
        secondSpace) :
    statementProgramPaths (tm := tm) (space := firstSpace)
        statement control transforms =
      statementProgramPaths (tm := tm) (space := secondSpace)
        statement control transforms := by
  classical
  induction statement generalizing control transforms with
  | push stack write next induction =>
      apply induction
      · intro candidate
        by_cases same : candidate = stack
        · subst candidate
          simpa [Function.update, statementObservationDepth] using
            firstFits stack
        · simpa [Function.update, same, statementObservationDepth] using
            firstFits candidate
      · intro candidate
        by_cases same : candidate = stack
        · subst candidate
          simpa [Function.update, statementObservationDepth] using
            secondFits stack
        · simpa [Function.update, same, statementObservationDepth] using
            secondFits candidate
  | peek stack read next induction =>
      simp only [statementProgramPaths]
      cases addedEq : (transforms stack).added with
      | cons symbol added =>
          apply induction
          · intro candidate
            have bound := firstFits candidate
            simp only [statementObservationDepth] at bound
            omega
          · intro candidate
            have bound := secondFits candidate
            simp only [statementObservationDepth] at bound
            omega
      | nil =>
          have sourceFirst : (transforms stack).discard < firstSpace := by
            have bound := firstFits stack
            simp only [statementObservationDepth] at bound
            omega
          have sourceSecond : (transforms stack).discard < secondSpace := by
            have bound := secondFits stack
            simp only [statementObservationDepth] at bound
            omega
          simp only [sourceFirst, sourceSecond, if_pos]
          apply List.flatMap_congr
          intro observed _
          rw [induction]
          · intro candidate
            have bound := firstFits candidate
            simp only [statementObservationDepth] at bound
            omega
          · intro candidate
            have bound := secondFits candidate
            simp only [statementObservationDepth] at bound
            omega
  | pop stack read next induction =>
      let popped := Function.update transforms stack (transforms stack).pop
      have poppedFirst : ∀ candidate,
          (popped candidate).discard + statementObservationDepth next <
            firstSpace := by
        intro candidate
        by_cases same : candidate = stack
        · subst candidate
          have oldBound := firstFits stack
          have discardBound := pop_discard_le (transforms stack)
          simp only [statementObservationDepth] at oldBound
          simp only [popped, Function.update_self]
          omega
        · have oldBound := firstFits candidate
          simp only [statementObservationDepth] at oldBound
          simp only [popped, Function.update_of_ne same]
          omega
      have poppedSecond : ∀ candidate,
          (popped candidate).discard + statementObservationDepth next <
            secondSpace := by
        intro candidate
        by_cases same : candidate = stack
        · subst candidate
          have oldBound := secondFits stack
          have discardBound := pop_discard_le (transforms stack)
          simp only [statementObservationDepth] at oldBound
          simp only [popped, Function.update_self]
          omega
        · have oldBound := secondFits candidate
          simp only [statementObservationDepth] at oldBound
          simp only [popped, Function.update_of_ne same]
          omega
      simp only [statementProgramPaths]
      cases addedEq : (transforms stack).added with
      | cons symbol added =>
          exact induction _ popped poppedFirst poppedSecond
      | nil =>
          have sourceFirst : (transforms stack).discard < firstSpace := by
            have bound := firstFits stack
            simp only [statementObservationDepth] at bound
            omega
          have sourceSecond : (transforms stack).discard < secondSpace := by
            have bound := secondFits stack
            simp only [statementObservationDepth] at bound
            omega
          simp only [sourceFirst, sourceSecond, if_pos]
          apply List.flatMap_congr
          intro observed _
          rw [induction _ popped poppedFirst poppedSecond]
  | load update next induction =>
      apply induction
      · intro candidate
        simpa [statementObservationDepth] using firstFits candidate
      · intro candidate
        simpa [statementObservationDepth] using secondFits candidate
  | branch test yes no yesInduction noInduction =>
      simp only [statementProgramPaths]
      split
      · apply yesInduction
        · intro candidate
          have bound := firstFits candidate
          simp only [statementObservationDepth] at bound
          exact lt_of_le_of_lt (Nat.add_le_add_left
            (Nat.le_max_left _ _) _) bound
        · intro candidate
          have bound := secondFits candidate
          simp only [statementObservationDepth] at bound
          exact lt_of_le_of_lt (Nat.add_le_add_left
            (Nat.le_max_left _ _) _) bound
      · apply noInduction
        · intro candidate
          have bound := firstFits candidate
          simp only [statementObservationDepth] at bound
          exact lt_of_le_of_lt (Nat.add_le_add_left
            (Nat.le_max_right _ _) _) bound
        · intro candidate
          have bound := secondFits candidate
          simp only [statementObservationDepth] at bound
          exact lt_of_le_of_lt (Nat.add_le_add_left
            (Nat.le_max_right _ _) _) bound
  | goto target => rfl
  | halt => rfl

def statementWidthCutoff
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) : Nat :=
  statementObservationDepth statement + 1

/-- Starting from identity transforms, the symbolic path list depends only on
the width capped at the statement's fixed observation cutoff. -/
theorem statementProgramPaths_eq_capped
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ) (space : Nat) :
    statementProgramPaths (tm := tm) (space := space) statement control
        BoundedMachineAtom.identityStackTransforms =
      statementProgramPaths (tm := tm)
        (space := min space (statementWidthCutoff statement))
        statement control BoundedMachineAtom.identityStackTransforms := by
  by_cases reached : statementWidthCutoff statement ≤ space
  · rw [Nat.min_eq_right reached]
    have depthFits : statementObservationDepth statement < space := by
      unfold statementWidthCutoff at reached
      omega
    apply statementProgramPaths_eq_of_depth_lt
    · intro stack
      simpa [BoundedMachineAtom.identityStackTransforms,
        StackTransform.identity] using depthFits
    · intro stack
      simp [BoundedMachineAtom.identityStackTransforms,
        StackTransform.identity, statementWidthCutoff]
  · have below : space ≤ statementWidthCutoff statement :=
      Nat.le_of_not_ge reached
    rw [Nat.min_eq_left below]

end BoundedMachineProgram
end PeriodicCNF
end LeanTrominoes
