/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIndexedTemplateEmitterSemantics
import LeanTrominoes.PeriodicCNFAffineTemplateEmitterTime

/-!
# Quantitative bounds for indexed template emission

For a fixed finite data alphabet and data-indexed recipe family, sum the
per-item recipe sizes and output weights into fixed coefficients.  These
coefficients bound the emitted word and verified scan runtime quadratically in
the input length.
-/

namespace LeanTrominoes

open BigOperators

namespace PeriodicCNF
namespace IndexedTemplateEmitterMachine

open AffineTemplateEmitterMachine
open IndexedTemplateEmitter

/-- Sum of all recipe-list lengths in a fixed finite indexed family. -/
noncomputable def familyRecipeCount {Data : Type} [Fintype Data]
    (family : Family Data) : Nat :=
  ∑ item : Data, (recipesFor family item).length

/-- Sum of all affine output coefficients in a fixed finite indexed family. -/
noncomputable def familyWeight {Data : Type} [Fintype Data]
    (family : Family Data) : Nat :=
  ∑ item : Data, AffineTemplateEmitterMachine.templateWeight
    (recipesFor family item)

theorem recipesFor_length_le_familyRecipeCount {Data : Type} [Fintype Data]
    (family : Family Data) (item : Data) :
    (recipesFor family item).length ≤ familyRecipeCount family := by
  classical
  exact Finset.single_le_sum
    (fun other _ => Nat.zero_le (recipesFor family other).length)
    (Finset.mem_univ item)

theorem templateWeight_le_familyWeight {Data : Type} [Fintype Data]
    (family : Family Data) (item : Data) :
    AffineTemplateEmitterMachine.templateWeight (recipesFor family item) ≤
      familyWeight family := by
  classical
  exact Finset.single_le_sum
    (fun other _ => Nat.zero_le
      (AffineTemplateEmitterMachine.templateWeight
        (recipesFor family other)))
    (Finset.mem_univ item)

theorem selectedCount_le_length {Data : Type} (family : Family Data)
    (data : List Data) :
    IndexedTemplateEmitter.selectedCount family data ≤ data.length := by
  induction data with
  | nil => simp
  | cons item data induction =>
      cases value : family item with
      | none =>
          rw [IndexedTemplateEmitter.selectedCount_cons_none
            family item data value]
          exact induction.trans (by simp)
      | some recipes =>
          rw [IndexedTemplateEmitter.selectedCount_cons_some
            family item data recipes value]
          simpa using Nat.add_le_add_right induction 1

theorem positionTokens_length_le_familyWeight {Data : Type} [Fintype Data]
    (family : Family Data) (item : Data) (position : Nat) :
    (positionTokens (recipesFor family item) position).length ≤
      familyWeight family * (position + 1) := by
  have baseBound := AffineTemplateEmitterMachine.positionTokens_length_le
    (recipesFor family item) position
  have weight := templateWeight_le_familyWeight family item
  exact baseBound.trans (Nat.mul_le_mul_right (position + 1) weight)

/-- The semantic token word emitted from an arbitrary starting position has a
uniform quadratic-scale bound depending only on the fixed finite family. -/
theorem emittedAux_length_le {Data : Type} [Fintype Data]
    (family : Family Data) (position : Nat) (data : List Data) :
    (emittedAux family position data).length ≤
      familyWeight family * data.length *
        (position + data.length + 1) := by
  induction data generalizing position with
  | nil => simp [emittedAux]
  | cons item data induction =>
      cases value : family item with
      | none =>
          rw [emittedAux_cons_none family position item data value]
          have rest := induction position
          have countLe : data.length ≤ data.length + 1 := by omega
          have sideLe : position + data.length + 1 ≤
              position + (data.length + 1) + 1 := by omega
          have productLe : data.length * (position + data.length + 1) ≤
              (data.length + 1) *
                (position + (data.length + 1) + 1) :=
            Nat.mul_le_mul countLe sideLe
          simpa only [List.length_cons] using rest.trans (by
            simpa only [Nat.mul_assoc] using
              Nat.mul_le_mul_left (familyWeight family) productLe)
      | some recipes =>
          rw [emittedAux_cons_some family position item data recipes value,
            List.length_append]
          have currentRaw := positionTokens_length_le_familyWeight
            family item position
          have recipesEq : recipesFor family item = recipes := by
            simp [recipesFor, value]
          rw [recipesEq] at currentRaw
          have sideLe : position + 1 ≤
              position + data.length + 2 := by omega
          have current := currentRaw.trans
            (Nat.mul_le_mul_left (familyWeight family) sideLe)
          have rest := induction (position + 1)
          have rest' : (emittedAux family (position + 1) data).length ≤
              familyWeight family * data.length *
                (position + data.length + 2) := by
            have sideEq : (position + 1) + data.length + 1 =
                position + data.length + 2 := by omega
            rw [sideEq] at rest
            exact rest
          calc
            (positionTokens recipes position).length +
                  (emittedAux family (position + 1) data).length ≤
                familyWeight family * (position + data.length + 2) +
                  familyWeight family * data.length *
                    (position + data.length + 2) :=
              Nat.add_le_add current rest'
            _ = familyWeight family * (data.length + 1) *
                  (position + (data.length + 1) + 1) := by ring

theorem emitted_length_le {Data : Type} [Fintype Data]
    (family : Family Data) (data : List Data) :
    (IndexedTemplateEmitter.emitted family data).length ≤
      familyWeight family * data.length * (data.length + 1) := by
  simpa [IndexedTemplateEmitter.emitted] using
    emittedAux_length_le family 0 data

theorem recipeTime_le (recipe : Recipe) (position : Nat) :
    IndexedTemplateEmitterMachine.recipeTime position recipe ≤
      3 * (position + 1) := by
  cases recipe <;>
    simp [IndexedTemplateEmitterMachine.recipeTime] <;> omega

theorem templateTime_le (recipes : List Recipe) (position : Nat) :
    IndexedTemplateEmitterMachine.templateTime recipes position ≤
      3 * recipes.length * (position + 1) := by
  induction recipes with
  | nil => simp [IndexedTemplateEmitterMachine.templateTime]
  | cons recipe recipes induction =>
      simp only [IndexedTemplateEmitterMachine.templateTime, List.map_cons,
        List.sum_cons, List.length_cons]
      have current := recipeTime_le recipe position
      calc
        IndexedTemplateEmitterMachine.recipeTime position recipe +
              (recipes.map
                (IndexedTemplateEmitterMachine.recipeTime position)).sum ≤
            3 * (position + 1) +
              3 * recipes.length * (position + 1) :=
          Nat.add_le_add current induction
        _ = 3 * (recipes.length + 1) * (position + 1) := by ring

theorem templateTime_recipesFor_le {Data : Type} [Fintype Data]
    (family : Family Data) (item : Data) (position : Nat) :
    IndexedTemplateEmitterMachine.templateTime
        (recipesFor family item) position ≤
      3 * familyRecipeCount family * (position + 1) := by
  have baseBound := templateTime_le (recipesFor family item) position
  have count := recipesFor_length_le_familyRecipeCount family item
  have scaled := Nat.mul_le_mul_left 3 count
  exact baseBound.trans (Nat.mul_le_mul_right (position + 1) scaled)

/-- The exact verified scan time is uniformly quadratic in the input length. -/
theorem scanTime_le {Data : Type} [Fintype Data]
    (family : Family Data) (position : Nat) (data : List Data) :
    scanTime family position data ≤
      (3 * familyRecipeCount family + 2) * data.length *
        (position + data.length + 1) + 1 := by
  induction data generalizing position with
  | nil => simp [scanTime]
  | cons item data induction =>
      let coefficient := 3 * familyRecipeCount family + 2
      have coefficientTwo : 2 ≤ coefficient := by
        simp [coefficient]
      cases value : family item with
      | none =>
          have rest := induction position
          change scanTime family position data ≤
            coefficient * data.length *
              (position + data.length + 1) + 1 at rest
          have sideLe : position + data.length + 1 ≤
              position + data.length + 2 := by omega
          have productLift := Nat.mul_le_mul_left data.length sideLe
          have weightedLift := Nat.mul_le_mul_left coefficient productLift
          have restLift : scanTime family position data ≤
              coefficient * data.length *
                (position + data.length + 2) + 1 :=
            rest.trans (by
              simpa only [Nat.mul_assoc] using
                Nat.add_le_add_right weightedLift 1)
          have head : 2 ≤ coefficient *
              (position + data.length + 2) := by
            have positive : 1 ≤ position + data.length + 2 := by omega
            exact coefficientTwo.trans
              (Nat.le_mul_of_pos_right coefficient (by omega))
          simp only [scanTime, value, Option.isSome_none, Bool.false_eq_true,
            if_false, List.length_cons]
          calc
            2 + scanTime family position data ≤
                2 + (coefficient * data.length *
                  (position + data.length + 2) + 1) :=
              Nat.add_le_add_left restLift 2
            _ ≤ coefficient * (position + data.length + 2) +
                  coefficient * data.length *
                    (position + data.length + 2) + 1 := by omega
            _ = coefficient * (data.length + 1) *
                  (position + (data.length + 1) + 1) + 1 := by ring
      | some recipes =>
          have currentRaw := templateTime_recipesFor_le family item position
          have recipesEq : recipesFor family item = recipes := by
            simp [recipesFor, value]
          rw [recipesEq] at currentRaw
          have positionLe : position + 1 ≤
              position + data.length + 2 := by omega
          have current := currentRaw.trans
            (Nat.mul_le_mul_left (3 * familyRecipeCount family) positionLe)
          have rest := induction (position + 1)
          have rest' : scanTime family (position + 1) data ≤
              coefficient * data.length *
                (position + data.length + 2) + 1 := by
            have sideEq : (position + 1) + data.length + 1 =
                position + data.length + 2 := by omega
            rw [sideEq] at rest
            simpa only [coefficient] using rest
          have head : 2 + templateTime recipes position ≤
              coefficient * (position + data.length + 2) := by
            calc
              2 + templateTime recipes position ≤
                  2 + 3 * familyRecipeCount family *
                    (position + data.length + 2) :=
                Nat.add_le_add_left current 2
              _ ≤ 2 * (position + data.length + 2) +
                    3 * familyRecipeCount family *
                      (position + data.length + 2) := by
                omega
              _ = coefficient * (position + data.length + 2) := by
                simp [coefficient]
                ring
          simp only [scanTime, value, Option.isSome_some, if_true,
            List.length_cons]
          calc
            2 + templateTime recipes position +
                  scanTime family (position + 1) data ≤
                coefficient * (position + data.length + 2) +
                  (coefficient * data.length *
                    (position + data.length + 2) + 1) :=
              Nat.add_le_add head rest'
            _ = coefficient * (data.length + 1) *
                  (position + (data.length + 1) + 1) + 1 := by ring

end IndexedTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
