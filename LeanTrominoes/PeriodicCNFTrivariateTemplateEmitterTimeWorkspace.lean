/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterTimeRange

/-! # Workspace-length bounds for the trivariate template emitter -/

namespace LeanTrominoes

namespace PeriodicCNF
namespace TrivariateTemplateEmitterMachine

open UnaryProgramTokens

theorem selectedCount_le_length {Data : Type} (selected : Data → Bool)
    (workspace : List (Workspace Data)) :
    selectedCount selected workspace ≤ workspace.length := by
  exact UnaryPolynomialPaddingMachine.selectedCount_le_length
    (dataSelected selected) workspace

theorem emittedOutput_eq {Data : Type}
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (workspace : List (Workspace Data)) :
    emittedOutput firstSelected secondSelected positionSelected recipes ending
        workspace =
      workspace ++
        (emittedOf firstSelected secondSelected positionSelected recipes
          workspace ++ ending).map Sum.inr := by
  unfold emittedOutput TrivariateTemplateEmitter.appendedOutput emittedOf
    firstCountOf secondCountOf positionCountOf selectedCount dataSelected
  congr 3

theorem emittedOutput_length {Data : Type}
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (workspace : List (Workspace Data)) :
    (emittedOutput firstSelected secondSelected positionSelected recipes ending
      workspace).length =
      workspace.length +
        (emittedOf firstSelected secondSelected positionSelected recipes
          workspace).length + ending.length := by
  rw [emittedOutput_eq]
  simp [Nat.add_assoc]

theorem emittedRange_length_le_workspace {Data : Type}
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (workspace : List (Workspace Data)) :
    (emittedOf firstSelected secondSelected positionSelected recipes
      workspace).length ≤
      3 * templateWeight recipes * (workspace.length + 1) ^ 2 := by
  let first := firstCountOf firstSelected workspace
  let second := secondCountOf secondSelected workspace
  let count := positionCountOf positionSelected workspace
  have firstLe : first ≤ workspace.length :=
    selectedCount_le_length firstSelected workspace
  have secondLe : second ≤ workspace.length :=
    selectedCount_le_length secondSelected workspace
  have countLe : count ≤ workspace.length :=
    selectedCount_le_length positionSelected workspace
  have rangeBound := positionRangeTokens_length_le recipes first second 0 count
  have productLe : count * (first + second + count + 1) ≤
      3 * (workspace.length + 1) ^ 2 := by
    nlinarith
  have weightedLe := Nat.mul_le_mul_left (templateWeight recipes) productLe
  dsimp only [first, second, count] at rangeBound ⊢
  unfold emittedOf
  calc
    _ ≤ templateWeight recipes *
          (3 * (workspace.length + 1) ^ 2) :=
      rangeBound.trans (by simpa [Nat.mul_assoc] using weightedLe)
    _ = _ := by ring

theorem positionRangeTime_le_workspace {Data : Type}
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (workspace : List (Workspace Data)) :
    positionRangeTime recipes
        (firstCountOf firstSelected workspace)
        (secondCountOf secondSelected workspace) 0
        (positionCountOf positionSelected workspace) ≤
      3 * (7 * recipes.length + 2) * (workspace.length + 1) ^ 2 := by
  let first := firstCountOf firstSelected workspace
  let second := secondCountOf secondSelected workspace
  let count := positionCountOf positionSelected workspace
  have firstLe : first ≤ workspace.length :=
    selectedCount_le_length firstSelected workspace
  have secondLe : second ≤ workspace.length :=
    selectedCount_le_length secondSelected workspace
  have countLe : count ≤ workspace.length :=
    selectedCount_le_length positionSelected workspace
  have rangeBound := positionRangeTime_le recipes first second 0 count
  have productLe : (count + 1) * (first + second + count + 1) ≤
      3 * (workspace.length + 1) ^ 2 := by
    nlinarith
  have weightedLe :=
    Nat.mul_le_mul_left (7 * recipes.length + 2) productLe
  dsimp only [first, second, count] at rangeBound ⊢
  calc
    _ ≤ (7 * recipes.length + 2) *
          (3 * (workspace.length + 1) ^ 2) :=
      rangeBound.trans (by simpa [Nat.mul_assoc] using weightedLe)
    _ = _ := by ring

end TrivariateTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
