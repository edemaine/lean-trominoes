/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFlatMapUnique
import Mathlib.Data.List.Nodup

/-! # Diagonal flat maps selected by duplicate-free keys -/

namespace List

/-- If keys are duplicate-free and a pair function vanishes on unequal keys,
its row-major square flat map reduces to the diagonal. -/
theorem keyedProduct_flatMap_eq_diagonal
    {Index Key Output : Type*}
    (indices : List Index) (key : Index → Key)
    (function : Index × Index → List Output)
    (keysNodup : (indices.map key).Nodup)
    (offDiagonal :
      ∀ first ∈ indices, ∀ second ∈ indices,
        key first ≠ key second → function (first, second) = []) :
    (indices ×ˢ indices).flatMap function =
      indices.flatMap fun index => function (index, index) := by
  change
    (indices.flatMap fun first =>
      indices.map fun second => (first, second)).flatMap function = _
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro first firstMember
  rw [List.flatMap_map]
  rw [List.flatMap_eq_selected_of_unique indices
    (fun second => function (first, second)) first
    (keysNodup.of_map key) firstMember]
  intro second secondMember secondNe
  apply offDiagonal first firstMember second secondMember
  intro keyEq
  exact secondNe
    (List.inj_on_of_nodup_map
      keysNodup firstMember secondMember keyEq).symm

end List
