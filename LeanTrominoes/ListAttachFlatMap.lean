/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Basic

/-! # Reindexing flat maps over attached lists -/

namespace List

theorem flatMap_eq_attach_flatMap
    {α β : Type*} (values : List α)
    (function : α → List β)
    (attachedFunction : {value // value ∈ values} → List β)
    (equal : ∀ value, function value.1 = attachedFunction value) :
    values.flatMap function = values.attach.flatMap attachedFunction := by
  conv_lhs =>
    rw [← List.attach_map_subtype_val values]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro value valueMember
  exact equal value

end List
