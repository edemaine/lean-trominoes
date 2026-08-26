/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Basic

/-! # Recovering a source item at the first mapped occurrence -/

namespace LeanTrominoes
namespace IndexedListScan

/-- If a value occurs in a pointwise map, looking up the source list at the
value's first mapped index returns a source item that maps to that value. -/
theorem exists_getElem?_idxOf_map
    {Source Target : Type} [BEq Target] [LawfulBEq Target]
    (items : List Source) (output : Source → Target)
    (value : Target) (valueMember : value ∈ items.map output) :
    ∃ item,
      items[(items.map output).idxOf value]? = some item ∧
        output item = value ∧ item ∈ items := by
  have mappedLookup := List.getElem?_idxOf valueMember
  rw [List.getElem?_map] at mappedLookup
  generalize itemLookup :
      items[(items.map output).idxOf value]? = itemOption
        at mappedLookup
  cases itemOption with
  | none => simp at mappedLookup
  | some item =>
      simp only [Option.map_some, Option.some.injEq] at mappedLookup
      exact ⟨item, rfl, mappedLookup,
        List.mem_of_getElem? itemLookup⟩

end IndexedListScan
end LeanTrominoes
