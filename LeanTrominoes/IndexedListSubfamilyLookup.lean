/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedListMappedScan

/-! # Optional lookup of an indexed middle subfamily -/

namespace LeanTrominoes
namespace IndexedListScan

/-- A member indexed from the length of a preceding prefix retains that
index when the prefix and an arbitrary suffix surround its subfamily. -/
theorem append_middle_getElem?_of_mem_zipIdx
    {Value : Type}
    (head middle tail : List Value)
    (tagged : Value × Nat)
    (member : tagged ∈ middle.zipIdx head.length) :
    (head ++ middle ++ tail)[tagged.2]? = some tagged.1 := by
  have headMiddleMember :
      tagged ∈ (head ++ middle).zipIdx := by
    rw [List.zipIdx_append]
    simp only [Nat.zero_add]
    exact List.mem_append_right _ member
  exact append_getElem?_of_mem_zipIdx
    (head ++ middle) tail tagged headMiddleMember

/-- The same middle-subfamily lookup transported across an explicit whole
list decomposition. -/
theorem getElem?_of_eq_append_middle_of_mem_zipIdx
    {Value : Type}
    (whole head middle tail : List Value)
    (wholeEq : whole = head ++ middle ++ tail)
    (tagged : Value × Nat)
    (member : tagged ∈ middle.zipIdx head.length) :
    whole[tagged.2]? = some tagged.1 := by
  rw [wholeEq]
  exact append_middle_getElem?_of_mem_zipIdx
    head middle tail tagged member

end IndexedListScan
end LeanTrominoes
