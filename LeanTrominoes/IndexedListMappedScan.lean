/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedListScan

/-! # Indexed scans through pointwise maps -/

namespace LeanTrominoes
namespace IndexedListScan

/-- Indexing a mapped list from `start` and scanning its values is the same
as scanning the zero-based source indices and adding `start` pointwise. -/
theorem map_zipIdx_from_flatMap
    {Value Position Output : Type}
    (values : List Value) (position : Value → Position)
    (start : Nat) (emit : Position × Nat → List Output) :
    ((values.map position).zipIdx start).flatMap emit =
      values.zipIdx.flatMap fun tagged =>
        emit (position tagged.1, start + tagged.2) := by
  rw [List.zipIdx_map, List.zipIdx_eq_map_add,
    List.flatMap_map, List.flatMap_map]
  rfl

/-- Apply `map_zipIdx_from_flatMap` independently across a natural-range
scan, without elaborating the body of the emitted blocks. -/
theorem range_flatMap_map_zipIdx_from_flatMap
    {Value Position Output : Type}
    (count : Nat) (values : List Value)
    (position : Nat → Value → Position)
    (start : Nat → Nat)
    (emit : Nat → Position × Nat → List Output) :
    (List.range count).flatMap (fun index =>
      ((values.map (position index)).zipIdx (start index)).flatMap
        (emit index)) =
      (List.range count).flatMap (fun index =>
        values.zipIdx.flatMap fun tagged =>
          emit index (position index tagged.1,
            start index + tagged.2)) := by
  apply List.flatMap_congr
  intro index indexMember
  exact map_zipIdx_from_flatMap values (position index)
    (start index) (emit index)

/-- A tagged prefix member remains at the same optional-lookup index after
an arbitrary suffix is appended. -/
theorem append_getElem?_of_mem_zipIdx
    {Value : Type} (head tail : List Value)
    (tagged : Value × Nat) (member : tagged ∈ head.zipIdx) :
    (head ++ tail)[tagged.2]? = some tagged.1 := by
  rw [List.getElem?_append_left (List.snd_lt_of_mem_zipIdx member)]
  exact (List.mem_zipIdx_iff_getElem?).mp member

end IndexedListScan
end LeanTrominoes
