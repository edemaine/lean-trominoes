/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Basic

/-! # Lookup of mapped prefix values at an appended-list index -/

namespace LeanTrominoes
namespace IndexedListScan

/-- An element already present in a value prefix selects its mapped output
from the corresponding output prefix, independently of both suffixes. -/
theorem map_append_getElem?_idxOf_append_of_mem
    {Value Output : Type} [BEq Value] [LawfulBEq Value]
    (headValues suffixValues : List Value)
    (output : Value → Output)
    (suffixOutputs : List Output)
    (value : Value)
    (valueMember : value ∈ headValues) :
    (headValues.map output ++ suffixOutputs)[
        (headValues ++ suffixValues).idxOf value]? =
      some (output value) := by
  rw [List.idxOf_append_of_mem valueMember]
  have mappedIndexLt :
      headValues.idxOf value < (headValues.map output).length := by
    simpa only [List.length_map] using
      (List.idxOf_lt_length_iff.mpr valueMember)
  rw [List.getElem?_append_left mappedIndexLt]
  rw [List.getElem?_map, List.getElem?_idxOf valueMember]
  simp only [Option.map_some]

end IndexedListScan
end LeanTrominoes
