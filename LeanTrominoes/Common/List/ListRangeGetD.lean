/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Range

/-! # Enumerating total list lookups -/

namespace List

/-- Total lookups over exactly the valid natural indices enumerate the
original list. -/
theorem map_range_getD (values : List α) (default : α) :
    (List.range values.length).map
        (fun index => values.getD index default) =
      values := by
  apply List.ext_getElem
  · simp
  · intro index leftBound rightBound
    have indexLt : index < values.length := by
      simpa using leftBound
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ indexLt]

end List
