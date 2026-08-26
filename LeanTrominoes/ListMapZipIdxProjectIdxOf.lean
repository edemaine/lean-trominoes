/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedListScan
import LeanTrominoes.ListMapZipIdxCongr

/-! # Replacing stable indices by duplicate-free projected ranks -/

namespace List

/-- When a projection has no duplicates, the stable index of each source
value is the `idxOf` rank of its projection. -/
theorem map_zipIdx_project_eq_map_idxOf
    {Value Key Output : Type} [DecidableEq Key]
    (values : List Value) (project : Value → Key)
    (nodup : (values.map project).Nodup)
    (indexed : Nat → Key → Output) :
    values.zipIdx.map (fun tagged =>
        indexed tagged.2 (project tagged.1)) =
      values.map (fun value =>
        indexed ((values.map project).idxOf (project value))
          (project value)) := by
  apply List.map_zipIdx_eq_map_of_mem
  intro tagged taggedMember
  apply congrArg (fun index => indexed index (project tagged.1))
  have projectedMember :
      (project tagged.1, tagged.2) ∈ (values.map project).zipIdx := by
    rw [List.zipIdx_map]
    exact List.mem_map.mpr ⟨tagged, taggedMember, rfl⟩
  exact
    (LeanTrominoes.IndexedListScan.idxOf_fst_eq_snd_of_mem_zipIdx
      (values.map project) nodup (project tagged.1, tagged.2)
      projectedMember).symm

/-- Project the source list on the right as well, so a subsequent equality
of projected lists can be transported without rewrite search. -/
theorem map_zipIdx_project_eq_projected_map_idxOf
    {Value Key Output : Type} [DecidableEq Key]
    (values : List Value) (project : Value → Key)
    (nodup : (values.map project).Nodup)
    (indexed : Nat → Key → Output) :
    values.zipIdx.map (fun tagged =>
        indexed tagged.2 (project tagged.1)) =
      (values.map project).map (fun key =>
        indexed ((values.map project).idxOf key) key) := by
  rw [map_zipIdx_project_eq_map_idxOf values project nodup indexed,
    List.map_map]
  rfl

/-- Mapping values together with their `idxOf` ranks respects equality of
the entire value list. -/
theorem map_idxOf_congr
    {Key Output : Type} [DecidableEq Key]
    (first second : List Key) (equal : first = second)
    (indexed : Nat → Key → Output) :
    first.map (fun key => indexed (first.idxOf key) key) =
      second.map (fun key => indexed (second.idxOf key) key) := by
  subst second
  rfl

end List
