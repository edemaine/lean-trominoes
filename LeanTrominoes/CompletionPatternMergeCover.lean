/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionPatternResidual
import LeanTrominoes.TrominoFiniteSortedCover
import LeanTrominoes.CompletionListMerge

namespace LeanTrominoes.CompletionPattern

theorem list_toFinset_eq {α : Type} [DecidableEq α] (xs : List α) (distinct : xs.Nodup) :
    xs.toFinset = (⟨(↑xs : Multiset α),distinct⟩ : Finset α) := by
  ext x
  simp

def mergeCells (t : Tromino) (ps : List (Placement Unit)) : List Cell :=
  let cells := TrominoFiniteSortedCover.cells t ps
  CompletionListMerge.sort (fun a b => decide (a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 ≤ b.2))
    cells.length cells

theorem mergeCells_perm (t : Tromino) (ps : List (Placement Unit)) :
    (mergeCells t ps).Perm (TrominoFiniteSortedCover.cells t ps) :=
  CompletionListMerge.sort_perm _ _ _

def mergeLists (xs ys : List Cell) : List Cell :=
  CompletionListMerge.merge (fun a b => decide (a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 ≤ b.2))
    (xs.length + ys.length) xs ys

theorem mergeLists_perm (xs ys : List Cell) : (mergeLists xs ys).Perm (xs ++ ys) :=
  CompletionListMerge.merge_perm _ _ _ _

theorem Pattern.fixed_eq_of_merge (p : Pattern) (ps : List (Placement Unit))
    (prefill : p.prefill = ps.toFinset) (region : List Cell)
    (sorted : mergeCells p.tromino ps = region) : p.fixedRegion = region.toFinset := by
  have perm : region.Perm (TrominoFiniteSortedCover.cells p.tromino ps) := by
    rw [← sorted]
    exact mergeCells_perm _ _
  ext c
  simp only [Pattern.fixedRegion,prefill,Finset.mem_biUnion,List.mem_toFinset,perm.mem_iff,
    TrominoFiniteSortedCover.cells,List.mem_flatMap]
  constructor
  · rintro ⟨q,hq,hc⟩
    exact ⟨q,hq,(PeriodicTrominoPrefill.mem_placementCells _ _ _).mpr hc⟩
  · rintro ⟨q,hq,hc⟩
    exact ⟨q,hq,(PeriodicTrominoPrefill.mem_placementCells _ _ _).mp hc⟩

theorem finiteTiling_of_merge (t : Tromino) (ps : List (Placement Unit)) (region : List Cell)
    (sorted : mergeCells t ps = region) (distinct : region.Nodup) :
    IsFiniteTiling (fun _ => t.cells) region.toFinset ps.toFinset := by
  have perm : region.Perm (TrominoFiniteSortedCover.cells t ps) := by
    rw [← sorted]
    exact mergeCells_perm _ _
  have tiled := TrominoFiniteSortedCover.finiteTiling_of_nodup t ps (perm.nodup_iff.mp distinct)
  have eq : region.toFinset = (TrominoFiniteSortedCover.cells t ps).toFinset := by
    ext c
    simp only [List.mem_toFinset,perm.mem_iff]
  rwa [eq]

theorem Pattern.holes_eq_of_merge (p : Pattern) (fixed holes region : List Cell)
    (fixed_eq : p.fixedRegion = fixed.toFinset) (region_eq : p.region = region.toFinset)
    (distinct : region.Nodup) (merged : mergeLists fixed holes = region) :
    p.region \ p.fixedRegion = holes.toFinset := by
  have perm : region.Perm (fixed ++ holes) := by
    rw [← merged]
    exact mergeLists_perm _ _
  have disjoint : List.Disjoint fixed holes :=
    List.disjoint_left.mpr fun c hf hh =>
      (List.nodup_append.mp (perm.nodup_iff.mp distinct)).2.2 c hf c hh rfl
  rw [region_eq,fixed_eq]
  ext c
  simp only [Finset.mem_sdiff,List.mem_toFinset,perm.mem_iff,List.mem_append]
  constructor
  · rintro ⟨member,absent⟩
    exact member.resolve_left absent
  · intro member
    exact ⟨Or.inr member,fun h => List.disjoint_left.mp disjoint h member⟩

end LeanTrominoes.CompletionPattern
