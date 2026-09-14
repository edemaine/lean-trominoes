/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicTrominoCompletion
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort

namespace LeanTrominoes.TrominoFiniteSortedCover

def cells (t : Tromino) (ps : List (Placement Unit)) : List Cell :=
  ps.flatMap (PeriodicTrominoPrefill.placementCells t)

def sortedCells (t : Tromino) (ps : List (Placement Unit)) : List Cell :=
  (cells t ps).insertionSort fun a b => a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 ≤ b.2

theorem finiteTiling_of_nodup (t : Tromino) (ps : List (Placement Unit))
    (distinct : (cells t ps).Nodup) :
    IsFiniteTiling (fun _ => t.cells) (cells t ps).toFinset ps.toFinset := by
  apply (isFiniteTiling_iff_isTiling _ _ _).mpr
  have pairs := (List.nodup_flatMap.mp distinct).2
  letI : Std.Symm (fun p q : Placement Unit =>
      List.Disjoint (PeriodicTrominoPrefill.placementCells t p)
        (PeriodicTrominoPrefill.placementCells t q)) := ⟨fun _ _ h => h.symm⟩
  constructor
  · intro p hp c hc
    exact List.mem_toFinset.mpr (List.mem_flatMap.mpr
      ⟨p,List.mem_toFinset.mp hp,(PeriodicTrominoPrefill.mem_placementCells t p c).mpr hc⟩)
  · intro c hc
    obtain ⟨p,hp,hpc⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hc)
    refine ⟨p,⟨List.mem_toFinset.mpr hp,(PeriodicTrominoPrefill.mem_placementCells t p c).mp hpc⟩,?_⟩
    intro q hq
    by_contra neq
    have dis := pairs.forall (List.mem_toFinset.mp hq.1) hp neq
    exact List.disjoint_left.mp dis
      ((PeriodicTrominoPrefill.mem_placementCells t q c).mpr hq.2) hpc

theorem finiteTiling_of_sorted (t : Tromino) (ps : List (Placement Unit))
    (region : List Cell) (sorted : sortedCells t ps = region) (distinct : region.Nodup) :
    IsFiniteTiling (fun _ => t.cells) region.toFinset ps.toFinset := by
  have perm : region.Perm (cells t ps) := by
    rw [← sorted]
    exact List.perm_insertionSort _ _
  have tiled := finiteTiling_of_nodup t ps (perm.nodup_iff.mp distinct)
  have eq : region.toFinset = (cells t ps).toFinset := by
    ext c
    simp only [List.mem_toFinset,perm.mem_iff]
  rwa [eq]

end LeanTrominoes.TrominoFiniteSortedCover
