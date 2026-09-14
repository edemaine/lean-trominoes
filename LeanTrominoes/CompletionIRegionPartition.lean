import LeanTrominoes.CompletionIRegionGeometry
import LeanTrominoes.CompletionPatternMergeCover

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

theorem Atom.prefill_list_eq (a : Atom) : a.motif.toFinset = a.pattern.prefill := by
  cases a
  · exact list_toFinset_eq _ IGuardedEqBoundary.prefillSet.nodup
  · exact list_toFinset_eq _ IGuardedNegBoundary.prefillSet.nodup
  · exact list_toFinset_eq _ IGuardedPlugTopBoundary.prefillSet.nodup
  · exact list_toFinset_eq _ IGuardedPlugBotBoundary.prefillSet.nodup
  · exact list_toFinset_eq _ IGuardedDup.prefillSet.nodup
  · exact list_toFinset_eq _ IGuardedTftsat.prefillSet.nodup

theorem Atom.region_list_eq (a : Atom) : a.regionCells.toFinset = a.pattern.region := by
  ext c
  rw [List.mem_toFinset]
  change c ∈ a.regionCells ↔ c ∈ a.pattern.region.val
  rw [a.region_val]
  rfl

theorem Atom.region_list_nodup (a : Atom) : a.regionCells.Nodup := by
  have h := a.pattern.region.nodup
  rw [a.region_val] at h
  exact h

theorem Atom.holes_of_merge (a : Atom) (holes : List Cell)
    (fixed_eq : a.fixed = a.pattern.fixedRegion)
    (merged : mergeLists a.fixedList holes = a.regionCells) :
    a.pattern.region \ a.fixed = holes.toFinset := by
  have fixed_list_eq : a.fixedList.toFinset = a.fixed :=
    CompletionCellOrder.toFinset_eq a.fixedList a.fixed.nodup
  have h := a.pattern.holes_eq_of_merge a.fixedList holes a.regionCells
    (fixed_eq.symm.trans fixed_list_eq.symm) a.region_list_eq.symm a.region_list_nodup merged
  rwa [← fixed_eq] at h

end LeanTrominoes.CompletionPattern.IBricks
