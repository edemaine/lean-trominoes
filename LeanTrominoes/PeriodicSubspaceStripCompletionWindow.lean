/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicSubspaceStripWindow
import LeanTrominoes.PeriodicSubspaceCompletion

/-! # Finite windows for completion by arbitrary prescribed placement orbits -/
namespace LeanTrominoes.PeriodicSubspaceTiling.Strip
abbrev CompletionData := CompletionInput Int

def CompletionValid (data : CompletionData) (bound : Nat) (w : Window data.1 bound) : Prop :=
  Valid data.1 bound w ∧ ∀ r∈data.1.2, r.1.1∈data.2 →
    value data.1 r.1.1 (w (center bound))=true

theorem completable_iff_windows (data : CompletionData) (bound : Nat)
    (bounded : Bounded data.1 bound) :
    Completable data ↔ LocalWindow.Satisfiable (2*bound) (CompletionValid data bound) := by
  classical
  constructor
  · rintro ⟨selected,tiled,forced⟩
    refine ⟨fun x i => selected data.1.2[i].1.1 x,fun x =>
      ⟨windows_of_tiling data.1 bound bounded selected tiled x,?_⟩⟩
    intro r hr hk
    change value data.1 r.1.1 (fun i => selected data.1.2[i].1.1 (x+bound))=true
    rw [value_assignment data.1 r.1.1 (fun k => selected k (x+bound)) ⟨r,hr,rfl⟩]
    exact forced r.1.1 hk _
  · rintro ⟨configuration,valid⟩
    let a := fun k z => value data.1 k (configuration z)
    let selected := fun k z => if ∃ r∈data.1.2, r.1.1=k then a k z else true
    have equal (r) (hr : r∈data.1.2) (z) : selected r.1.1 z=a r.1.1 z := by
      simp only [selected,if_pos (show ∃ s∈data.1.2, s.1.1=r.1.1 from ⟨r,hr,rfl⟩)]
    have tiled := tiling_of_windows data.1 bound bounded configuration (fun x => (valid x).1)
    refine ⟨selected,⟨?_,?_⟩,?_⟩
    · intro r hr z one
      rw [equal r hr z] at one
      exact tiled.1 r hr z one
    · intro q hq z
      have candidate_equal (c : Nat × Int) (hc : c∈candidates data.1 q) :
          selected c.1 (z+c.2)=a c.1 (z+c.2) := by
        obtain ⟨r,hr,_,rfl⟩ := candidate_record data.1 hc
        exact equal r hr _
      obtain ⟨c,hc,unique⟩ := tiled.2 q hq z
      refine ⟨c,⟨hc.1,?_⟩,?_⟩
      · rw [candidate_equal c hc.1]; exact hc.2
      · intro e he
        rw [candidate_equal e he.1] at he
        exact unique e he
    · intro k hk z
      by_cases present : ∃ r∈data.1.2, r.1.1=k
      · obtain ⟨r,hr,rfl⟩ := present
        rw [equal r hr z]
        have forced := (valid (z-bound)).2 r hr hk
        change value data.1 r.1.1 (configuration ((z-bound)+bound))=true at forced
        simpa only [a,sub_add_cancel] using forced
      · simp only [selected,if_neg present]

theorem completable_iff_cycle (data : CompletionData) (bound : Nat)
    (bounded : Bounded data.1 bound) :
    Completable data ↔ FiniteState.HasCycle (LocalWindow.Transition (CompletionValid data bound)) := by
  rw [completable_iff_windows data bound bounded,LocalWindow.satisfiable_iff_cycle]

end LeanTrominoes.PeriodicSubspaceTiling.Strip
