/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMCopy

/-! # Bounded execution of the full path-row copying loop -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM
attribute [local simp] Reg.one Reg.rowLeft Reg.rowRight Reg.source Reg.target Reg.copyIndex Reg.rowIndex Reg.value Reg.scratch Reg.length

theorem copyState_fixed (d : Data) (i : Fin 64)
    (different : i≠Reg.copyIndex ∧ i≠Reg.rowIndex ∧ i≠Reg.value ∧ i≠Reg.scratch) :
    (copyState d).1 i=d.1 i := by
  simp only [copyState,copy8,copy7,copy6,copy5,copy4,copy3,copy2,copy1,readState,writeState,NaturalData.set,NaturalData.store]
  simp_all

theorem copy_iterate_fixed (d : Data) (k : Nat) (i : Fin 64)
    (different : i≠Reg.copyIndex ∧ i≠Reg.rowIndex ∧ i≠Reg.value ∧ i≠Reg.scratch) :
    (copyState^[k] d).1 i=d.1 i := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',copyState_fixed _ i different,ih]

theorem copy_iterate_index (d : Data) (k : Nat) :
    (copyState^[k] d).1 Reg.copyIndex=d.1 Reg.copyIndex+k*d.1 Reg.one := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',(copyState_controls _).1,ih,
      copy_iterate_fixed _ _ Reg.one (by decide)]
    simp [Nat.add_mul,Nat.add_assoc]

attribute [local simp] copy_iterate_fixed

def CopyRoom (B count : Nat) (d : Data) : Prop :=
  d.1 Reg.source+count≤B ∧ d.1 Reg.target+count≤B ∧
  d.1 Reg.rowLeft+(d.1 Reg.source+count)≤B ∧ d.1 Reg.rowLeft+(d.1 Reg.target+count)≤B ∧
  d.1 Reg.rowRight+(d.1 Reg.source+count)≤B ∧ d.1 Reg.rowRight+(d.1 Reg.target+count)≤B ∧ count≤B

theorem copy_iteration {B count k : Nat} (d : Data) (room : CopyRoom B count d)
    (unit : d.1 Reg.one=1) (start : d.1 Reg.copyIndex=0) (within : k<count)
    (before : NaturalData.Bounded B (copyState^[k] d)) :
    Natural.Exec B copyPair (copyState^[k] d) (copyState^[k+1] d) 13 := by
  have index : (copyState^[k] d).1 Reg.copyIndex=k := by rw [copy_iterate_index,start,unit]; omega
  have one := copy_iterate_fixed d k Reg.one (by decide)
  have source := copy_iterate_fixed d k Reg.source (by decide)
  have target := copy_iterate_fixed d k Reg.target (by decide)
  have left := copy_iterate_fixed d k Reg.rowLeft (by decide)
  have right := copy_iterate_fixed d k Reg.rowRight (by decide)
  have trace := copyPair_exec (copyState^[k] d) before
    (by rw [source,target,index]; rcases room with ⟨a,b,c,e,f,g,h⟩; omega)
    (by rw [source,target,index,left,right]; rcases room with ⟨a,b,c,e,f,g,h⟩; omega)
    (by rw [index,one,unit]; rcases room with ⟨a,b,c,e,f,g,h⟩; omega)
  simpa only [Function.iterate_succ_apply'] using trace

theorem copy_prefix_bounded {B count k : Nat} (d : Data) (room : CopyRoom B count d)
    (unit : d.1 Reg.one=1) (start : d.1 Reg.copyIndex=0) (before : NaturalData.Bounded B d)
    (within : k≤count) : NaturalData.Bounded B (copyState^[k] d) := by
  induction k with
  | zero => exact before
  | succ k ih =>
    exact (copy_iteration d room unit start (by omega) (ih (by omega))).bounded (ih (by omega))

/-- Copying `count` prefix pairs takes at most `15*count+2` primitive
instructions, including loop control. Every intermediate value and address
is bounded by the same fixed natural headroom. -/
theorem copyLoop_exec {B count : Nat} (d : Data) (room : CopyRoom B count d)
    (unit : d.1 Reg.one=1) (start : d.1 Reg.copyIndex=0) (length : d.1 Reg.length=count)
    (before : NaturalData.Bounded B d) :
    ∃ cost, Natural.Exec B (.loop (.lt Reg.copyIndex Reg.length) copyPair) d (copyState^[count] d) cost ∧
      cost≤15*count+2 := by
  apply Natural.Exec.finite_loop (budget := 13) (.lt Reg.copyIndex Reg.length) copyPair (fun k => copyState^[k] d)
  · intro k hk
    simp only [Natural.Holds]
    rw [copy_iterate_index,start,unit,copy_iterate_fixed _ _ Reg.length (by decide),length]
    omega
  · simp only [Natural.Holds]
    rw [copy_iterate_index,start,unit,copy_iterate_fixed _ _ Reg.length (by decide),length]
    omega
  · intro k hk
    exact ⟨13,copy_iteration d room unit start hk (copy_prefix_bounded d room unit start before (by omega)),by omega⟩

end LeanTrominoes.BipartiteMatching.DenseWordRAM
