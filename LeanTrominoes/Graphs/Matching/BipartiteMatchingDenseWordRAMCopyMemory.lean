/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMCopyLoop

/-! # Memory effects and frame property of the actual path-copy instructions -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM
attribute [local simp] Reg.one Reg.rowLeft Reg.rowRight Reg.source Reg.target Reg.copyIndex Reg.rowIndex Reg.value Reg.scratch Reg.length

def copyMemory (memory : Nat → Nat) (sourceL sourceR targetL targetR : Nat) : Nat → Nat → Nat
  | 0 => memory
  | count+1 =>
    let before := copyMemory memory sourceL sourceR targetL targetR count
    let left := Function.update before (targetL+count) (before (sourceL+count))
    Function.update left (targetR+count) (left (sourceR+count))

theorem copyState_memory (d : Data) :
    (copyState d).2=
      let left := Function.update d.2 (d.1 Reg.rowLeft+(d.1 Reg.target+d.1 Reg.copyIndex))
        (d.2 (d.1 Reg.rowLeft+(d.1 Reg.source+d.1 Reg.copyIndex)))
      Function.update left (d.1 Reg.rowRight+(d.1 Reg.target+d.1 Reg.copyIndex))
        (left (d.1 Reg.rowRight+(d.1 Reg.source+d.1 Reg.copyIndex))) := by
  simp [copyState,copy8,copy7,copy6,copy5,copy4,copy3,copy2,copy1,readState,writeState,NaturalData.set,NaturalData.store]

theorem copyMemory_frame (memory : Nat → Nat) (sourceL sourceR targetL targetR count address : Nat)
    (outside : ∀ j, j<count → address≠targetL+j ∧ address≠targetR+j) :
    copyMemory memory sourceL sourceR targetL targetR count address=memory address := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have last := outside count (by omega)
    simp only [copyMemory,Function.update_of_ne last.2,Function.update_of_ne last.1]
    exact ih (fun j hj => outside j (by omega))

theorem copy_iterate_memory (d : Data) (count : Nat) (unit : d.1 Reg.one=1) (start : d.1 Reg.copyIndex=0) :
    (copyState^[count] d).2=copyMemory d.2
      (d.1 Reg.rowLeft+d.1 Reg.source) (d.1 Reg.rowRight+d.1 Reg.source)
      (d.1 Reg.rowLeft+d.1 Reg.target) (d.1 Reg.rowRight+d.1 Reg.target) count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [Function.iterate_succ_apply',copyState_memory]
    have index : (copyState^[count] d).1 Reg.copyIndex=count := by rw [copy_iterate_index,start,unit]; omega
    rw [index,copy_iterate_fixed _ _ Reg.rowLeft (by decide),copy_iterate_fixed _ _ Reg.rowRight (by decide),
      copy_iterate_fixed _ _ Reg.target (by decide),copy_iterate_fixed _ _ Reg.source (by decide),ih]
    simp only [copyMemory,Nat.add_assoc]

theorem copyMemory_left (memory : Nat → Nat) (sourceL sourceR targetL targetR limit count j : Nat)
    (within : count≤limit) (copied : j<count)
    (separateTargets : ∀ i k, i<limit → k<limit → targetL+i≠targetR+k)
    (separateSource : ∀ i k, i<limit → k<limit → sourceL+i≠targetL+k ∧ sourceL+i≠targetR+k) :
    copyMemory memory sourceL sourceR targetL targetR count (targetL+j)=memory (sourceL+j) := by
  induction count with
  | zero => omega
  | succ count ih =>
    by_cases last : j=count
    · subst j
      simp only [copyMemory,Function.update_of_ne (separateTargets count count (by omega) (by omega)),Function.update_self]
      exact copyMemory_frame memory sourceL sourceR targetL targetR count (sourceL+count)
        (fun k hk => separateSource count k (by omega) (by omega))
    · have different : targetL+j≠targetL+count := by omega
      simp only [copyMemory,Function.update_of_ne (separateTargets j count (by omega) (by omega)),Function.update_of_ne different]
      exact ih (by omega) (by omega)

theorem copyMemory_right (memory : Nat → Nat) (sourceL sourceR targetL targetR limit count j : Nat)
    (within : count≤limit) (copied : j<count)
    (separateTargets : ∀ i k, i<limit → k<limit → targetL+i≠targetR+k)
    (separateSource : ∀ i k, i<limit → k<limit → sourceR+i≠targetL+k ∧ sourceR+i≠targetR+k) :
    copyMemory memory sourceL sourceR targetL targetR count (targetR+j)=memory (sourceR+j) := by
  induction count with
  | zero => omega
  | succ count ih =>
    by_cases last : j=count
    · subst j
      simp only [copyMemory,Function.update_self,
        Function.update_of_ne (separateSource count count (by omega) (by omega)).1]
      exact copyMemory_frame memory sourceL sourceR targetL targetR count (sourceR+count)
        (fun k hk => separateSource count k (by omega) (by omega))
    · have different : targetR+j≠targetR+count := by omega
      have cross := Ne.symm (separateTargets count j (by omega) (by omega))
      simp only [copyMemory,Function.update_of_ne different,Function.update_of_ne cross]
      exact ih (by omega) (by omega)

end LeanTrominoes.BipartiteMatching.DenseWordRAM
