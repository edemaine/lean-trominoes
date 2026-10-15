/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Encoding.Unary.UnaryColumnFieldLookup
import LeanTrominoes.Computation.Encoding.Unary.UnaryColumnSerialization
import LeanTrominoes.Computation.Encoding.Unary.UnaryColumnDivisionCompiler
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.GetD

/-! # Exact unary maxima through a bounded ordered support scan -/
noncomputable section
namespace LeanTrominoes.UnaryColumn
open _root_.Computability Turing
set_option maxHeartbeats 2000000

def orderedSupport (values : List Nat) (bound : Nat) : List Nat :=
  (List.range bound).filter fun n => decide (n∈values)

private theorem lastSupport_eq_sup (values : List Nat) (bound : Nat) :
    (orderedSupport values bound).getD ((orderedSupport values bound).length-1) 0=
      ((Finset.range bound).filter fun n => n∈values).sup id := by
  induction bound with
  | zero => simp [orderedSupport]
  | succ bound ih =>
    have le : ((Finset.range bound).filter fun n => n∈values).sup id≤bound := by
      apply Finset.sup_le
      intro n member
      have lt := Finset.mem_range.mp (Finset.mem_filter.mp member).1
      exact Nat.le_of_lt lt
    by_cases member : bound∈values
    · simp only [orderedSupport,List.range_succ,List.filter_append,List.filter_cons,
        member,decide_true,List.filter_nil,↓reduceIte,List.length_append,List.length_singleton,Nat.add_sub_cancel]
      rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)]
      have eq : ((Finset.range (bound+1)).filter fun n => n∈values)=
          insert bound ((Finset.range bound).filter fun n => n∈values) := by
        ext n
        by_cases same : n=bound <;> simp [Finset.range_add_one,same,member]
      rw [eq,Finset.sup_insert]
      simp [max_eq_left le]
    · have eq : ((Finset.range (bound+1)).filter fun n => n∈values)=
          ((Finset.range bound).filter fun n => n∈values) := by
        ext n
        by_cases same : n=bound <;> simp [Finset.range_add_one,same,member]
      rw [eq]
      simpa [orderedSupport,List.range_succ,member] using ih

theorem lastSupport_eq_maximum (values : List Nat) (bound : Nat)
    (bounded : ∀ n∈values,n<bound) :
    (orderedSupport values bound).getD ((orderedSupport values bound).length-1) 0=values.toFinset.sup id := by
  rw [lastSupport_eq_sup]
  congr 1
  ext n
  simp only [Finset.mem_filter,Finset.mem_range,List.mem_toFinset]
  exact ⟨fun member => member.2,fun member => ⟨bounded n member,member⟩⟩

variable {Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]
  {rows : List Symbol → List Index} {value : List Symbol → Index → Nat}

/-- Unary magnitude bounds make an exact maximum polynomial-time computable,
including empty columns and duplicate values. -/
def maximum (column : Compiler rows value) :
    ScalarCompiler (fun s => ((rows s).map (value s)).toFinset.sup id) := by
  classical
  let bound := columnBound column
  let keys := naturalRange bound
  let datum := fun s n => if n∈(rows s).map (value s) then 1 else 0
  let present := keyedSupported keys column (constant column 1) datum (by
    intro s i hi
    simp only [datum,if_pos (List.mem_map.mpr ⟨i,hi,rfl⟩)]) (by
    intro s n hn absent
    apply if_neg
    intro member
    obtain ⟨i,hi,eq⟩ := List.mem_map.mp member
    exact absent ⟨i,hi,eq⟩)
  let control : TM2ComputableInPolyTime id id (fun s =>
      (List.range (((rows s).map (value s)).sum+1)).map fun n =>
        decide (n∈(rows s).map (value s))) := (bits present).of_eq (fun s => by
    apply List.map_congr_left
    intro n _
    by_cases member : n∈(rows s).map (value s) <;>
      simp only [datum,member,↓reduceIte] <;> decide)
  let selected := filter keys control
  let count : Compiler (fun _ : List Symbol => [()]) (fun s _ =>
      (orderedSupport ((rows s).map (value s)) (((rows s).map (value s)).sum+1)).length) :=
    (TM2CompositionMachine.computableInPolyTime selected UnaryFieldAggregate.countCompiler).of_eq
      (fun s => by simp only [List.length_map]; rfl)
  let index := sub count (constant count 1)
  let result := fieldLookup index selected
  apply result.of_eq
  intro s
  have bounded : ∀ n∈(rows s).map (value s),n<((rows s).map (value s)).sum+1 := by
    intro n member
    have le := List.le_sum_of_mem member
    omega
  simpa [orderedSupport] using congrArg (fun n : Nat => [n])
    (lastSupport_eq_maximum ((rows s).map (value s)) _ bounded)
end LeanTrominoes.UnaryColumn
