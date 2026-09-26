/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.NormalizedOrientationFlatEncoding
import LeanTrominoes.BinaryFieldBoundedDecoder
import LeanTrominoes.UnaryFieldAggregateCompiler

/-! # Bounded native preparation for normalized orientation

Valid drawing dimensions are bounded by the explicitly stored cell table.
All cell codes lie in a fixed finite range. Bounded binary decoding therefore
recovers every field on well-formed drawings in polynomial time, while large
malformed dimensions produce an overflow marker instead of huge unary data.
-/
noncomputable section
namespace LeanTrominoes.Gadget.NormalizedOrientation.BoundedPreparation
open Turing UnaryColumn PeriodicOrthogonalDrawing FlatEncoding
abbrev Symbol := PeriodicCNFFlatEncoding.Symbol

def cellBound : Nat := (Finset.univ.sum fun c : OrthogonalCellType => cellCode c) + 1

theorem cellCode_lt (c : OrthogonalCellType) : cellCode c < cellBound := by
  have h : cellCode c ≤ Finset.univ.sum (fun c : OrthogonalCellType => cellCode c) :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  unfold cellBound
  omega

def bound (s : List Symbol) : Nat := s.length + cellBound + 1

private theorem fields_length_le (fields : List Nat) :
    fields.length ≤ (PeriodicCNFFlatEncoding.encodeNatFields fields).length := by
  rw [PeriodicCNFFlatEncoding.encodeNatFields_length]
  induction fields with
  | nil => simp
  | cons a rest ih => simp only [List.length_cons,List.map_cons,List.sum_cons]; omega

theorem fields_bounded (d : PeriodicOrthogonalDrawing) (wf : d.IsWellFormed) :
    ∀ n ∈ fields d, n < bound (finEncoding.encode d) := by
  have stored := fields_length_le (fields d)
  have cellLength : d.cellTypes.length ≤ (finEncoding.encode d).length := by
    change _ ≤ (PeriodicCNFFlatEncoding.encodeNatFields (fields d)).length
    have count : (fields d).length = d.cellTypes.length+2 := by simp [fields]
    rw [count] at stored
    omega
  have widthPositive : 0 < d.horizontalPeriod := by simp [horizontalPeriod]
  have heightPositive : 0 < d.verticalPeriod := by simp [verticalPeriod]
  have len : d.cellTypes.length = d.horizontalPeriod*d.verticalPeriod := wf.1
  have widthBound : d.horizontalPeriod ≤ d.cellTypes.length := by
    rw [len]
    exact Nat.le_mul_of_pos_right _ heightPositive
  have heightBound : d.verticalPeriod ≤ d.cellTypes.length := by
    rw [len,Nat.mul_comm]
    exact Nat.le_mul_of_pos_right _ widthPositive
  have inputSmall : (finEncoding.encode d).length < bound (finEncoding.encode d) := by
    change (finEncoding.encode d).length < (finEncoding.encode d).length+cellBound+1
    omega
  intro n member
  simp only [fields,List.mem_cons,List.mem_map] at member
  rcases member with rfl | rfl | ⟨c,_,rfl⟩
  · exact (widthBound.trans cellLength).trans_lt inputSmall
  · exact (heightBound.trans cellLength).trans_lt inputSmall
  · have h := cellCode_lt c
    unfold bound
    omega

def lengthCompiler : ScalarCompiler (fun s : List Symbol => s.length) := by
  let physical := TM2CompositionMachine.computableInPolyTime
    (FiniteBlockTransducer.computableInPolyTime (fun _ : Symbol => [()]))
    UnaryFieldUnitLengthBroadcast.singletonComputableInPolyTime
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  simp only [← List.map_eq_flatMap,List.length_map]

def boundCompiler : ScalarCompiler bound := by
  let length : Compiler (fun _ : List Symbol => [()]) (fun s _ => s.length) := lengthCompiler
  apply TM2ComputableInPolyTime.of_eq (add length (constant length (cellBound+1)))
  intro s
  simp [bound,Nat.add_assoc]

def prepare (s : List Symbol) : List Nat := BinaryFieldBoundedDecoder.values (bound s) s

def compiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields prepare :=
  BinaryFieldBoundedDecoder.compiler boundCompiler

theorem prepare_encoded (d : PeriodicOrthogonalDrawing) (wf : d.IsWellFormed) :
    prepare (finEncoding.encode d) = (fields d).map (·+1) ++ [1] := by
  exact BinaryFieldBoundedDecoder.values_fields_bounded (bound (finEncoding.encode d))
    (by unfold bound; omega) (fields d) (fields_bounded d wf)

end LeanTrominoes.Gadget.NormalizedOrientation.BoundedPreparation
end
