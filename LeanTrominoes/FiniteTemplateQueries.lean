/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteUnaryFieldBlockMapCompiler
import LeanTrominoes.AlignedUnaryListClosure
import LeanTrominoes.UnaryPrefixSumsTime

/-! # Polynomial-time queries into concatenated finite templates -/
noncomputable section
namespace LeanTrominoes.FiniteTemplateQueries
open Turing

variable {A : Type} (size : A → Nat) (offsets : A → List Nat)

def queriesFrom : Nat → List A → List Nat
  | _, [] => []
  | start, a :: rest => (offsets a).map (start + ·) ++ queriesFrom (start + size a) rest

def increments (a : A) : List Nat :=
  match (offsets a).length with
  | 0 => []
  | n + 1 => List.replicate n 0 ++ [size a]

@[simp] theorem increments_length (a : A) : (increments size offsets a).length = (offsets a).length := by
  unfold increments
  split <;> simp_all

private theorem starts_zeros (n start : Nat) (rest : List Nat) :
    PrefixSums.startsAux start (List.replicate n 0 ++ rest) =
      List.replicate n start ++ PrefixSums.startsAux start rest := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

private theorem starts_block (a : A) (start : Nat) (rest : List Nat)
    (nonempty : offsets a = [] → size a = 0) :
    PrefixSums.startsAux start (increments size offsets a ++ rest) =
      List.replicate (offsets a).length start ++ PrefixSums.startsAux (start + size a) rest := by
  unfold increments
  split
  · rename_i h
    have empty : offsets a = [] := by simpa using h
    simp [nonempty empty, h]
  · rename_i n h
    rw [List.append_assoc, starts_zeros]
    simp only [List.cons_append, List.nil_append, PrefixSums.startsAux_cons, h]
    rw [List.replicate_succ']
    simp [List.append_assoc]

private theorem add_block (localOffsets : List Nat) (start : Nat) (firstRest secondRest : List Nat) :
    UnaryAlignedAddMachine.sums (List.replicate localOffsets.length start ++ firstRest)
      (localOffsets ++ secondRest) =
        localOffsets.map (start + ·) ++ UnaryAlignedAddMachine.sums firstRest secondRest := by
  induction localOffsets with
  | nil => rfl
  | cons value rest ih => simp [List.replicate_succ, UnaryAlignedAddMachine.sums, ih]

theorem compiled_eq (nonempty : ∀ a, offsets a = [] → size a = 0) (source : List A) (start : Nat) :
    UnaryAlignedAddMachine.sums
      (PrefixSums.startsAux start (source.flatMap (increments size offsets)))
      (source.flatMap offsets) = queriesFrom size offsets start source := by
  induction source generalizing start with
  | nil => rfl
  | cons a rest ih =>
      rw [List.flatMap_cons, List.flatMap_cons, starts_block size offsets a start _ (nonempty a), add_block, ih]
      rfl

/-- Relative template indices become absolute indices in one polynomial-time pass. -/
def compiler [Fintype A] [Inhabited A]
    (nonempty : ∀ a, offsets a = [] → size a = 0) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (queriesFrom size offsets 0) := by
  let starts := TM2CompositionMachine.computableInPolyTime
    (FiniteUnaryFieldBlockMap.computableInPolyTime (increments size offsets))
    UnaryPrefixSumsMachine.computableInPolyTime
  let result := AlignedUnaryListClosure.addedComputableInPolyTime id
    (fun source => PrefixSums.starts (source.flatMap (increments size offsets)))
    (fun source => source.flatMap offsets) (fun source => by
      simp only [PrefixSums.starts_length, List.length_flatMap, increments_length])
    starts (FiniteUnaryFieldBlockMap.computableInPolyTime offsets)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result (fun source =>
    congrArg UnaryFieldEncoderMachine.unaryFields (compiled_eq size offsets nonempty source 0))

end LeanTrominoes.FiniteTemplateQueries
end
