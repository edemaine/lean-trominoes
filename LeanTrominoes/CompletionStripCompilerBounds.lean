/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionStripCompilerData
import LeanTrominoes.PartrecBinaryLengthSpace

/-! # Bit bounds for the uncovered-strip scan -/
namespace LeanTrominoes.PeriodicStripTrominoPrefill.Raw.Compiler
open Turing.PartrecToTM2

theorem nat_bits_le (n : Nat) : (Computability.encodeNat n).length ≤ n+1 :=
  encodeNat_length_le_of_lt_pow n (n+1) (lt_trans (Nat.lt_succ_self n) (Nat.lt_two_pow_self))

theorem fields_space_le (xs : List Nat) : encodedListSpace xs ≤ xs.sum+2*xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := nat_bits_le a
    simp only [encodedListSpace_cons,List.sum_cons,List.length_cons]
    omega

theorem raw_space_le (input : PeriodicStripTrominoPrefill) :
    encodedListSpace (fields input) ≤ 3*(CompletionStripEncoding.finEncoding.encode input).length+5 := by
  have h := fields_space_le (fields input)
  simpa only [fields,List.sum_cons,List.length_cons,bound,
    CompletionStripEncoding.finEncoding,CompletionStripEncoding.unaryFields_length] using
    (show encodedListSpace (fields input) ≤
      3*((CompletionStripEncoding.fields input).sum+(CompletionStripEncoding.fields input).length)+5 by
      simp only [fields,List.sum_cons,List.length_cons,bound] at h ⊢
      omega)

theorem packed_bits_le (t : Tromino) (input : PeriodicStripTrominoPrefill)
    (hh : 0 < input.height) (n : Nat) (hn : n ≤ input.period*input.height) :
    (Computability.encodeNat (PackedFields.pack (base input) (records t input n).reverse)).length ≤
      (base input+1)*(2*n) := by
  have bounded : ∀ a ∈ (records t input n).reverse, a < base input := by
    simpa using records_bounded t input hh n hn
  have packed := PackedFields.pack_lt_pow (base input) (records t input n).reverse
    (by unfold base; omega) bounded
  have power : base input ≤ 2^(base input+1) :=
    (Nat.le_succ _).trans (Nat.le_of_lt Nat.lt_two_pow_self)
  have powered := Nat.pow_le_pow_left power (records t input n).reverse.length
  rw [← pow_mul] at powered
  have bits := encodeNat_length_le_of_lt_pow _ _ (lt_of_lt_of_le packed powered)
  have len := emitted_length_le t input n
  simp only [List.length_reverse,records_length] at bits
  exact bits.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 len))

def scanSpace (input : PeriodicStripTrominoPrefill) : Nat :=
  (base input+1)*(2*(input.period*input.height)) + 3*(input.period*input.height) +
    encodedListSpace (fields input)+6

theorem payload_space (t : Tromino) (input : PeriodicStripTrominoPrefill)
    (hh : 0 < input.height) (n : Nat) (hn : n ≤ input.period*input.height) :
    encodedListSpace (payload t input n) ≤ scanSpace input := by
  have word := packed_bits_le t input hh n hn
  have count := nat_bits_le (records t input n).length
  have index := nat_bits_le n
  have len := emitted_length_le t input n
  rw [records_length] at count
  have prod := Nat.mul_le_mul_left (base input+1) (Nat.mul_le_mul_left 2 hn)
  simp only [payload,List.cons_append,List.nil_append,encodedListSpace_cons,scanSpace]
  rw [records_length]
  omega

theorem scanSpace_polynomial (input : PeriodicStripTrominoPrefill) :
    scanSpace input ≤ 20*((CompletionStripEncoding.finEncoding.encode input).length+1)^3 := by
  let n := (CompletionStripEncoding.finEncoding.encode input).length
  have hh : input.height ≤ n := CompletionStripEncoding.height_le_length input
  have hp : input.period ≤ n := CompletionStripEncoding.period_le_length input
  have area : input.period*input.height ≤ n*n := Nat.mul_le_mul hp hh
  have raw := raw_space_le input
  change encodedListSpace (fields input) ≤ 3*n+5 at raw
  have radix : base input+1 ≤ 4*n+3 := by unfold base; omega
  have packed := Nat.mul_le_mul radix (Nat.mul_le_mul_left 2 area)
  change scanSpace input ≤ 20*(n+1)^3
  unfold scanSpace
  nlinarith

end LeanTrominoes.PeriodicStripTrominoPrefill.Raw.Compiler
