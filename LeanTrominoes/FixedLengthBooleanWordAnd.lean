/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedLengthWordEvaluator
import LeanTrominoes.SeparatedProductEncoding
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Pointwise conjunction of two fixed-length Boolean words -/

noncomputable section

namespace LeanTrominoes
namespace FixedLengthBooleanWordAnd

open Computability Turing

abbrev Token := SeparatedProductEncoding.Token Bool Bool

instance : Inhabited Token := ⟨.separator⟩

def leftValues (tokens : List Token) : List Bool :=
  tokens.filterMap fun
    | .left value => some value
    | _ => none

def rightValues (tokens : List Token) : List Bool :=
  tokens.filterMap fun
    | .right value => some value
    | _ => none

def finish (tokens : List Token) : List Bool :=
  List.zipWith (· && ·) (leftValues tokens) (rightValues tokens)

/-- Store one complete separated fixed-length word pair and conjoin its two
Boolean components pointwise. -/
def output (length : Nat) (pair : List Bool × List Bool) : List Bool :=
  FixedLengthWordEvaluator.output (2 * length + 1) finish
    (SeparatedProductEncoding.encode id id pair)

@[simp] theorem leftValues_encode (first second : List Bool) :
    leftValues (SeparatedProductEncoding.encode id id (first, second)) =
      first := by
  simp [leftValues, SeparatedProductEncoding.encode]

@[simp] theorem rightValues_encode (first second : List Bool) :
    rightValues (SeparatedProductEncoding.encode id id (first, second)) =
      second := by
  simp [rightValues, SeparatedProductEncoding.encode]

@[simp] theorem finish_encode (first second : List Bool) :
    finish (SeparatedProductEncoding.encode id id (first, second)) =
      List.zipWith (· && ·) first second := by
  simp [finish]

/-- On two words of the declared length, the fixed evaluator returns their
exact pointwise conjunction. -/
theorem output_eq_zipWith
    (length : Nat) (first second : List Bool)
    (firstLength : first.length = length)
    (secondLength : second.length = length) :
    output length (first, second) =
      List.zipWith (· && ·) first second := by
  unfold output
  rw [FixedLengthWordEvaluator.output_eq_of_length_eq]
  · exact finish_encode first second
  · rw [SeparatedProductEncoding.encode_length]
    simp only [id_eq, firstLength, secondLength]
    omega

/-- Pointwise conjunction of two fixed-length Boolean words is
polynomial-time under their separated pair encoding. -/
noncomputable def outputComputableInPolyTime (length : Nat) :
    TM2ComputableInPolyTime
      (SeparatedProductEncoding.encode id id) id (output length) := by
  let physical := FixedLengthWordEvaluator.computableInPolyTime
    (2 * length + 1) finish
  exact TM2PolyTimeInputEncodingTransport.of_prepare
    (SeparatedProductEncoding.encode id id) physical
    (fun _ => rfl) (fun _ => by unfold output; rfl)

end FixedLengthBooleanWordAnd
end LeanTrominoes

end
