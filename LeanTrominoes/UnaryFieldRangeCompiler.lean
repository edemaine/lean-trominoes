/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.UnaryFieldConstantStreamCompiler
import LeanTrominoes.UnaryPrefixSumsTime

/-! # Consecutive unary indices aligned with a field stream -/

noncomputable section

namespace LeanTrominoes
namespace UnaryFieldRange

open Computability Turing

/-- The consecutive positions of an arbitrary list. -/
def values (source : List Nat) : List Nat := List.range source.length

private theorem startsAux_ones (start : Nat) (count : Nat) :
    PrefixSums.startsAux start (List.replicate count 1) =
      List.range' start count := by
  induction count generalizing start with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, PrefixSums.startsAux_cons,
        List.range'_succ, induction]

theorem starts_ones (source : List Nat) :
    PrefixSums.starts (UnaryFieldConstantStreams.ones source) =
      values source := by
  unfold UnaryFieldConstantStreams.ones values PrefixSums.starts
  have onesEq : source.map (fun _ => 1) =
      List.replicate source.length 1 := by
    induction source with
    | nil => rfl
    | cons value source induction =>
        rw [List.map_cons, induction, List.length_cons]
        rw [List.replicate_succ]
  rw [onesEq, startsAux_ones]
  rw [List.range'_eq_map_range]
  simp

/-- Reading only the delimiters of a unary stream and prefix-summing unit
fields emits `0, 1, ..., n - 1` in polynomial time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields
      UnaryFieldEncoderMachine.unaryFields values := by
  let composed := TM2CompositionMachine.computableInPolyTime
    UnaryFieldConstantStreams.onesComputableInPolyTime
    UnaryPrefixSumsMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq composed
    (fun source => congrArg UnaryFieldEncoderMachine.unaryFields
      (starts_ones source))

end UnaryFieldRange
end LeanTrominoes

end
