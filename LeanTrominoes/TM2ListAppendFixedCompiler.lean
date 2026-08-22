/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Appending one fixed word in polynomial time -/

noncomputable section

namespace LeanTrominoes
namespace TM2ListAppend

open Computability Turing

def appendFixedTransition {Symbol : Type} :
    Unit → Symbol → Unit × List Symbol :=
  fun _ symbol => ((), [symbol])

def appendFixedWords {Symbol : Type}
    (suffix input : List Symbol) : List Symbol :=
  input ++ suffix

@[simp] theorem finiteStateOutput_appendFixed
    {Symbol : Type} (suffix input : List Symbol) :
    FiniteStateTransducer.output () appendFixedTransition
        (fun _ => suffix) input =
      appendFixedWords suffix input := by
  induction input with
  | nil => rfl
  | cons symbol input induction =>
      simp only [FiniteStateTransducer.output,
        FiniteStateTransducer.scan, appendFixedTransition,
        List.cons_append, List.nil_append, appendFixedWords] at induction ⊢
      rw [induction]

/-- Appending a fixed finite suffix to a native list is polynomial-time. -/
noncomputable def appendFixedComputableInPolyTime
    {Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
    (suffix : List Symbol) :
    TM2ComputableInPolyTime id id (appendFixedWords suffix) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (FiniteStateTransducer.computableInPolyTime
      () appendFixedTransition (fun _ => suffix))
    (finiteStateOutput_appendFixed suffix)

end TM2ListAppend
end LeanTrominoes

end
