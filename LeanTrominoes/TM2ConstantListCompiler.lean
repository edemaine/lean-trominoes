/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Constant finite-list output compilers -/

noncomputable section

namespace LeanTrominoes.TM2ConstantListCompiler

open Computability Turing

def transition {Source Target : Type} :
    Unit → Source → Unit × List Target :=
  fun _ _ => ((), [])

def finish {Target : Type} (output : List Target) : Unit → List Target :=
  fun _ => output

@[simp] theorem output_eq {Source Target : Type}
    (output : List Target) (input : List Source) :
    FiniteStateTransducer.output () transition (finish output) input =
      output := by
  unfold FiniteStateTransducer.output
  induction input with
  | nil => rfl
  | cons symbol input induction =>
      simp only [FiniteStateTransducer.scan, transition, List.nil_append,
        induction]

/-- A fixed finite output word is polynomial-time computable under every
finite input alphabet, including the empty alphabet. -/
noncomputable def computableInPolyTime
    {Input InputSymbol OutputSymbol : Type}
    [Fintype InputSymbol] [Fintype OutputSymbol] [Inhabited OutputSymbol]
    (encodeInput : Input → List InputSymbol) (output : List OutputSymbol) :
    TM2ComputableInPolyTime encodeInput id (fun _ : Input => output) := by
  let physical := FiniteStateTransducer.computableInPolyTime
    () (transition (Source := InputSymbol)) (finish output)
  exact TM2PolyTimeInputEncodingTransport.of_prepare encodeInput physical
    (fun _ => rfl) (fun input => output_eq output (encodeInput input))

end LeanTrominoes.TM2ConstantListCompiler

end
