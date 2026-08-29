/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteRoleSlotUnaryDecoderArithmetic
import LeanTrominoes.FiniteRoleSlotUnaryDecoderTransducerData
import LeanTrominoes.FiniteStateTransducerSemantics

/-! # Streaming correctness of generic unary role/slot decoding -/

noncomputable section

namespace LeanTrominoes.FiniteRoleSlotUnaryDecoder

variable {Role : Type} [Fintype Role] [Nonempty Role]

theorem scan_unaryField (control : Control Role) (code : Nat) :
    FiniteStateTransducer.scan transition control
        (UnaryFieldEncoderMachine.unaryField code) =
      (zero, [decode (advance control code)]) := by
  induction code generalizing control with
  | zero => rfl
  | succ code induction =>
      rw [UnaryFieldEncoderMachine.unaryField,
        List.replicate_succ, List.cons_append]
      simp only [FiniteStateTransducer.scan, transition]
      rw [← UnaryFieldEncoderMachine.unaryField]
      simpa only [advance_succ, List.nil_append] using
        induction (increment control)

theorem scan_unaryFields (codes : List Nat) :
    FiniteStateTransducer.scan transition (zero (Role := Role))
        (UnaryFieldEncoderMachine.unaryFields codes) =
      (zero, pairs codes) := by
  induction codes with
  | nil => rfl
  | cons code codes induction =>
      rw [UnaryFieldEncoderMachine.unaryFields_cons,
        FiniteStateTransducer.scan_append, scan_unaryField]
      dsimp only
      have advanceZero :
          advance (zero (Role := Role)) code = boundedCode code := by
        simpa [zero] using
          (advance_boundedCode (Role := Role) 0 code)
      rw [advanceZero, induction]
      rfl

theorem output_unaryFields (codes : List Nat) :
    FiniteStateTransducer.output (zero (Role := Role)) transition finish
        (UnaryFieldEncoderMachine.unaryFields codes) =
      pairs codes := by
  simp [FiniteStateTransducer.output, scan_unaryFields, finish]

end LeanTrominoes.FiniteRoleSlotUnaryDecoder

end
