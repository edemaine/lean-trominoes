/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerData
import LeanTrominoes.FiniteStateTransducerFunctionData

/-! # Compatibility of lightweight and machine-backed transducer outputs -/

namespace LeanTrominoes.LightweightFiniteStateTransducer

universe u v w

theorem scan_eq_finiteState
    {Control : Type u} {Source : Type v} {Target : Type w}
    (transition : Control → Source → Control × List Target)
    (control : Control) (input : List Source) :
    scan transition control input =
      FiniteStateTransducer.scan transition control input := by
  induction input generalizing control with
  | nil => rfl
  | cons symbol input induction =>
      simp only [scan, FiniteStateTransducer.scan]
      rw [induction]

@[simp] theorem output_eq_finiteState
    {Control : Type u} {Source : Type v} {Target : Type w}
    (initial : Control)
    (transition : Control → Source → Control × List Target)
    (finish : Control → List Target) (input : List Source) :
    output initial transition finish input =
      FiniteStateTransducer.output initial transition finish input := by
  simp [output, FiniteStateTransducer.output, scan_eq_finiteState]

end LeanTrominoes.LightweightFiniteStateTransducer
