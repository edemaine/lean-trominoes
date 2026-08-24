/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

/-! # Pure output functions for finite-state word transducers -/

namespace LeanTrominoes.FiniteStateTransducer

universe u v w

/-- Scan a word from left to right, carrying finite control and concatenating
the finite word emitted at each transition. -/
def scan {Control : Type u} {Source : Type v} {Target : Type w}
    (transition : Control → Source → Control × List Target) :
    Control → List Source → Control × List Target
  | control, [] => (control, [])
  | control, symbol :: input =>
      let current := transition control symbol
      let rest := scan transition current.1 input
      (rest.1, current.2 ++ rest.2)

/-- Complete output, including the terminal word selected by the final
control state. -/
def output {Control : Type u} {Source : Type v} {Target : Type w}
    (initial : Control)
    (transition : Control → Source → Control × List Target)
    (finish : Control → List Target) (input : List Source) : List Target :=
  let scanned := scan transition initial input
  scanned.2 ++ finish scanned.1

end LeanTrominoes.FiniteStateTransducer
