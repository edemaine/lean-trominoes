/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.GadgetDirectionTrimTransducers
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequests

/-! # Dropping the last three directions inside a retained request -/

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace NormalizationDirectionRequest
namespace DropLast

open Gadget.DirectionTrim

structure Control where
  readingRoute : Bool
  buffer : DropLastThree.Buffer
  deriving DecidableEq, Fintype

def initial : Control := ⟨false, .zero⟩

def transition : Control → Token → Control × List Token
  | control, .separator =>
      if control.readingRoute then (control, [])
      else (⟨true, .zero⟩, [.separator])
  | control, .direction direction =>
      if control.readingRoute then
        let result := DropLastThree.transition control.buffer direction
        (⟨true, result.1⟩, result.2.map .direction)
      else
        (control, [.direction direction])
  | control, token =>
      if control.readingRoute then (control, []) else (control, [token])

def finish (_ : Control) : List Token := []

def output (tokens : List Token) : List Token :=
  FiniteStateTransducer.output initial transition finish tokens

def request (input : Request) : Request :=
  { header := input.header
    directions := input.directions.take (input.directions.length - 3) }

@[simp]
theorem scan_header (header : Header) :
    FiniteStateTransducer.scan transition initial header.tokens =
      (initial, header.tokens) := by
  simp [Header.tokens, FiniteStateTransducer.scan, transition, initial]

theorem scan_route (buffer : DropLastThree.Buffer)
    (directions : List AxisDirection) :
    FiniteStateTransducer.scan transition ⟨true, buffer⟩
        (directions.map .direction) =
      let scanned := FiniteStateTransducer.scan
        DropLastThree.transition buffer directions
      (⟨true, scanned.1⟩, scanned.2.map .direction) := by
  induction directions generalizing buffer with
  | nil => rfl
  | cons direction directions induction =>
      let current := DropLastThree.transition buffer direction
      have stepEq :
          transition ⟨true, buffer⟩ (.direction direction) =
            (⟨true, current.1⟩, current.2.map .direction) := by
        simp [transition, current]
      simp only [List.map_cons, FiniteStateTransducer.scan]
      rw [stepEq]
      rw [induction current.1]
      simp [current, List.map_append]

theorem output_request (input : Request) :
    output input.tokens = (request input).tokens := by
  unfold output FiniteStateTransducer.output Request.tokens
  rw [FiniteStateTransducer.scan_append, scan_header]
  have separatorEq :
      transition initial .separator =
        (⟨true, .zero⟩, [.separator]) := by
    simp [transition, initial]
  simp only [FiniteStateTransducer.scan]
  rw [separatorEq]
  rw [scan_route .zero input.directions]
  dsimp only
  have dropped :
      (FiniteStateTransducer.scan DropLastThree.transition .zero
        input.directions).2 =
        input.directions.take (input.directions.length - 3) := by
    simpa [DropLastThree.output, FiniteStateTransducer.output,
      DropLastThree.finish] using
      DropLastThree.output_eq_take input.directions
  rw [dropped]
  simp [request, finish]

end DropLast
end NormalizationDirectionRequest
end PeriodicThreeDM
end LeanTrominoes
