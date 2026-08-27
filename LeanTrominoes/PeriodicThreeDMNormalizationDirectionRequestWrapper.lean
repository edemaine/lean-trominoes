/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequests

/-! # Dynamically selected template wrappers for retained requests -/

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace NormalizationDirectionRequest
namespace Wrapper

open Gadget

def defaultFirstChoice : FirstTemplateChoice :=
  ⟨.east, .west⟩

def defaultRotationChoice : RotationTemplateChoice :=
  ⟨false, .west⟩

def defaultHeader : Header where
  firstSource := defaultFirstChoice
  firstTarget := defaultFirstChoice
  secondSource := defaultRotationChoice
  secondTarget := defaultRotationChoice
  finalSource := defaultRotationChoice
  finalTarget := defaultRotationChoice

structure Control where
  header : Header
  readingRoute : Bool
  deriving DecidableEq, Fintype

def initial : Control := ⟨defaultHeader, false⟩

def transition (round : Round) :
    Control → Token → Control × List Token
  | control, token@(.firstSource choice) =>
      if control.readingRoute then (control, [])
      else (⟨{ control.header with firstSource := choice }, false⟩, [token])
  | control, token@(.firstTarget choice) =>
      if control.readingRoute then (control, [])
      else (⟨{ control.header with firstTarget := choice }, false⟩, [token])
  | control, token@(.secondSource choice) =>
      if control.readingRoute then (control, [])
      else (⟨{ control.header with secondSource := choice }, false⟩, [token])
  | control, token@(.secondTarget choice) =>
      if control.readingRoute then (control, [])
      else (⟨{ control.header with secondTarget := choice }, false⟩, [token])
  | control, token@(.finalSource choice) =>
      if control.readingRoute then (control, [])
      else (⟨{ control.header with finalSource := choice }, false⟩, [token])
  | control, token@(.finalTarget choice) =>
      if control.readingRoute then (control, [])
      else (⟨{ control.header with finalTarget := choice }, false⟩, [token])
  | control, .separator =>
      if control.readingRoute then (control, [])
      else
        (⟨control.header, true⟩,
          .separator ::
            (routeStepDirections
              (control.header.sourceTemplate round)).map .direction)
  | control, token@(.direction _) =>
      if control.readingRoute then (control, [token]) else (control, [])

def finish (round : Round) (control : Control) : List Token :=
  if control.readingRoute then
    (routeStepDirections
      (control.header.targetTemplate round).reverse).map .direction
  else
    []

def output (round : Round) (tokens : List Token) : List Token :=
  FiniteStateTransducer.output initial (transition round)
    (finish round) tokens

/-- Mathematical wrapper stage, applied after expansion and trimming. -/
def request (round : Round) (input : Request) : Request :=
  { header := input.header
    directions :=
      routeStepDirections (input.header.sourceTemplate round) ++
        (input.directions ++
          routeStepDirections
            (input.header.targetTemplate round).reverse) }

@[simp]
theorem scan_header (round : Round) (header : Header) :
    FiniteStateTransducer.scan (transition round) initial header.tokens =
      (⟨header, false⟩, header.tokens) := by
  simp [Header.tokens, FiniteStateTransducer.scan, transition, initial,
    defaultHeader, defaultFirstChoice, defaultRotationChoice]

@[simp]
theorem scan_route (round : Round) (header : Header)
    (directions : List AxisDirection) :
    FiniteStateTransducer.scan (transition round) ⟨header, true⟩
        (directions.map .direction) =
      (⟨header, true⟩, directions.map .direction) := by
  induction directions with
  | nil => rfl
  | cons direction directions induction =>
      simp [FiniteStateTransducer.scan, transition, induction]

theorem output_request (round : Round) (input : Request) :
    output round input.tokens = (request round input).tokens := by
  unfold output FiniteStateTransducer.output Request.tokens
  rw [FiniteStateTransducer.scan_append, scan_header]
  have separatorEq :
      transition round ⟨input.header, false⟩ .separator =
        (⟨input.header, true⟩,
          .separator ::
            (routeStepDirections
              (input.header.sourceTemplate round)).map .direction) := by
    simp [transition]
  simp only [FiniteStateTransducer.scan]
  rw [separatorEq]
  rw [scan_route]
  simp [request, finish, List.map_append, List.append_assoc]

end Wrapper
end NormalizationDirectionRequest
end PeriodicThreeDM
end LeanTrominoes
