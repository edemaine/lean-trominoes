/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceDirectionRequestData

/-! # Compiler for complete horizontal occurrence direction requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalOccurrenceDirectionRequest

open Computability Turing
open PeriodicPlanarOneInThreeToThreeDM

local instance : Inhabited AxisDirection := ⟨.invalid⟩

/-- Finite control remembers the selected lane and preceding source
direction while scanning the dynamic corridor word. -/
structure State where
  lane : Gadget.WireColor
  previous : Option AxisDirection
  deriving DecidableEq, Fintype

instance : Inhabited State := ⟨⟨.red, none⟩⟩

def initial : State := ⟨.red, none⟩

def transition (state : State) : Token → State × List AxisDirection
  | .finite query =>
      (state, HorizontalFiniteIncidenceDirectionQuery.directions query)
  | .lane color => (⟨color, none⟩, [])
  | .direction current =>
      (⟨state.lane, some current⟩,
        match state.previous with
        | none => []
        | some incoming =>
            ribbonMacrocellDirectionBlock incoming current state.lane)

def finish (_ : State) : List AxisDirection := []

def output (input : List Token) : List AxisDirection :=
  FiniteStateTransducer.output initial transition finish input

/-- A finite query at the start of a request emits its fixed word and leaves
the corridor control unchanged. -/
@[simp] theorem output_finite_cons
    (query : HorizontalFiniteIncidenceDirectionQuery)
    (input : List Token) :
    output (.finite query :: input) =
      HorizontalFiniteIncidenceDirectionQuery.directions query ++
        output input := by
  unfold output FiniteStateTransducer.output
  simp only [FiniteStateTransducer.scan, transition]
  rw [List.append_assoc]

private theorem scan_some_eq
    (lane : Gadget.WireColor)
    (previous : AxisDirection)
    (directions : List AxisDirection) :
    (FiniteStateTransducer.scan transition ⟨lane, some previous⟩
      (directions.map Token.direction)).2 =
      ribbonCorridorDirectionWord lane (previous :: directions) := by
  induction directions generalizing previous with
  | nil =>
      simp [FiniteStateTransducer.scan, ribbonCorridorDirectionWord]
  | cons current directions induction =>
      simp only [List.map_cons, FiniteStateTransducer.scan, transition]
      rw [induction current]
      rw [ribbonCorridorDirectionWord]

private theorem scan_none_eq
    (lane : Gadget.WireColor)
    (directions : List AxisDirection) :
    (FiniteStateTransducer.scan transition ⟨lane, none⟩
      (directions.map Token.direction)).2 =
      ribbonCorridorDirectionWord lane directions := by
  cases directions with
  | nil =>
      simp [FiniteStateTransducer.scan, ribbonCorridorDirectionWord]
  | cons first rest =>
      simp only [List.map_cons, FiniteStateTransducer.scan, transition]
      rw [scan_some_eq lane first rest]
      simp only [List.nil_append]

/-- The compact request emits its leading finite stub, complete dynamic
corridor, and trailing finite stub in that order. -/
@[simp] theorem output_tokens
    (leading : HorizontalFiniteIncidenceDirectionQuery)
    (lane : Gadget.WireColor)
    (source : List AxisDirection)
    (trailing : HorizontalFiniteIncidenceDirectionQuery) :
    output (tokens leading lane source trailing) =
      requestedOutput leading lane source trailing := by
  unfold output tokens requestedOutput FiniteStateTransducer.output
  rw [FiniteStateTransducer.scan_append]
  simp only [FiniteStateTransducer.scan, transition]
  rw [FiniteStateTransducer.scan_append]
  simp only [FiniteStateTransducer.scan, transition, finish,
    List.append_nil]
  rw [scan_none_eq lane source]

/-- One fixed finite-state transducer compiles arbitrary compact occurrence
requests in linear time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id output :=
  FiniteStateTransducer.computableInPolyTime initial transition finish

end HorizontalOccurrenceDirectionRequest
end PeriodicCNFStripReduction
end LeanTrominoes

end
