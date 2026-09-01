/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteRoleSlotUnaryDecoderData
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderOccurrenceData
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonVariableFanFinite

/-! # Assembly of finite variable-fan records from occurrence triples -/

noncomputable section

namespace LeanTrominoes.FinalFanDataTripleAssembler

open Computability Turing
open PeriodicCNFStripReduction
open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

abbrev OccurrenceData := HorizontalRoutedRouteHeader.OccurrenceData
abbrev Pair := FiniteRoleSlotUnaryDecoder.Pair OccurrenceData
abbrev FanData := VariableRibbonFanData

/-- Embed a fan count predecessor into the generic decoder's eight slots. -/
def slotOfCountPred (countPred : Fin 3) :
    FiniteRoleSlotUnaryDecoder.Slot :=
  ⟨countPred.val, by omega⟩

/-- Total recovery of a fan count predecessor from a generic decoder slot.
Malformed slots outside zero through two use the harmless zero fallback. -/
def countPredOfSlot (slot : FiniteRoleSlotUnaryDecoder.Slot) : Fin 3 :=
  if bounded : slot.val < 3 then ⟨slot.val, bounded⟩ else 0

@[simp] theorem countPredOfSlot_slotOfCountPred (countPred : Fin 3) :
    countPredOfSlot (slotOfCountPred countPred) = countPred := by
  unfold countPredOfSlot slotOfCountPred
  simp only [countPred.isLt, ↓reduceDIte]

/-- Assemble one complete fan from its count and selected first, second, and
third occurrence records. -/
def fanData (countPred : Fin 3)
    (first second third : OccurrenceData) : FanData where
  countPred := countPred
  kind
    | .first => first.kind
    | .second => second.kind
    | .third => third.kind
  polarity
    | .first => first.polarity
    | .second => second.polarity
    | .third => third.polarity
  direction
    | .first => first.direction
    | .second => second.direction
    | .third => third.direction

instance : Inhabited FanData :=
  ⟨fanData 0 default default default⟩

@[simp] theorem fanData_countPred (countPred : Fin 3)
    (first second third : OccurrenceData) :
    (fanData countPred first second third).countPred = countPred :=
  rfl

@[simp] theorem fanData_kind_first (countPred : Fin 3)
    (first second third : OccurrenceData) :
    (fanData countPred first second third).kind .first = first.kind :=
  rfl

@[simp] theorem fanData_kind_second (countPred : Fin 3)
    (first second third : OccurrenceData) :
    (fanData countPred first second third).kind .second = second.kind :=
  rfl

@[simp] theorem fanData_kind_third (countPred : Fin 3)
    (first second third : OccurrenceData) :
    (fanData countPred first second third).kind .third = third.kind :=
  rfl

@[simp] theorem fanData_polarity_first (countPred : Fin 3)
    (first second third : OccurrenceData) :
    (fanData countPred first second third).polarity .first = first.polarity :=
  rfl

@[simp] theorem fanData_polarity_second (countPred : Fin 3)
    (first second third : OccurrenceData) :
    (fanData countPred first second third).polarity .second = second.polarity :=
  rfl

@[simp] theorem fanData_polarity_third (countPred : Fin 3)
    (first second third : OccurrenceData) :
    (fanData countPred first second third).polarity .third = third.polarity :=
  rfl

@[simp] theorem fanData_direction_first (countPred : Fin 3)
    (first second third : OccurrenceData) :
    (fanData countPred first second third).direction .first = first.direction :=
  rfl

@[simp] theorem fanData_direction_second (countPred : Fin 3)
    (first second third : OccurrenceData) :
    (fanData countPred first second third).direction .second = second.direction :=
  rfl

@[simp] theorem fanData_direction_third (countPred : Fin 3)
    (first second third : OccurrenceData) :
    (fanData countPred first second third).direction .third = third.direction :=
  rfl

inductive State
  | empty
  | first (countPred : Fin 3) (first : OccurrenceData)
  | second (countPred : Fin 3)
      (first second : OccurrenceData)
  deriving DecidableEq, Fintype, Inhabited

def transition : State → Pair → State × List FanData
  | .empty, pair =>
      (.first (countPredOfSlot pair.2) pair.1, [])
  | .first countPred first, pair =>
      (.second countPred first pair.1, [])
  | .second countPred first second, pair =>
      (.empty, [fanData countPred first second pair.1])

def finish (_ : State) : List FanData := []

/-- Declarative consecutive-triple grouping, ignoring an incomplete suffix. -/
def grouped : List Pair → List FanData
  | first :: second :: third :: remaining =>
      fanData (countPredOfSlot first.2)
        first.1 second.1 third.1 :: grouped remaining
  | _ => []

/-- State left by an incomplete final group. -/
def finalState : List Pair → State
  | [] => .empty
  | [first] => .first (countPredOfSlot first.2) first.1
  | [first, second] =>
      .second (countPredOfSlot first.2) first.1 second.1
  | _ :: _ :: _ :: remaining => finalState remaining

theorem scan_empty : (pairs : List Pair) →
    FiniteStateTransducer.scan transition .empty pairs =
      (finalState pairs, grouped pairs)
  | [] => rfl
  | [first] => rfl
  | [first, second] => rfl
  | first :: second :: third :: remaining => by
      simp only [FiniteStateTransducer.scan, transition,
        List.nil_append, List.singleton_append]
      rw [scan_empty remaining]
      rfl
termination_by pairs => pairs.length

def output (pairs : List Pair) : List FanData :=
  FiniteStateTransducer.output .empty transition finish pairs

@[simp] theorem output_eq_grouped (pairs : List Pair) :
    output pairs = grouped pairs := by
  simp [output, FiniteStateTransducer.output, scan_empty, finish]

/-- Consecutive finite occurrence triples assemble into finite fan records in
linear time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id output := by
  unfold output
  exact FiniteStateTransducer.computableInPolyTime
    .empty transition finish

end LeanTrominoes.FinalFanDataTripleAssembler

end
