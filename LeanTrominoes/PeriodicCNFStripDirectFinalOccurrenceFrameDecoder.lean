/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.FiniteIndexSlotUnaryDecoderCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceSlotCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderClauseFrameData
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableRibbonFanDataCode

/-! # Finite mixed-radix decoder for final occurrence frames -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction
namespace DirectFinalOccurrenceFrame

open Computability Turing
open PeriodicPlanarOneInThreeToThreeDM

abbrev VariableFan := VariableRibbonFanData
abbrev ClauseFrame := HorizontalRoutedRouteHeaderClauseFrame.Data

private noncomputable def defaultVariableFan : VariableFan :=
  variableRibbonFanDataOfCode default

noncomputable instance : Inhabited VariableFan :=
  ⟨defaultVariableFan⟩

/-- Explicit mixed-radix index of a variable fan and clause frame. -/
abbrev RoleIndex :=
  Fin (Fintype.card VariableFan * Fintype.card ClauseFrame)

instance roleCountNeZero :
    NeZero (Fintype.card VariableFan * Fintype.card ClauseFrame) := by
  have fanPos : 0 < Fintype.card VariableFan := Fintype.card_pos
  have clausePos : 0 < Fintype.card ClauseFrame := Fintype.card_pos
  exact ⟨Nat.ne_of_gt (Nat.mul_pos fanPos clausePos)⟩

abbrev EncodedPair :=
  FiniteIndexSlotUnaryDecoder.Pair
    (Fintype.card VariableFan * Fintype.card ClauseFrame)

/-- All finite endpoint data aligned with one routed final occurrence. -/
structure Data where
  variableFan : VariableFan
  occurrenceSlot : PeriodicOneInThreeToThreeDM.OccurrenceSlot
  clauseFrame : ClauseFrame
  deriving DecidableEq, Fintype

noncomputable instance : Inhabited Data :=
  ⟨⟨default, .first, default⟩⟩

def variableFanBase (fan : VariableFan) : Nat :=
  8 * Fintype.card ClauseFrame * (Fintype.equivFin VariableFan fan).val

def clauseFrameBase (frame : ClauseFrame) : Nat :=
  8 * (Fintype.equivFin ClauseFrame frame).val

def occurrenceSlotValue
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot) : Nat :=
  slot.index

/-- Explicit mixed-radix index of a semantic variable/clause pair. -/
def roleIndex (fan : VariableFan) (frame : ClauseFrame) : RoleIndex :=
  FiniteIndexSlotUnaryDecoder.pairIndex
    (Fintype.equivFin VariableFan fan,
      Fintype.equivFin ClauseFrame frame)

def boundedSlot
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot) : Fin 8 :=
  ⟨slot.index, by cases slot <;> decide⟩

def codeOfData (frame : Data) : Nat :=
  variableFanBase frame.variableFan +
    clauseFrameBase frame.clauseFrame +
      occurrenceSlotValue frame.occurrenceSlot

def decodedRolePair (pair : EncodedPair) :
    Fin (Fintype.card VariableFan) × Fin (Fintype.card ClauseFrame) :=
  FiniteIndexSlotUnaryDecoder.unpairIndex pair.1

def dataOfPair (pair : EncodedPair) : Data where
  variableFan := (Fintype.equivFin VariableFan).symm
    (decodedRolePair pair).1
  occurrenceSlot :=
    BoundedOccurrenceSlots.boundedOccurrenceSlot pair.2.val
  clauseFrame := (Fintype.equivFin ClauseFrame).symm
    (decodedRolePair pair).2

def data (pairs : List EncodedPair) : List Data :=
  pairs.flatMap fun pair => [dataOfPair pair]

@[simp] theorem data_length (pairs : List EncodedPair) :
    (data pairs).length = pairs.length := by
  simp [data]

noncomputable def dataComputableInPolyTime :
    TM2ComputableInPolyTime id id data :=
  FiniteBlockTransducer.computableInPolyTime fun pair => [dataOfPair pair]

end DirectFinalOccurrenceFrame
end LeanTrominoes.PeriodicCNFStripReduction

end
