/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeCodeData

/-! # Exact semantics of reversible carrier-node codes -/

namespace LeanTrominoes.PeriodicOrthocrossing

@[simp] theorem IndexedGridSegmentCode.indexed_code
    (indexed : IndexedGridSegment) :
    (indexedGridSegmentCode indexed).indexed = indexed := by
  cases indexed
  rfl

@[simp] theorem CrossingRecordCode.record_code
    (record : CrossingRecord) : record.code.record = record := by
  cases record
  simp [CrossingRecord.code, CrossingRecordCode.record]

@[simp] theorem SegmentTerminalCode.terminal_code
    (terminal : SegmentTerminal) : terminal.code.terminal = terminal := by
  cases terminal
  simp [SegmentTerminal.code, SegmentTerminalCode.terminal]

@[simp] theorem CrossingBoundaryCode.boundary_code
    (boundary : CrossingBoundary) : boundary.code.boundary = boundary := by
  cases boundary
  simp [CrossingBoundary.code, CrossingBoundaryCode.boundary]

@[simp] theorem CarrierNodeCode.node_code
    (node : CarrierNode) : node.code.node = node := by
  cases node <;> simp [CarrierNode.code, CarrierNodeCode.node]

theorem indexedGridSegmentCode_injective :
    Function.Injective indexedGridSegmentCode := by
  intro first second equal
  exact congrArg IndexedGridSegmentCode.indexed equal

theorem CrossingRecord.code_injective :
    Function.Injective CrossingRecord.code := by
  intro first second equal
  exact congrArg CrossingRecordCode.record equal

theorem CarrierNode.code_injective :
    Function.Injective CarrierNode.code := by
  intro first second equal
  simpa using congrArg CarrierNodeCode.node equal

end LeanTrominoes.PeriodicOrthocrossing
