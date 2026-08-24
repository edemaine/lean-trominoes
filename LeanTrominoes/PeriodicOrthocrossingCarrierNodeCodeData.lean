/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingPlanarTerminals

/-! # Reversible numeric codes for carrier nodes -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Proof-free fields of one indexed drawing segment. -/
structure IndexedGridSegmentCode where
  routeIndex : Nat
  segmentIndex : Nat
  start : Cell
  finish : Cell
  deriving DecidableEq, Repr

def indexedGridSegmentCode
    (indexed : IndexedGridSegment) : IndexedGridSegmentCode where
  routeIndex := indexed.routeIndex
  segmentIndex := indexed.segmentIndex
  start := indexed.segment.start
  finish := indexed.segment.finish

def IndexedGridSegmentCode.indexed
    (code : IndexedGridSegmentCode) : IndexedGridSegment where
  routeIndex := code.routeIndex
  segmentIndex := code.segmentIndex
  segment := ⟨code.start, code.finish⟩

/-- Proof-free fields of one physical crossing record. -/
structure CrossingRecordCode where
  first : IndexedGridSegmentCode
  firstTranslate : Cell
  second : IndexedGridSegmentCode
  secondTranslate : Cell
  point : Cell
  deriving DecidableEq, Repr

def CrossingRecord.code
    (record : CrossingRecord) : CrossingRecordCode where
  first := indexedGridSegmentCode record.first
  firstTranslate := record.firstTranslate
  second := indexedGridSegmentCode record.second
  secondTranslate := record.secondTranslate
  point := record.point

def CrossingRecordCode.record
    (code : CrossingRecordCode) : CrossingRecord where
  first := code.first.indexed
  firstTranslate := code.firstTranslate
  second := code.second.indexed
  secondTranslate := code.secondTranslate
  point := code.point

/-- Proof-free identity of one terminal node. -/
structure SegmentTerminalCode where
  indexed : IndexedGridSegmentCode
  translate : Cell
  endpoint : SegmentEnd
  deriving DecidableEq, Repr

def SegmentTerminal.code
    (terminal : SegmentTerminal) : SegmentTerminalCode where
  indexed := indexedGridSegmentCode terminal.indexed
  translate := terminal.translate
  endpoint := terminal.endpoint

def SegmentTerminalCode.terminal
    (code : SegmentTerminalCode) : SegmentTerminal where
  indexed := code.indexed.indexed
  translate := code.translate
  endpoint := code.endpoint

/-- Proof-free identity of one crossing-boundary node. -/
structure CrossingBoundaryCode where
  crossing : CrossingRecordCode
  side : CrossingSide
  deriving DecidableEq, Repr

def CrossingBoundary.code
    (boundary : CrossingBoundary) : CrossingBoundaryCode where
  crossing := boundary.crossing.code
  side := boundary.side

def CrossingBoundaryCode.boundary
    (code : CrossingBoundaryCode) : CrossingBoundary where
  crossing := code.crossing.record
  side := code.side

/-- Reversible proof-free identity of either kind of carrier node. -/
inductive CarrierNodeCode
  | boundary (boundary : CrossingBoundaryCode)
  | terminal (terminal : SegmentTerminalCode)
  deriving DecidableEq, Repr

def CarrierNode.code : CarrierNode → CarrierNodeCode
  | CarrierNode.boundary boundaryValue =>
      CarrierNodeCode.boundary boundaryValue.code
  | CarrierNode.terminal terminalValue =>
      CarrierNodeCode.terminal terminalValue.code

def CarrierNodeCode.node : CarrierNodeCode → CarrierNode
  | CarrierNodeCode.boundary boundaryValue =>
      CarrierNode.boundary boundaryValue.boundary
  | CarrierNodeCode.terminal terminalValue =>
      CarrierNode.terminal terminalValue.terminal

end LeanTrominoes.PeriodicOrthocrossing
