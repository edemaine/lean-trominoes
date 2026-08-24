/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierRepresentativeKeyData

/-! # Candidate stream for retained carrier keys -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- The physical carrier key named by a neighboring segment occurrence. -/
def occurrenceCarrierKey
    (occurrence : IndexedGridSegment × Cell) : Nat × Nat × Cell :=
  PeriodicGridDrawing.SegmentOccurrenceKey occurrence.1 occurrence.2

/-- The two terminal nodes contribute two adjacent copies of every
neighboring occurrence key. -/
def retainedTerminalCarrierKeys
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List (Nat × Nat × Cell) :=
  (neighborOccurrences graph).flatMap fun occurrence =>
    [occurrenceCarrierKey occurrence, occurrenceCarrierKey occurrence]

/-- Carrier keys contributed by the retained crossing-boundary window. -/
def retainedCrossingCarrierKeys
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List (Nat × Nat × Cell) :=
  (retainedCrossingBoundaries graph).map CrossingBoundary.carrierKey

/-- Exact pre-deduplication key stream of the retained carrier nodes. -/
def retainedCarrierKeyCandidates
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List (Nat × Nat × Cell) :=
  retainedTerminalCarrierKeys graph ++ retainedCrossingCarrierKeys graph

end LeanTrominoes.PeriodicOrthocrossing
