/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierLinks

/-! # Per-key retained representative carrier blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- Carrier keys of the finite neighboring segment-occurrence window. -/
def neighboringCarrierKeys
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List (Nat × Nat × Cell) :=
  (neighborOccurrences graph).map fun occurrence =>
    PeriodicGridDrawing.SegmentOccurrenceKey
      occurrence.1 occurrence.2

/-- Selected representative links on one fixed physical carrier key. -/
def retainedRepresentativeCarrierLinksAt
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (key : Nat × Nat × Cell) :
    List (EqualityLink CarrierNode) :=
  (retainedCompleteCarrierLinks graph key).filter
    (CarrierLinkIsRepresentative graph)

/-- Retained key order restricted to the neighboring occurrence window. -/
def retainedNeighboringCarrierKeys
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List (Nat × Nat × Cell) :=
  (retainedDrawingCompleteCarrierKeys graph).filter fun key =>
    key ∈ neighboringCarrierKeys graph

/-- Selected carrier links assembled only from neighboring occurrence keys. -/
def retainedNeighboringCarrierLinks
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (EqualityLink CarrierNode) :=
  (retainedNeighboringCarrierKeys graph).flatMap
    (retainedRepresentativeCarrierLinksAt graph)

end LeanTrominoes.PeriodicOrthocrossing
