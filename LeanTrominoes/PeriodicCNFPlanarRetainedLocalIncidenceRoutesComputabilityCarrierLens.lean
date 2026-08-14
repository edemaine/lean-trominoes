/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedLocalIncidenceRoutesComputabilityCarrierPlacedLens

/-! # Primitive-recursive retained carrier-lens metadata and routes -/

noncomputable section

namespace LeanTrominoes

open PlanarThreeSAT

set_option maxHeartbeats 1000000

namespace PeriodicOrthocrossing

def carrierLensRouteData
    {Vertex : Type*} [DecidableEq Vertex]
    (input : CarrierLensRouteInput Vertex) :
    PlacedHorizontalLensRouteInput := by
  let origin := input.1.1.2.first.position input.1.1.1
  let finish := input.1.1.2.second.position input.1.1.1
  exact ((origin, finish),
    ((AxisDirection.axisSpan origin finish, input.1.2), input.2))

def carrierLensRoute
    {Vertex : Type*} [DecidableEq Vertex]
    (input : CarrierLensRouteInput Vertex) : List Cell :=
  placedHorizontalLensRoute (carrierLensRouteData input)

theorem carrierLensRouteData_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (carrierLensRouteData (Vertex := Vertex)) := by
  have firstNode : Primrec fun input :
      ((PeriodicGraph Vertex × EqualityLink CarrierNode) × Nat) × Nat =>
      input.1.1.2.first :=
    EqualityLink.first_primrec.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have secondNode : Primrec fun input :
      ((PeriodicGraph Vertex × EqualityLink CarrierNode) × Nat) × Nat =>
      input.1.1.2.second :=
    EqualityLink.second_primrec.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have graph : Primrec fun input :
      ((PeriodicGraph Vertex × EqualityLink CarrierNode) × Nat) × Nat =>
      input.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have firstPosition : Primrec fun input :
      ((PeriodicGraph Vertex × EqualityLink CarrierNode) × Nat) × Nat =>
      input.1.1.2.first.position input.1.1.1 :=
    CarrierNode.position_primrec.comp graph firstNode
  have secondPosition : Primrec fun input :
      ((PeriodicGraph Vertex × EqualityLink CarrierNode) × Nat) × Nat =>
      input.1.1.2.second.position input.1.1.1 :=
    CarrierNode.position_primrec.comp graph secondNode
  have span : Primrec fun input :
      ((PeriodicGraph Vertex × EqualityLink CarrierNode) × Nat) × Nat =>
      AxisDirection.axisSpan
        (input.1.1.2.first.position input.1.1.1)
        (input.1.1.2.second.position input.1.1.1) :=
    AxisDirection.axisSpan_primrec.comp firstPosition secondPosition
  have endpoints : Primrec fun input :
      CarrierLensRouteInput Vertex =>
      (input.1.1.2.first.position input.1.1.1,
        input.1.1.2.second.position input.1.1.1) :=
    Primrec.pair firstPosition secondPosition
  have routeQuery : Primrec fun input :
      CarrierLensRouteInput Vertex =>
      ((AxisDirection.axisSpan
          (input.1.1.2.first.position input.1.1.1)
          (input.1.1.2.second.position input.1.1.1), input.1.2),
        input.2) :=
    Primrec.pair
      (Primrec.pair span (Primrec.snd.comp Primrec.fst))
      Primrec.snd
  exact (Primrec.pair endpoints routeQuery).of_eq fun _ => rfl

theorem carrierLensRoute_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (carrierLensRoute (Vertex := Vertex)) :=
  placedHorizontalLensRoute_primrec.comp carrierLensRouteData_primrec

abbrev CarrierRouteInput (Variable : Type*) :=
  ((PeriodicCNF Variable × EqualityLink CarrierNode) × Nat) × Nat



end PeriodicOrthocrossing
end LeanTrominoes
