/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedLocalIncidenceRoutesComputabilityRoutesCore

/-! # Primitive-recursive retained carrier and translated-corner routes -/

noncomputable section

namespace LeanTrominoes

open PlanarThreeSAT

set_option maxHeartbeats 1000000

namespace PeriodicOrthocrossing

abbrev CarrierLensRouteInput (Vertex : Type*) :=
  ((PeriodicGraph Vertex × EqualityLink CarrierNode) × Nat) × Nat

abbrev PlacedHorizontalLensRouteInput :=
  (Cell × Cell) × ((Int × Nat) × Nat)

def placedHorizontalLensRoute
    (input : PlacedHorizontalLensRouteInput) : List Cell :=
  (horizontalEqualityLensRoutes input.2.1.1
    input.2.1.2 input.2.2).map
      ((AxisDirection.between input.1.1 input.1.2).placePoint
        input.1.1)

set_option maxHeartbeats 4000000 in
theorem placedHorizontalLensRoute_primrec :
    Primrec placedHorizontalLensRoute := by
  change Primrec fun input : PlacedHorizontalLensRouteInput =>
    (horizontalEqualityLensRoutes input.2.1.1
      input.2.1.2 input.2.2).map
        ((AxisDirection.between input.1.1 input.1.2).placePoint
          input.1.1)
  have transform : Primrec fun input :
      PlacedHorizontalLensRouteInput × Cell =>
      (AxisDirection.between input.1.1.1
        input.1.1.2).placePoint input.1.1.1 input.2 := by
    have origin : Primrec fun input :
        PlacedHorizontalLensRouteInput × Cell =>
        input.1.1.1 :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have finish : Primrec fun input :
        PlacedHorizontalLensRouteInput × Cell =>
        input.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have direction : Primrec fun input :
        PlacedHorizontalLensRouteInput × Cell =>
        AxisDirection.between input.1.1.1 input.1.1.2 :=
      AxisDirection.between_primrec.comp origin finish
    exact AxisDirection.placePoint_primrec.comp
      (Primrec.pair (Primrec.pair origin direction) Primrec.snd)
  exact Primrec.list_map
    (PlanarThreeSAT.horizontalEqualityLensRoutes_primrec.comp Primrec.snd)
    transform.to₂


end PeriodicOrthocrossing
end LeanTrominoes
