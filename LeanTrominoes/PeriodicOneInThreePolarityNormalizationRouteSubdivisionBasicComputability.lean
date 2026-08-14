/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision
import LeanTrominoes.PeriodicThreeDMNormalizationGeometryComputability

/-!
# Basic computability for routed polarity normalization

This module certifies the proof-free geometric operations that refine one
source incidence route and select the two new subdivision vertices.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- Uniform scaling of a finite polyline is primitive recursive. -/
theorem scalePolyline_primrec : Primrec₂ scalePolyline := by
  change Primrec fun input : Int × List Cell =>
    scalePolyline input.1 input.2
  exact (Primrec.list_map Primrec.snd
    (Computability.cell_scale_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq
        fun _ => rfl

/-- Refinement and unit subdivision preserve primitive recursiveness of a
source route query. -/
theorem refinedRoute_primrec
    {Input : Type*} [Primcodable Input]
    (routes : Input → Nat → Nat → List Cell)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec fun input : (Input × Nat) × Nat =>
      refinedRoute (routes input.1.1) input.1.2 input.2 := by
  have scaled : Primrec fun input : (Input × Nat) × Nat =>
      scalePolyline refinementFactor
        (routes input.1.1 input.1.2 input.2) :=
    scalePolyline_primrec.comp
      (Primrec.const (refinementFactor : Int)) routesPrimrec
  exact
    PeriodicThreeDM.NormalizationCompiler.unitSubdividePolyline_primrec.comp
      scaled

/-- Selecting either inserted vertex from a refined route is primitive
recursive whenever the underlying route lookup is. -/
theorem routePoint_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (routes : Input → Nat → Nat → List Cell)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec fun input : (Input × FreshOccurrence Variable) × Nat =>
      routePoint (routes input.1.1) input.1.2 input.2 := by
  have refined : Primrec fun input :
      (Input × FreshOccurrence Variable) × Nat =>
      refinedRoute (routes input.1.1)
        input.1.2.1.1 input.1.2.1.2 :=
    (refinedRoute_primrec routes routesPrimrec).comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst)
          (Primrec.fst.comp
            (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))
        (Primrec.snd.comp
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))
  exact (Primrec.list_getD ((0, 0) : Cell)).comp refined Primrec.snd

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
