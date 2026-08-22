/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendNextSliceSemantics

/-! # Translation invariance of canonical retained-bend descriptors -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PlanarThreeSAT
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- Changing a bend occurrence's common route translation does not change
its ordered-port descriptor sequence. -/
theorem routeBendsAux_descriptorBlocks_translate
    (routeIndex incomingSegmentIndex : Nat)
    (firstTranslate secondTranslate : Cell) :
    ∀ points : List Cell,
      (routeBendsAux routeIndex firstTranslate
          incomingSegmentIndex points).flatMap
          (fun routeBend =>
            canonicalBendDescriptorBlock
              routeBend.incomingPort routeBend.outgoingPort false) =
        (routeBendsAux routeIndex secondTranslate
          incomingSegmentIndex points).flatMap
          (fun routeBend =>
            canonicalBendDescriptorBlock
              routeBend.incomingPort routeBend.outgoingPort false) := by
  intro points
  induction points generalizing incomingSegmentIndex with
  | nil => rfl
  | cons first rest induction =>
      cases rest with
      | nil => rfl
      | cons second rest =>
          cases rest with
          | nil => rfl
          | cons third rest =>
              simp only [routeBendsAux, List.flatMap_cons]
              rw [induction]
              rfl

/-- Public route-level translation invariance of ordered-port descriptors. -/
theorem routeBends_descriptorBlocks_translate
    (routeIndex : Nat) (firstTranslate secondTranslate : Cell)
    (route : List Cell) :
    (routeBends routeIndex firstTranslate route).flatMap
        (fun routeBend =>
          canonicalBendDescriptorBlock
            routeBend.incomingPort routeBend.outgoingPort false) =
      (routeBends routeIndex secondTranslate route).flatMap
        (fun routeBend =>
          canonicalBendDescriptorBlock
            routeBend.incomingPort routeBend.outgoingPort false) := by
  exact routeBendsAux_descriptorBlocks_translate
    routeIndex 0 firstTranslate secondTranslate route

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
