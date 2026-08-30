/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanCarrierLensTemplateNormalizedDirections
import LeanTrominoes.RetainedAngularFanFallbackSourcePrefixDirectionData

/-! # Source-prefix words of canonical carrier-lens templates -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT

/-- Deleting the old endpoint of a canonical horizontal or vertical carrier
route exposes the explicit compiler prefix word. -/
theorem carrierLensTemplateRoute_prefixDirections_eq
    (geometry : CarrierFallbackRouteTailRecords.Geometry)
    (spanLarge : 8 ≤ geometry.span)
    (localClauseIndex literalIndex : Fin 2) :
    Gadget.unitSubdivisionDirections
        (carrierLensTemplateRoute geometry.horizontal geometry.span
          localClauseIndex literalIndex).dropLast =
      carrierLensRoutePrefixDirections geometry.horizontal geometry.span
        localClauseIndex literalIndex := by
  rcases geometry with ⟨horizontal, nextSlice, span⟩
  change 8 ≤ span at spanLarge
  have spanThree : (3 : Int) < span := by omega
  cases horizontal <;>
    fin_cases localClauseIndex <;>
    fin_cases literalIndex <;>
    simp [carrierLensTemplateRoute, horizontalEqualityLensRoutes,
      horizontalEqualityLensUpperLeftRoute,
      horizontalEqualityLensUpperRightRoute,
      horizontalEqualityLensLowerLeftRoute,
      horizontalEqualityLensLowerRightRoute,
      carrierLensRoutePrefixDirections,
      Gadget.unitSubdivisionDirections,
      AxisDirection.segmentLength, Int.natAbs_neg,
      AxisDirection.orientPoint, AxisDirection.between,
      spanThree]
  all_goals omega

/-- After the two fixed source refinements, the canonical carrier template
has the exact 1152-fold fallback prefix word. -/
theorem carrierLensTemplateFallbackSourcePrefix_directions_eq
    (geometry : CarrierFallbackRouteTailRecords.Geometry)
    (spanLarge : 8 ≤ geometry.span)
    (localClauseIndex literalIndex : Fin 2) :
    Gadget.unitSubdivisionDirections
        (retainedFallbackSourcePrefix
          (scalePolyline retainedAngularFanSourceClearanceFactor
            (carrierLensTemplateRoute geometry.horizontal geometry.span
              localClauseIndex literalIndex))) =
      Gadget.repeatDirections 1152
        (carrierLensRoutePrefixDirections
          geometry.horizontal geometry.span
          localClauseIndex literalIndex) := by
  rw [retainedFallbackSourcePrefix_sourceClearanceScaled_directions,
    carrierLensTemplateRoute_prefixDirections_eq
      geometry spanLarge localClauseIndex literalIndex]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
