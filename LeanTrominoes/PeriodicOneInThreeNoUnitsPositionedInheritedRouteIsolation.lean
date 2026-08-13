/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionScaling
import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedInheritedRouteSplicing

/-!
# Endpoint isolation for transformed unit-elimination source routes

The unit-elimination adapter first refines an inherited source route by six
and changes its clause-anchor gauge.  Positive scaling and translation
preserve both endpoint-isolation certificates, even if the source route has
unrelated internal loops.  The later head-replacement layer can therefore
focus solely on its new local connector.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeNoUnitsPositioned

/-- Refinement and anchor-gauge translation preserve isolation of both
endpoints of an inherited source route. -/
theorem inheritedSourceRoute_endpointIsolation
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeNoUnitVariable Variable))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable))
    (sourceRoute : List Cell)
    (sourceIsolation :
      AxisDirection.HeadNotInTail
          (AxisDirection.unitSubdividePolyline sourceRoute) ∧
        AxisDirection.LastNotInDropLast
          (AxisDirection.unitSubdividePolyline sourceRoute))
    (sourceOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline sourceRoute) :
    AxisDirection.HeadNotInTail
        (AxisDirection.unitSubdividePolyline
          (inheritedSourceRoute
            outputPlacement sourcePlacement sourceClause generatedClause
            sourceRoute)) ∧
      AxisDirection.LastNotInDropLast
        (AxisDirection.unitSubdividePolyline
          (inheritedSourceRoute
            outputPlacement sourcePlacement sourceClause generatedClause
            sourceRoute)) := by
  have scaledHead :=
    sourceIsolation.1.unitSubdividePolyline_scalePolyline
      (factor := 6) (by decide) sourceOrthogonal
  have scaledLast :=
    sourceIsolation.2.unitSubdividePolyline_scalePolyline
      (factor := 6) (by decide) sourceOrthogonal
  have translatedHead :=
    scaledHead.unitSubdividePolyline_map_add
      (inheritedSourceRouteShift
        outputPlacement sourcePlacement sourceClause generatedClause)
  have translatedLast :=
    scaledLast.unitSubdividePolyline_map_add
      (inheritedSourceRouteShift
        outputPlacement sourcePlacement sourceClause generatedClause)
  simpa [inheritedSourceRoute,
    PeriodicOrthocrossing.translatePolyline, gadgetScale] using
    ⟨translatedHead, translatedLast⟩

end PeriodicOneInThreeNoUnitsPositioned
end LeanTrominoes
