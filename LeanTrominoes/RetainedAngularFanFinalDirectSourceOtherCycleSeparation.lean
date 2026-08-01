import LeanTrominoes.RetainedAngularFanFinalFallbackCycleSeparation
import LeanTrominoes.RetainedAngularFanFinalDirectSourceOwnCycleSeparation
import LeanTrominoes.RetainedFinalSourceRouteOtherVertexFinalSegmentSeparation

/-!
# Final direct occurrences avoid cycles at other source centers

The direct-source atlas replaces a two-point source incidence by a
coordinated outer fan.  A finite certificate bounds every such replacement
inside the radius-288 expansion of the fully refined source segment.  This
lets the retained source drawing's vertex/segment separation clear every
cycle centered at a different source atom.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- Every finite direct-source atlas route stays within the radius-288
expansion of its fully refined two-point local source segment. -/
theorem
    retainedDirectSourceFanCompleteRouteAt_point_in_scaledLocalSegmentRectangle :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length)
      (slot : RetainedTerminalSlot)
      (point : Cell),
      point ∈ retainedDirectSourceFanCompleteRouteAt kind index slot →
        let localSegment : GridSegment :=
          ⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
            (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩
        InClosedGridRectangle
          (coordinateRadiusLower 288
            (Cell.scale
              (retainedTerminalFanTotalRefinement * 4)
              localSegment.coordinateLower))
          (coordinateRadiusUpper 288
            (Cell.scale
              (retainedTerminalFanTotalRefinement * 4)
              localSegment.coordinateUpper))
          point := by
  native_decide

end PeriodicEightOccurrenceSplit
end LeanTrominoes
