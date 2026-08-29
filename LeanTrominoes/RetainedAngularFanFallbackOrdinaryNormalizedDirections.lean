/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteNormalizedJoinDirection
import LeanTrominoes.RetainedAngularFanFallbackExteriorRadialJoinNodup
import LeanTrominoes.RetainedAngularFanFallbackOrdinaryTerminalTailDecomposition
import LeanTrominoes.RetainedAngularFanFinalOuterSpokeSeparation

/-! # Normalized direction semantics of ordinary fallback suffixes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
open FallbackSuffixDirectionCompiler
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- The exterior radial prefix and the normalized fixed terminal tail meet
only at the point one primitive outside the selected lane port. -/
theorem retainedTerminalFanOuterRadialPrefix_normalizedTerminalTail_only_common
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (radialPositive :
      0 < retainedTerminalFanOuterRadialLength terminal) :
    ∀ point,
      point ∈ AxisDirection.unitSubdividePolyline
        (retainedTerminalFanOuterRadialPrefix center terminal slot) →
      point ∈ AxisDirection.unitSubdividePolyline
        (AxisDirection.normalizeOrthogonalPolyline
          (retainedFallbackFanTerminalTailRouteAt
            center terminal.1 slot)) →
      point =
        Cell.add center
          (Cell.add
            (retainedTerminalFanOuterLanePortOffset terminal.1 slot)
            terminal.1.primitive) := by
  let radialPrefix := retainedTerminalFanOuterRadialPrefix
    center terminal slot
  let finalStub := retainedTerminalFanOuterRadialFinalStubAt
    center terminal.1 slot
  let finiteTail := retainedFallbackFanFiniteTailRouteAt
    center terminal.1 slot
  let terminalTail := retainedFallbackFanTerminalTailRouteAt
    center terminal.1 slot
  let normalizedTail := AxisDirection.normalizeOrthogonalPolyline
    terminalTail
  let radialBoundary := Cell.add center
    (Cell.add
      (retainedTerminalFanOuterLanePortOffset terminal.1 slot)
      terminal.1.primitive)
  let lanePort := retainedTerminalFanOuterLanePort
    center terminal.1 slot
  have terminalTailNonempty : terminalTail ≠ [] :=
    retainedFallbackFanTerminalTailRouteAt_ne_nil
      center terminal.1 slot
  have terminalTailOrthogonal : OrthogonalPolyline terminalTail :=
    retainedFallbackFanTerminalTailRouteAt_orthogonal
      center terminal.1 slot
  have normalizedTailUnit :
      AxisDirection.unitSubdividePolyline normalizedTail =
        normalizedTail :=
    AxisDirection.unitSubdividePolyline_eq_self_of_unitSteps
      (AxisDirection.normalizeOrthogonalPolyline_unitSteps
        terminalTailNonempty terminalTailOrthogonal)
  have normalizedTailSublist :
      List.Sublist normalizedTail
        (AxisDirection.unitSubdividePolyline terminalTail) :=
    AxisDirection.normalizeOrthogonalPolyline_sublist_unitSubdividePolyline
      terminalTailNonempty terminalTailOrthogonal
  have finalStubHead : finalStub.head? = some radialBoundary :=
    retainedTerminalFanOuterRadialFinalStubAt_head?
      center terminal.1 slot
  have finalStubNonempty : finalStub ≠ [] := by
    intro empty
    rw [empty] at finalStubHead
    simp at finalStubHead
  have finalStubLast : finalStub.getLast? = some lanePort :=
    retainedTerminalFanOuterRadialFinalStubAt_getLast?
      center terminal.1 slot
  have finiteTailHead : finiteTail.head? = some lanePort :=
    retainedFallbackFanFiniteTailRouteAt_head?
      center terminal.1 slot
  have terminalTailEq :
      terminalTail = joinAtEndpoint finalStub finiteTail := by
    rfl
  have prefixFiniteStrict :
      RoutesStrictlyAvoidEachOther radialPrefix finiteTail := by
    unfold finiteTail retainedFallbackFanFiniteTailRouteAt
    exact
      (retainedTerminalFanOuterRadialPrefix_strictlyAvoid_local
        center terminal slot slot terminal.1 radialPositive).join_right
        (retainedTerminalFanOuterRadialPrefix_strictlyAvoid_figure7SpokeRouteAt
          center terminal slot slot radialPositive)
        (retainedTerminalFanOuterLocalRouteAt_getLast?
          center terminal.1 slot)
        (retainedTerminalFanFigure7SpokeRouteAt_head? center slot)
  have prefixFiniteDisjoint :
      List.Disjoint
        (AxisDirection.unitSubdividePolyline radialPrefix)
        (AxisDirection.unitSubdividePolyline finiteTail) :=
    prefixFiniteStrict.unitSubdividePolyline_disjoint
      (retainedTerminalFanOuterRadialPrefix_orthogonal
        center terminal slot)
      (retainedFallbackFanFiniteTailRouteAt_orthogonal
        center terminal.1 slot)
  intro point prefixMember normalizedMember
  have normalizedPlain : point ∈ normalizedTail := by
    rw [normalizedTailUnit] at normalizedMember
    exact normalizedMember
  have terminalTailMember :
      point ∈ AxisDirection.unitSubdividePolyline terminalTail :=
    normalizedTailSublist.subset normalizedPlain
  rw [terminalTailEq,
    AxisDirection.unitSubdividePolyline_joinAtEndpoint
      finalStubNonempty finalStubLast finiteTailHead]
    at terminalTailMember
  rcases mem_joinAtEndpoint terminalTailMember with
    finalStubMember | finiteTailMember
  · exact
      FallbackSuffixDirectionCompiler.retainedTerminalFanOuterRadialPrefix_finalStub_only_common
        center terminal slot radialPositive
        point prefixMember finalStubMember
  · exact (prefixFiniteDisjoint prefixMember finiteTailMember).elim

/-- Normalization of an ordinary fallback suffix preserves the streamed
lane-shift and exterior radial word, and confines loop erasure to the fixed
terminal-tail table. -/
theorem retainedFallbackFanOrdinarySuffixRouteAt_normalized_directions_eq
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (radialPositive :
      0 < retainedTerminalFanOuterRadialLength terminal) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (retainedFallbackFanSuffixRouteAt
            .ordinary center terminal slot)) =
      prefixDirections .ordinary terminal.1 slot ++
        radialCopies
            (retainedTerminalFanOuterRadialLength terminal - 1)
            terminal.1 ++
          retainedFallbackFanNormalizedTerminalTailDirections
            terminal.1 slot := by
  let radialPrefix := retainedTerminalFanOuterRadialPrefix
    center terminal slot
  let terminalTail := retainedFallbackFanTerminalTailRouteAt
    center terminal.1 slot
  let normalizedTail := AxisDirection.normalizeOrthogonalPolyline
    terminalTail
  let radialBoundary := Cell.add center
    (Cell.add
      (retainedTerminalFanOuterLanePortOffset terminal.1 slot)
      terminal.1.primitive)
  have radialPrefixHead := retainedTerminalFanOuterRadialPrefix_head?
    center terminal slot
  have radialPrefixNonempty : radialPrefix ≠ [] := by
    intro empty
    change radialPrefix.head? = _ at radialPrefixHead
    rw [empty] at radialPrefixHead
    simp at radialPrefixHead
  have radialPrefixOrthogonal : OrthogonalPolyline radialPrefix :=
    retainedTerminalFanOuterRadialPrefix_orthogonal
      center terminal slot
  have radialPrefixLast : radialPrefix.getLast? = some radialBoundary :=
    retainedTerminalFanOuterRadialPrefix_getLast?
      center terminal slot radialPositive
  have radialPrefixNodup :
      (AxisDirection.unitSubdividePolyline radialPrefix).Nodup :=
    FallbackSuffixDirectionCompiler.retainedTerminalFanOuterRadialPrefix_unitSubdivide_nodup
      center terminal slot
  have terminalTailNonempty : terminalTail ≠ [] :=
    retainedFallbackFanTerminalTailRouteAt_ne_nil
      center terminal.1 slot
  have terminalTailOrthogonal : OrthogonalPolyline terminalTail :=
    retainedFallbackFanTerminalTailRouteAt_orthogonal
      center terminal.1 slot
  have normalizedTailNonempty : normalizedTail ≠ [] :=
    AxisDirection.normalizeOrthogonalPolyline_ne_nil
      terminalTailNonempty terminalTailOrthogonal
  have normalizedTailOrthogonal : OrthogonalPolyline normalizedTail :=
    AxisDirection.normalizeOrthogonalPolyline_orthogonal
      terminalTailNonempty terminalTailOrthogonal
  have normalizedTailSimple :
      LocalIncidenceDrawing.RouteIsSimple normalizedTail :=
    AxisDirection.normalizeOrthogonalPolyline_isSimple
      terminalTailNonempty terminalTailOrthogonal
  have normalizedTailHead : normalizedTail.head? = some radialBoundary := by
    simpa [normalizedTail, terminalTail] using
      (AxisDirection.normalizeOrthogonalPolyline_head?
        terminalTailNonempty terminalTailOrthogonal).trans
        (retainedFallbackFanTerminalTailRouteAt_head?
          center terminal.1 slot)
  have onlyCommon :
      ∀ point,
        point ∈ AxisDirection.unitSubdividePolyline radialPrefix →
        point ∈ AxisDirection.unitSubdividePolyline normalizedTail →
        point = radialBoundary :=
    retainedTerminalFanOuterRadialPrefix_normalizedTerminalTail_only_common
      center terminal slot radialPositive
  have localizedNormalization :
      AxisDirection.normalizeOrthogonalPolyline
          (joinAtEndpoint radialPrefix normalizedTail) =
        joinAtEndpoint
          (AxisDirection.normalizeOrthogonalPolyline radialPrefix)
          (AxisDirection.unitSubdividePolyline normalizedTail) :=
    AxisDirection.normalizeOrthogonalPolyline_joinAtEndpoint_of_only_common
      radialPrefixNonempty normalizedTailNonempty
      radialPrefixOrthogonal normalizedTailOrthogonal
      normalizedTailSimple radialPrefixLast normalizedTailHead onlyCommon
  rw [retainedFallbackFanOrdinarySuffixRouteAt_normalize_terminalTail_right
    center terminal slot lengthPositive radialPositive]
  calc
    Gadget.unitSubdivisionDirections
          (AxisDirection.normalizeOrthogonalPolyline
            (joinAtEndpoint radialPrefix normalizedTail)) =
        Gadget.unitSubdivisionDirections
            (AxisDirection.normalizeOrthogonalPolyline radialPrefix) ++
          Gadget.unitSubdivisionDirections normalizedTail :=
      Gadget.unitSubdivisionDirections_normalized_join
        localizedNormalization radialPrefixNonempty
        radialPrefixOrthogonal radialPrefixLast
        normalizedTailNonempty normalizedTailOrthogonal normalizedTailHead
    _ = Gadget.unitSubdivisionDirections radialPrefix ++
          Gadget.unitSubdivisionDirections normalizedTail := by
      rw [AxisDirection.unitSubdivisionDirections_normalizeOrthogonalPolyline_of_nodup
        radialPrefixNonempty radialPrefixOrthogonal radialPrefixNodup]
    _ = prefixDirections .ordinary terminal.1 slot ++
          radialCopies
              (retainedTerminalFanOuterRadialLength terminal - 1)
              terminal.1 ++
            retainedFallbackFanNormalizedTerminalTailDirections
              terminal.1 slot := by
      rw [retainedTerminalFanOuterRadialPrefix_directions,
        retainedFallbackFanTerminalTailRouteAt_normalized_directions]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
