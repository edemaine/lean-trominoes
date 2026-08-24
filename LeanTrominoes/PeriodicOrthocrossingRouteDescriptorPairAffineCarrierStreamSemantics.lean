/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorSquareDiagonal
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCarrierNumericBlockSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCarrierOffDiagonalSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCarrierStreamBlockMapSemantics

/-! # Numeric stream semantics of affine carrier candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- On the numeric descriptor square, the compiled candidate scan is exactly
the route-major, segment-major, neighboring-translation-major axis stream. -/
theorem affineCarrierSegmentBitStream_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal) :
    affineCarrierSegmentBitStream
        (encodeDescriptorPairs
          ((PeriodicCNF.numericRouteDescriptors formula) ×ˢ
            (PeriodicCNF.numericRouteDescriptors formula))) =
      (PeriodicCNF.numericRouteDescriptors formula).flatMap fun descriptor =>
        (gridPolylineSegments descriptor.route).flatMap fun segment =>
          neighborTranslations.map fun _ =>
            (decide segment.IsHorizontal, false) := by
  rw [affineCarrierSegmentBitStream_encodeDescriptorPairs]
  rw [PeriodicCNF.numericRouteDescriptorSquare_flatMap_diagonal_of_offDiagonal
    formula
    (fun pair =>
      affineCarrierSegmentBitBlock (descriptorPairTokens pair))]
  · apply List.flatMap_congr
    intro descriptor descriptorMember
    rcases PeriodicCNF.numericRouteDescriptors_all_hasLocalShape
      formula forward descriptor descriptorMember with
      ⟨shape, shapeMatches⟩
    exact affineCarrierSegmentBitBlock_numeric_diagonal
      formula wellFormed degree isLocal shape descriptor
      descriptorMember shapeMatches
  · intro first _firstMember second _secondMember edgeIndexNe
    exact affineCarrierSegmentBitBlock_eq_nil_of_edgeIndex_ne
      (first, second) edgeIndexNe

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
