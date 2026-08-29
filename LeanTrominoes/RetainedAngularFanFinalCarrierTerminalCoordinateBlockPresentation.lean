/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierFamilyTerminalCoordinatesSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataTaggedCarrierTerminalData
import LeanTrominoes.RetainedAngularCarrierTaggedTerminalCoordinateFamily
import LeanTrominoes.ListProductBoolZipIdxFlatMap

/-! # Four-incidence block presentation of final carrier coordinates -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT

/-- The two implication clauses for each retained link flatten to the
canonical four-incidence carrier terminal block, independently of the
global starting clause index. -/
theorem taggedCarrierTerminalCoordinates_eq_linkBlocks
    {Variable : Type} [DecidableEq Variable]
    (retained : PeriodicCNF Variable)
    (links : List (EqualityLink CarrierNode))
    (start : Nat) :
    retainedCarrierTaggedTerminalCoordinates retained links start =
      retainedCarrierLinkTerminalCoordinates retained links := by
  unfold retainedCarrierTaggedTerminalCoordinates
  calc
    _ = links.flatMap fun link =>
        [retainedTerminalDataCoordinate
            (carrierLensRouteTerminalDataTagged link.first.isHorizontal
              (AxisDirection.axisSpan
                (CarrierNode.position
                  retained.incidenceGraph
                    link.first)
                (CarrierNode.position
                  retained.incidenceGraph
                    link.second)) true 0),
          retainedTerminalDataCoordinate
            (carrierLensRouteTerminalDataTagged link.first.isHorizontal
              (AxisDirection.axisSpan
                (CarrierNode.position
                  retained.incidenceGraph
                    link.first)
                (CarrierNode.position
                  retained.incidenceGraph
                    link.second)) true 1),
          retainedTerminalDataCoordinate
            (carrierLensRouteTerminalDataTagged link.first.isHorizontal
              (AxisDirection.axisSpan
                (CarrierNode.position
                  retained.incidenceGraph
                    link.first)
                (CarrierNode.position
                  retained.incidenceGraph
                    link.second)) false 0),
          retainedTerminalDataCoordinate
            (carrierLensRouteTerminalDataTagged link.first.isHorizontal
              (AxisDirection.axisSpan
                (CarrierNode.position
                  retained.incidenceGraph
                    link.first)
                (CarrierNode.position
                  retained.incidenceGraph
                    link.second)) false 1)] :=
      ListProductBoolZipIdxFlatMap.pair_eq_block links start
        (fun tagged literalIndex =>
          retainedTerminalDataCoordinate
            (carrierLensRouteTerminalDataTagged
              tagged.1.first.isHorizontal
              (AxisDirection.axisSpan
                (CarrierNode.position
                  retained.incidenceGraph
                    tagged.1.first)
                (CarrierNode.position
                  retained.incidenceGraph
                    tagged.1.second))
              tagged.2 literalIndex))
    _ = _ := by
      unfold retainedCarrierLinkTerminalCoordinates
      apply List.flatMap_congr
      intro link linkMember
      exact congrArg (List.map retainedTerminalDataCoordinate)
        (carrierLensRouteTerminalDataTagged_block_eq
          link.first.isHorizontal
          (AxisDirection.axisSpan
            (CarrierNode.position
              retained.incidenceGraph link.first)
            (CarrierNode.position
              retained.incidenceGraph link.second)))

end PeriodicEightOccurrenceSplit
end LeanTrominoes
