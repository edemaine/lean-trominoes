/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularCarrierTerminalCoordinateData

/-! # Tagged-link presentation of retained carrier coordinates -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT

/-- Two coordinates per tagged carrier implication, retaining the global
clause indices even though terminal data itself does not depend on them. -/
def retainedCarrierTaggedTerminalCoordinates
    {Variable : Type} [DecidableEq Variable]
    (retained : PeriodicCNF Variable)
    (links : List (EqualityLink CarrierNode))
    (start : Nat) : List (Nat × Nat) :=
  (((links.product [true, false]).zipIdx start).flatMap fun tagged =>
    [retainedTerminalDataCoordinate
        (carrierLensRouteTerminalDataTagged
          tagged.1.1.first.isHorizontal
          (AxisDirection.axisSpan
            (CarrierNode.position retained.incidenceGraph tagged.1.1.first)
            (CarrierNode.position retained.incidenceGraph tagged.1.1.second))
          tagged.1.2 0),
      retainedTerminalDataCoordinate
        (carrierLensRouteTerminalDataTagged
          tagged.1.1.first.isHorizontal
          (AxisDirection.axisSpan
            (CarrierNode.position retained.incidenceGraph tagged.1.1.first)
            (CarrierNode.position retained.incidenceGraph tagged.1.1.second))
          tagged.1.2 1)])

/-- One canonical four-coordinate block per retained carrier link. -/
def retainedCarrierLinkTerminalCoordinates
    {Variable : Type} [DecidableEq Variable]
    (retained : PeriodicCNF Variable)
    (links : List (EqualityLink CarrierNode)) : List (Nat × Nat) :=
  links.flatMap fun link =>
    List.map retainedTerminalDataCoordinate
      (carrierLensRouteTerminalDataBlock link.first.isHorizontal
        (AxisDirection.axisSpan
          (CarrierNode.position retained.incidenceGraph link.first)
          (CarrierNode.position retained.incidenceGraph link.second)))

end PeriodicEightOccurrenceSplit
end LeanTrominoes
