/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderClauseFrameData
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderEndpointDirections

/-! # Clause fan directions agree with reversed completed route words -/

namespace LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderClauseFrame

open Gadget PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader

/-- A present terminal uses the arriving direction of its complete route;
an absent terminal keeps the north fallback. -/
theorem directionAt_eq_completed
    (pairs : List (Header × List AxisDirection)) (index : Nat) :
    directionAt (pairs.map Prod.fst) index =
      ((pairs[index]?).map (fun pair =>
        (((HorizontalRoutedRouteHeader.block pair.1 pair.2).directions
          RetainedFigureNineRouteDirectionBlock.directions).headD .invalid).opposite)).getD .north := by
  simp only [directionAt, List.getElem?_map, Option.map_map]
  congr 1
  apply Option.map_congr
  intro pair pairMember
  exact congrArg AxisDirection.opposite
    (HorizontalRoutedRouteHeader.outputFirstDirection_eq_completed pair.1 pair.2)

/-- At an actual route, the finite header direction is the incoming
geometric direction used by the clause ribbon fan. -/
theorem directionAt_eq_polylineLastDirection_reverse
    (pairs : List (Header × List AxisDirection)) (index : Nat)
    (pair : Header × List AxisDirection)
    (lookup : pairs[index]? = some pair)
    (points : List Cell)
    (orthogonal : OrthogonalPolyline points)
    (wordEq :
      (HorizontalRoutedRouteHeader.block pair.1 pair.2).directions
        RetainedFigureNineRouteDirectionBlock.directions =
        unitSubdivisionDirections points) :
    directionAt (pairs.map Prod.fst) index =
      AxisDirection.polylineLastDirection points.reverse := by
  rw [directionAt_eq_completed, lookup]
  simp only [Option.map_some, Option.getD_some, wordEq,
    unitSubdivisionDirections_headD points orthogonal,
    AxisDirection.polylineLastDirection_reverse]

end LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderClauseFrame
