/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixCoordinateSemantics

/-! # Profile-qualified presentation coordinates of Figure 9 headers -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNineRoutePrefix

open FormulaShapeDirectionOrdering
open FormulaShapeFigureNinePolarityRouteHeader
open PlanarOneInThreeNoUnitsFigureNine

/-- Every emitted header carries the exact clockwise parent profile in
addition to its already-established template coordinates. -/
theorem sourceClauseHeaders_map_headerTemplateProfileCoordinate :
    ∀ profile : DirectedClauseProfile,
      (sourceClauseHeaders profile).map
          headerTemplateProfileCoordinate =
        expectedSourceClauseHeaderTemplateProfileCoordinates profile := by
  intro profile
  have checked := sourceHeaderCoordinatesCheck_correct profile
  simp only [sourceHeaderCoordinatesCheck, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact checked.2

/-- Profile-qualified coordinate block emitted by one source token. -/
def expectedHeaderTemplateProfileCoordinateBlock :
    FormulaShapeDirectionOrdering.Token →
      List HeaderTemplateProfileCoordinate
  | .clause profile =>
      expectedSourceClauseHeaderTemplateProfileCoordinates profile
  | .variable => []

/-- Dynamic tails do not affect the profile-qualified header-coordinate
stream of a complete source. -/
theorem sourcePairs_map_headerTemplateProfileCoordinate
    (source : List FormulaShapeDirectionOrdering.Token)
    (tailTables : List (List (List AxisDirection))) :
    (FormulaShapeFigureNinePolarityRouteTail.sourcePairs
      source tailTables).map (fun pair =>
        headerTemplateProfileCoordinate pair.1) =
      source.flatMap expectedHeaderTemplateProfileCoordinateBlock := by
  rw [show
      (FormulaShapeFigureNinePolarityRouteTail.sourcePairs
        source tailTables).map (fun pair =>
          headerTemplateProfileCoordinate pair.1) =
        ((FormulaShapeFigureNinePolarityRouteTail.sourcePairs
          source tailTables).map Prod.fst).map
            headerTemplateProfileCoordinate by
    rw [List.map_map]
    rfl]
  rw [FormulaShapeFigureNinePolarityRouteTail.sourcePairs_map_fst]
  induction source with
  | nil => rfl
  | cons token source induction =>
      cases token with
      | «variable» =>
          simpa [FormulaShapeFigureNinePolarityRouteHeader.sourceHeaders,
            FormulaShapeFigureNinePolarityRouteHeader.tokenBlock,
            expectedHeaderTemplateProfileCoordinateBlock] using induction
      | clause profile =>
          simp only [FormulaShapeFigureNinePolarityRouteHeader.sourceHeaders,
            FormulaShapeFigureNinePolarityRouteHeader.tokenBlock,
            expectedHeaderTemplateProfileCoordinateBlock,
            List.map_append, List.flatMap_cons]
          rw [sourceClauseHeaders_map_headerTemplateProfileCoordinate]
          congr 1

end FormulaShapeFigureNineRoutePrefix
end PeriodicCNF
end LeanTrominoes
