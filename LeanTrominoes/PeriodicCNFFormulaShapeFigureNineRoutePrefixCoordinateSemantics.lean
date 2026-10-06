/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixCoordinateCertificates.Case0
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixCoordinateCertificates.Case1
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixCoordinateCertificates.Case2
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixCoordinateCertificates.Case3
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixCoordinateCertificates.Case4
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixCoordinateCertificates.Case5
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixCoordinateCertificates.Case6
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixCoordinateCertificates.Case7
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixCoordinateCertificates.Case8
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixCoordinateCertificates.Case9
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixCoordinateCertificates.Case10
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixCoordinateCertificates.Case11
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixCoordinateCertificates.Case12
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixCoordinateCertificates.Case13
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixCoordinateCertificates.Case14
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixCoordinateCertificates.Case15
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixCoordinateCertificates.Case16
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixCoordinateCertificates.Case17
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixCoordinateCertificates.Case18
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixCoordinateCertificates.Case19

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNineRoutePrefix

open ClauseProfilePolarityRouteOperation
open FormulaShapeDirectionOrdering
open FormulaShapeFigureNineFinalClauseOrdering
open FormulaShapeFigureNinePolarityRouteHeader
open PlanarOneInThreeNoUnitsFigureNine

private theorem firstSourceHeaderCoordinatesCheck_correct
    (first : UnaryProgramClauseProfile.LiteralProfile) (direction : AxisDirection) :
    firstSourceHeaderCoordinatesCheck first direction = true := by
  rcases first with ⟨nextSlice, value⟩
  cases nextSlice <;> cases value <;> cases direction
  · exact firstSourceHeaderCoordinatesCheck_case0
  · exact firstSourceHeaderCoordinatesCheck_case1
  · exact firstSourceHeaderCoordinatesCheck_case2
  · exact firstSourceHeaderCoordinatesCheck_case3
  · exact firstSourceHeaderCoordinatesCheck_case4
  · exact firstSourceHeaderCoordinatesCheck_case5
  · exact firstSourceHeaderCoordinatesCheck_case6
  · exact firstSourceHeaderCoordinatesCheck_case7
  · exact firstSourceHeaderCoordinatesCheck_case8
  · exact firstSourceHeaderCoordinatesCheck_case9
  · exact firstSourceHeaderCoordinatesCheck_case10
  · exact firstSourceHeaderCoordinatesCheck_case11
  · exact firstSourceHeaderCoordinatesCheck_case12
  · exact firstSourceHeaderCoordinatesCheck_case13
  · exact firstSourceHeaderCoordinatesCheck_case14
  · exact firstSourceHeaderCoordinatesCheck_case15
  · exact firstSourceHeaderCoordinatesCheck_case16
  · exact firstSourceHeaderCoordinatesCheck_case17
  · exact firstSourceHeaderCoordinatesCheck_case18
  · exact firstSourceHeaderCoordinatesCheck_case19

/-- Both coordinate columns are certified for every directed profile. -/
theorem sourceHeaderCoordinatesCheck_correct (profile : DirectedClauseProfile) :
    sourceHeaderCoordinatesCheck profile = true := by
  cases profile with
  | unary first direction =>
    have checked := firstSourceHeaderCoordinatesCheck_correct first direction
    simp only [firstSourceHeaderCoordinatesCheck, Bool.and_eq_true, finiteAll_eq_true] at checked
    exact checked.1
  | binary first direction second secondDirection =>
    have checked := firstSourceHeaderCoordinatesCheck_correct first direction
    simp only [firstSourceHeaderCoordinatesCheck, Bool.and_eq_true, finiteAll_eq_true] at checked
    exact (checked.2 ⟨second, secondDirection⟩).1
  | ternary first direction second secondDirection third thirdDirection =>
    have checked := firstSourceHeaderCoordinatesCheck_correct first direction
    simp only [firstSourceHeaderCoordinatesCheck, Bool.and_eq_true, finiteAll_eq_true] at checked
    exact ((checked.2 ⟨second, secondDirection⟩).2 ⟨third, thirdDirection⟩)

/-- Every final header selects exactly the original finite-template
incidence prescribed by its generated clause and reordered literal slot. -/
theorem sourceClauseHeaders_map_headerTemplateCoordinate :
    ∀ profile : DirectedClauseProfile,
      (sourceClauseHeaders profile).map headerTemplateCoordinate =
        expectedSourceClauseHeaderTemplateCoordinates profile := by
  intro profile
  have checked := sourceHeaderCoordinatesCheck_correct profile
  simp only [sourceHeaderCoordinatesCheck, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact checked.1

/-- Coordinate block emitted by one direction-aware source token. -/
def expectedHeaderTemplateCoordinateBlock :
    FormulaShapeDirectionOrdering.Token → List HeaderTemplateCoordinate
  | .clause profile => expectedSourceClauseHeaderTemplateCoordinates profile
  | .variable => []

/-- Across a complete header/tail pair stream, dynamic tails do not affect
the exact finite-template coordinate schedule. -/
theorem sourcePairs_map_headerTemplateCoordinate
    (source : List FormulaShapeDirectionOrdering.Token)
    (tailTables : List (List (List AxisDirection))) :
    (FormulaShapeFigureNinePolarityRouteTail.sourcePairs
      source tailTables).map (fun pair =>
        headerTemplateCoordinate pair.1) =
      source.flatMap expectedHeaderTemplateCoordinateBlock := by
  rw [show
      (FormulaShapeFigureNinePolarityRouteTail.sourcePairs
        source tailTables).map (fun pair =>
          headerTemplateCoordinate pair.1) =
        ((FormulaShapeFigureNinePolarityRouteTail.sourcePairs
          source tailTables).map Prod.fst).map
            headerTemplateCoordinate by
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
            expectedHeaderTemplateCoordinateBlock] using induction
      | clause profile =>
          simp only [FormulaShapeFigureNinePolarityRouteHeader.sourceHeaders,
            FormulaShapeFigureNinePolarityRouteHeader.tokenBlock,
            expectedHeaderTemplateCoordinateBlock,
            List.map_append, List.flatMap_cons]
          rw [sourceClauseHeaders_map_headerTemplateCoordinate]
          congr 1

end FormulaShapeFigureNineRoutePrefix
end PeriodicCNF
end LeanTrominoes
