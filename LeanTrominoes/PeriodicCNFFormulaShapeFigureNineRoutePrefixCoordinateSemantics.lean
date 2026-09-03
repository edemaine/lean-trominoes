/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineFinalClauseOrderingSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixLocalDirectionSemantics
import LeanTrominoes.PeriodicCNFClauseProfilePolarityIndexedRouteOperationSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteTailPairs

/-! # Presentation coordinates selected by final Figure 9 headers -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNineRoutePrefix

open ClauseProfilePolarityRouteOperation
open FormulaShapeDirectionOrdering
open FormulaShapeFigureNineFinalClauseOrdering
open FormulaShapeFigureNinePolarityRouteHeader
open PlanarOneInThreeNoUnitsFigureNine

/-- The polarity operation and original template incidence coordinates
selected by one final Figure 9 route header. -/
structure HeaderTemplateCoordinate where
  polarity : IndexedDescriptor
  clauseIndex : Nat
  literalIndex : Nat
  deriving DecidableEq

/-- Read a header's exact clause-major, literal-minor template coordinates. -/
def headerTemplateCoordinate (header : Header) : HeaderTemplateCoordinate :=
  let query := header.figurePrefix.localQuery
  let incidence :=
    (templateDrawingOfClauseProfile query.1).incidenceAt query.2
  ⟨header.polarity.indexed, incidence.clauseIndex, incidence.literalIndex⟩

/-- The coordinate schedule obtained directly from the finite template,
including the final within-clause clockwise permutation. -/
def expectedSourceClauseHeaderTemplateCoordinates
    (profile : DirectedClauseProfile) : List HeaderTemplateCoordinate :=
  let ordered := orderedDirectedProfile profile
  let drawing := templateDrawingOfClauseProfile (clauseProfile ordered)
  drawing.formula.zipIdx.flatMap fun taggedClause =>
    let generatedProfile := embeddedClauseProfile taggedClause.1
    let sourceOrder :=
      reorderList (List.range taggedClause.1.literals.length)
    (ClauseProfilePolarityRouteOperation.descriptors
      (reorderProfile generatedProfile)).map fun polarity =>
        ⟨polarity.indexed, taggedClause.2,
          sourceOrder.getD (sourceSlotNat polarity.sourceSlot) 0⟩

/-- Every final header selects exactly the original finite-template
incidence prescribed by its generated clause and reordered literal slot. -/
theorem sourceClauseHeaders_map_headerTemplateCoordinate :
    ∀ profile : DirectedClauseProfile,
      (sourceClauseHeaders profile).map headerTemplateCoordinate =
        expectedSourceClauseHeaderTemplateCoordinates profile := by
  native_decide

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
