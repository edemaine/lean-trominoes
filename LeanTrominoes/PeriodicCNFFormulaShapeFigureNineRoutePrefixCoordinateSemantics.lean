/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineFinalClauseOrderingSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixLocalDirectionSemantics
import LeanTrominoes.PeriodicCNFClauseProfilePolarityIndexedRouteOperationSemantics

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

end FormulaShapeFigureNineRoutePrefix
end PeriodicCNF
end LeanTrominoes
