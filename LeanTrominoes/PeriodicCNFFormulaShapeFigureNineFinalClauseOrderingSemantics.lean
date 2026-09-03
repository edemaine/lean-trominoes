/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteHeaderData

/-! # Finite semantics of the final Figure 9 clause ordering -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNineFinalClauseOrdering

open FormulaShapeDirectionOrdering
open FormulaShapeFigureNinePolarityRouteHeader
open FormulaShapeFigureNineRoutePrefix
open PlanarOneInThreeNoUnitsFigureNine
open UnaryProgramClauseProfile

/-- Attach the first direction of each finite template route to the literal
profile at the same generated-clause coordinate. -/
def embeddedDirectedClauseProfile
    (drawing : PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
      FigureNineNoUnitsVariable)
    (taggedClause :
      PlanarThreeSAT.EmbeddedClause FigureNineNoUnitsVariable × Nat) :
    DirectedClauseProfile :=
  DirectedClauseProfile.ofList
    (taggedClause.1.literals.zipIdx.map fun taggedLiteral =>
      (⟨false, taggedLiteral.1.2⟩,
        AxisDirection.polylineFirstDirection
          (drawing.routes taggedClause.2 taggedLiteral.2)))

/-- Direction-aware profiles of all generated clauses in the finite Figure 9
template, before the second clockwise sort. -/
def figureDirectedClauseProfiles (profile : DirectedClauseProfile) :
    List DirectedClauseProfile :=
  let drawing := templateDrawingOfClauseProfile (clauseProfile profile)
  drawing.formula.zipIdx.map (embeddedDirectedClauseProfile drawing)

/-- Forgetting route directions recovers the original generated profile
column exactly. -/
theorem figureDirectedClauseProfiles_map_clauseProfile :
    ∀ profile : DirectedClauseProfile,
      (figureDirectedClauseProfiles profile).map clauseProfile =
        figureClauseProfiles profile := by
  native_decide

/-- Sorting every finite template clause by its route's first direction is
exactly the explicit final permutation: binary clauses use `1,0`, and ternary
clauses use `2,0,1`. -/
theorem figureDirectedClauseProfiles_map_orderedProfile :
    ∀ profile : DirectedClauseProfile,
      (figureDirectedClauseProfiles profile).map
          DirectedClauseProfile.orderedProfile =
        finalFigureClauseProfiles profile := by
  native_decide

end FormulaShapeFigureNineFinalClauseOrdering
end PeriodicCNF
end LeanTrominoes
