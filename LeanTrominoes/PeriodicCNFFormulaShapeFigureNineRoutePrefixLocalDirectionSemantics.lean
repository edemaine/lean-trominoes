/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixData

/-! # Local route words named by Figure 9 prefix descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNineRoutePrefix

open Gadget PlanarOneInThreeNoUnitsFigureNine

/-- Forget the optional inherited connector while retaining the common
finite-template local route query. -/
def Descriptor.localQuery : Descriptor → LocalDirectionQuery
  | .local query => query
  | .inherited _ query => ⟨query.1, query.2.1⟩

/-- A descriptor constructed at a template incidence retains exactly that
incidence's local query, regardless of whether the atom is inherited. -/
@[simp] theorem localQuery_descriptorAt
    (profile : FormulaShapeDirectionOrdering.DirectedClauseProfile)
    (index : Fin
      (templateDrawingOfClauseProfile
        (clauseProfile profile)).incidences.length) :
    (descriptorAt profile index).localQuery =
      ⟨clauseProfile profile, index⟩ := by
  unfold descriptorAt
  dsimp only
  split <;> rfl

/-- Interpreting the common local query of every descriptor recovers the
template drawing's complete normalized incidence-route direction column in
clause-major, literal-minor order. -/
theorem clauseDescriptors_map_localDirections
    (profile : FormulaShapeDirectionOrdering.DirectedClauseProfile) :
    ((clauseDescriptors profile).map fun descriptor =>
        normalizedLocalDirectionBlock descriptor.localQuery) =
      (templateDrawingOfClauseProfile
          (clauseProfile profile)).incidences.map fun incidence =>
        unitSubdivisionDirections
          (AxisDirection.normalizeOrthogonalPolyline
            ((templateDrawingOfClauseProfile
              (clauseProfile profile)).routeAt incidence)) := by
  unfold clauseDescriptors
  rw [List.map_map]
  apply List.ext_getElem
  · simp
  · intro index leftLt rightLt
    simp only [List.getElem_map, List.getElem_finRange,
      Function.comp_apply]
    rw [localQuery_descriptorAt]
    rfl

end FormulaShapeFigureNineRoutePrefix
end PeriodicCNF
end LeanTrominoes
