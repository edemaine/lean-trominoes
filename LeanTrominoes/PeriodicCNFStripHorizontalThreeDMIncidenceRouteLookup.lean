/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMDrawingData
import LeanTrominoes.OrthogonalPolylineEndpointDirections

/-! # Direct lookup of horizontal normalized incidence routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget PeriodicOrthocrossing
open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- The executable normalization pair exposes its problem component without
unfolding any of the horizontal drawing construction. -/
@[simp] theorem horizontalNormalizationInputComputed_problem
    (source : PeriodicCNF Nat) :
    (horizontalNormalizationInputComputed source).problem =
      horizontalThreeDMProblemComputed source := by
  rfl

/-- The executable normalization pair exposes its drawing component without
unfolding any of the horizontal problem construction. -/
@[simp] theorem horizontalNormalizationInputComputed_drawing
    (source : PeriodicCNF Nat) :
    (horizontalNormalizationInputComputed source).drawing =
      horizontalThreeDMDrawingComputed source := by
  rfl

/-- Looking up a member's index in a pointwise map returns its image.  Keeping
this argument polymorphic avoids reducing either horizontal constructor while
discharging the final lookup. -/
private theorem getD_map_idxOf_of_mem
    {α β : Type*} [DecidableEq α]
    (keys : List α) (value : α → β) (default : β)
    {key : α} (member : key ∈ keys) :
    (keys.map value).getD (keys.idxOf key) default = value key := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_idxOf member]
  rfl

/-- The normalization input's tag-indexed incidence lookup retrieves the
proof-free horizontal assembled route stored at that tag. -/
theorem horizontalNormalizationIncidenceRouteComputed_eq_routeAtTag
    (source : PeriodicCNF Nat)
    (tag : PeriodicThreeDM.IncidenceTag)
    (tagMember :
      tag ∈ (horizontalThreeDMProblemComputed source).incidenceTags) :
    PeriodicThreeDM.NormalizationCompiler.incidenceRoute
        (horizontalNormalizationInputComputed source) tag =
      horizontalAssembledRouteAtTagComputed (source, tag) := by
  unfold PeriodicThreeDM.NormalizationCompiler.incidenceRoute
  rw [horizontalNormalizationInputComputed_problem,
    horizontalNormalizationInputComputed_drawing]
  unfold PeriodicThreeDM.incidenceRouteIndex
    PeriodicGridDrawing.edgeRoute
  rw [horizontalThreeDMDrawingComputed_edgeRoutes]
  unfold horizontalThreeDMEdgeRoutesComputed
    horizontalThreeDMIncidenceTagsComputed
  exact getD_map_idxOf_of_mem
    (horizontalThreeDMProblemComputed source).incidenceTags
    (fun selected =>
      horizontalAssembledRouteAtTagComputed (source, selected))
    [] tagMember

/-- If the stable triple lookup names a clause-core triple, the incidence's
first direction is read directly from the fixed clause route table. -/
theorem horizontalNormalizationClauseIncidenceFirstDirectionComputed
    (source : PeriodicCNF Nat)
    (tag : PeriodicThreeDM.IncidenceTag)
    (clauseIndex : Nat) (set : PlanarThreeDM.X3CClauseSet)
    (tagMember :
      tag ∈ (horizontalThreeDMProblemComputed source).incidenceTags)
    (tripleEq :
      horizontalAssembledRouteTriple?Computed (source, tag) =
        some (.clause clauseIndex set)) :
    AxisDirection.polylineFirstDirection
        (PeriodicThreeDM.NormalizationCompiler.incidenceRoute
          (horizontalNormalizationInputComputed source) tag) =
      AxisDirection.polylineFirstDirection
        (PlanarThreeDM.X3CClauseOrthogonal.route set tag.color) := by
  rw [horizontalNormalizationIncidenceRouteComputed_eq_routeAtTag
    source tag tagMember]
  unfold horizontalAssembledRouteAtTagComputed
    typedRouteFromOptionData
  rw [tripleEq]
  simp [horizontalTypedIncidenceRouteComputed,
    horizontalClauseIncidenceRouteComputed]

end PeriodicCNFStripReduction
end LeanTrominoes
