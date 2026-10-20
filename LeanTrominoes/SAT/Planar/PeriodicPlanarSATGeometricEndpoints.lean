/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Planar.PeriodicPlanarBoundedLocalCompleteness

/-! # Orthogonal, endpoint-separated geometry of the supplied SAT reductions -/
namespace LeanTrominoes.PeriodicPlanarSAT

def StrongGeometry (drawing : PeriodicGridDrawing) : Prop :=
  drawing.IsOrthogonal ∧ drawing.IsRibbonReady

def Geometric {V : Type} (problem : Input V → Prop) (input : Input V) : Prop :=
  problem input ∧ StrongGeometry input.2

namespace ThreeOccurrenceGeometry
open PeriodicOrthocrossing PositionedPeriodicCNF
variable {V : Type} [DecidableEq V]

 theorem ribbonReady (f : PeriodicCNF V) (hl : f.IsLocal) (hw : f.WidthAtMost 3)
    (ho : f.OccurrencesAtMost 3) (hn : ∀ c∈f.clauses, c≠[]) : (drawing f).IsRibbonReady := by
  apply PeriodicGridDrawing.isRibbonReady_of_relativeLiftedRoutesAvoidEachOther
  · exact incidenceDrawing_relativeLiftedRoutesAvoidEachOther (formula f) (placement f) (routes f)
      (retainedFigureNineClearancePlacement_period_pos f)
      (retainedFigureNineClearanceIncidenceRoutes_relativeAvoidEachOther f hl hw ho hn)
  · apply incidenceDrawing_routesSimple_of_pointwise
    intro c i hc l j hlit
    exact retainedFigureNineClearanceIncidenceRoutes_isSimple f hl hw ho hn hc hlit
  · apply incidenceDrawing_hasUnitSteps_of_pointwise
    intro c i hc l j hlit
    exact retainedFigureNineClearanceIncidenceRoutes_unitSteps f hl hw ho hn hc hlit

private theorem incidence_orthogonal {A : Type} [DecidableEq A]
    (source : PositionedPeriodicCNF A) (placement : PeriodicVariablePlacement A) (routes : IncidenceRoutes)
    (orthogonal : ∀ c i, (c,i)∈source.clauses.zipIdx → ∀ l j, (l,j)∈c.literals.zipIdx →
      PeriodicOrthocrossing.OrthogonalPolyline (routes i j)) : (incidenceDrawing source placement routes).IsOrthogonal := by
  rw [PeriodicGridDrawing.isOrthogonal_iff_routes]
  intro route routeMember
  change route∈incidenceEdgeRoutes source routes at routeMember
  rw [incidenceEdgeRoutes_eq_metadata_map] at routeMember
  obtain ⟨incidence,member,rfl⟩ := List.mem_map.mp routeMember
  obtain ⟨index,within,atIndex⟩ := List.mem_iff_getElem.mp member
  have tagged : (incidence,index)∈(PeriodicCNF.incidencesWithMetadata source.erase).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,List.getElem?_eq_some_iff]
    exact ⟨within,atIndex⟩
  obtain ⟨c,l,hc,hl,_⟩ := incidenceMetadata_of_tagged source tagged
  exact orthogonal c incidence.clauseIndex hc l incidence.literalIndex hl

 theorem strongGeometry (f : PeriodicCNF V) (hl : f.IsLocal) (hw : f.WidthAtMost 3)
    (ho : f.OccurrencesAtMost 3) (hn : ∀ c∈f.clauses, c≠[]) : StrongGeometry (drawing f) :=
by
  constructor
  · apply incidence_orthogonal (formula f) (placement f) (routes f)
    intro c i hc l j hlit
    exact (retainedFigureNineClearanceIncidenceRoutes_valid f hl hw ho hn hc hlit).2.2
  · exact ribbonReady f hl hw ho hn
end ThreeOccurrenceGeometry

namespace ExactOneEndpoint
open PeriodicOrthocrossing
variable {V : Type} [DecidableEq V]
local instance : DecidableEq (Target V) := PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

 theorem strongGeometry (f : PeriodicCNF V) (hl : f.IsLocal) (hw : f.WidthAtMost 3)
    (ho : f.OccurrencesAtMost 3) (hn : ∀ c∈f.clauses, c≠[]) : StrongGeometry (drawing f) := by
  unfold StrongGeometry drawing positioned
  rw [retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed_eq f hl hw ho hn,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed_eq f hl hw ho hn]
  exact ⟨retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_isOrthogonal f hl hw ho hn,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauged_isRibbonReady f hl hw ho hn⟩
end ExactOneEndpoint
end LeanTrominoes.PeriodicPlanarSAT
