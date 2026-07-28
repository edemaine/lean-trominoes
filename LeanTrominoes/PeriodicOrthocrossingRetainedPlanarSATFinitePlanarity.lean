import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGlobalRouteSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGlobalClausePositions
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGlobalVariableClausePositions
import LeanTrominoes.EmbeddedCNFIncidenceDrawingVertexCoverage

/-!
# Residual finite planarity for the retained planar SAT drawing

The retained assembly already has simple routes and pairwise continuous
route separation.  This file isolates the exact remaining geometric
obligation: graph vertices must avoid genuine route interiors, and all graph
vertex positions must be distinct.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- The two vertex-separation fields still needed after global retained-route
separation has been established. -/
def RetainedDrawingPlanarSATVertexSeparation
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : Prop :=
  (retainedDrawingPlanarSATLocalIncidenceDrawing
      formula).VerticesAvoidRouteInteriors ∧
    (retainedDrawingPlanarSATLocalIncidenceDrawing
      formula).vertexPositions.Nodup

/-- Complete finite planarity of the retained drawing is equivalent to its
two residual vertex-separation fields. -/
theorem
    retainedDrawingPlanarSATLocalIncidenceDrawing_isPlanar_iff_vertexSeparation
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    (retainedDrawingPlanarSATLocalIncidenceDrawing formula).IsPlanar ↔
      RetainedDrawingPlanarSATVertexSeparation formula := by
  constructor
  · intro planar
    exact planar.2.2
  · rintro ⟨verticesAvoid, verticesNodup⟩
    exact
      ⟨retainedDrawingPlanarSATLocalIncidenceDrawing_routesAreSimple
          formula wellFormed degree isLocal,
        retainedDrawingPlanarSATLocalIncidenceDrawing_routesAvoidEachOther
          formula wellFormed degree isLocal,
        verticesAvoid, verticesNodup⟩

/-- If every retained clause is incident to a literal, exact endpoints and
the completed global route separation discharge vertex/interior avoidance. -/
theorem
    retainedDrawingPlanarSATLocalIncidenceDrawing_verticesAvoidRouteInteriors
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    (retainedDrawingPlanarSATLocalIncidenceDrawing
      formula).VerticesAvoidRouteInteriors := by
  let drawing :=
    retainedDrawingPlanarSATLocalIncidenceDrawing formula
  have covered : drawing.VertexPositionsCoveredByRoutes := by
    apply drawing.vertexPositionsCoveredByRoutes_of_routesMatch
      (retainedDrawingPlanarSATLocalIncidenceDrawing_routesMatch
        formula wellFormed degree isLocal)
    simpa [drawing] using clausesNonempty
  exact drawing.verticesAvoidRouteInteriors_of_covered
    covered
    (retainedDrawingPlanarSATLocalIncidenceDrawing_routesAreSimple
      formula wellFormed degree isLocal)
    (retainedDrawingPlanarSATLocalIncidenceDrawing_routesAvoidEachOther
      formula wellFormed degree isLocal)

/-- The assembled retained drawing has no coincident graph vertices. -/
theorem
    retainedDrawingPlanarSATLocalIncidenceDrawing_vertexPositions_nodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    (retainedDrawingPlanarSATLocalIncidenceDrawing
      formula).vertexPositions.Nodup := by
  exact
    EmbeddedCNFIncidenceDrawing.vertexPositions_nodup_of_parts
      (retainedDrawingPlanarSATLocalIncidenceDrawing formula)
      (retainedDrawingPlanarSATLocalIncidenceDrawing_variablePosition_injective
        formula wellFormed degree isLocal)
      (retainedDrawingPlanarSATLocalIncidenceDrawing_clausePositions_nodup
        formula wellFormed degree isLocal clausesNonempty)
      (retainedDrawingPlanarSATLocalIncidenceDrawing_variableClauseDisjoint
        formula wellFormed degree isLocal)

/-- The retained finite incidence drawing is continuously planar. -/
theorem retainedDrawingPlanarSATLocalIncidenceDrawing_isPlanar
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    (retainedDrawingPlanarSATLocalIncidenceDrawing formula).IsPlanar := by
  rw [
    retainedDrawingPlanarSATLocalIncidenceDrawing_isPlanar_iff_vertexSeparation
      formula wellFormed degree isLocal]
  exact
    ⟨retainedDrawingPlanarSATLocalIncidenceDrawing_verticesAvoidRouteInteriors
        formula wellFormed degree isLocal clausesNonempty,
      retainedDrawingPlanarSATLocalIncidenceDrawing_vertexPositions_nodup
        formula wellFormed degree isLocal clausesNonempty⟩

end PeriodicOrthocrossing
end LeanTrominoes
