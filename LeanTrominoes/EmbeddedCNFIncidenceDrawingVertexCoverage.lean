import LeanTrominoes.EmbeddedCNFIncidenceDrawingPlanarity
import LeanTrominoes.PeriodicGridDrawingPointBounds

/-!
# Covering embedded CNF vertices by incidence routes

For a drawing whose clauses are nonempty, exact route endpoints put every
variable and clause vertex on at least one genuine incidence route.  Once
such coverage is known, route simplicity and pairwise route separation imply
that no graph vertex lies in any route interior.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

namespace EmbeddedCNFIncidenceDrawing

/-- Every graph-vertex position occurs as a listed point of at least one
genuine incidence route. -/
def VertexPositionsCoveredByRoutes
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable) : Prop :=
  ∀ point ∈ drawing.vertexPositions,
    ∃ incidenceIndex : Fin drawing.incidences.length,
      point ∈ drawing.routeAt (drawing.incidenceAt incidenceIndex)

/-- Vertex coverage converts route simplicity and pairwise route separation
into the global vertex/interior avoidance field. -/
theorem verticesAvoidRouteInteriors_of_covered
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (covered : drawing.VertexPositionsCoveredByRoutes)
    (simple : drawing.RoutesAreSimple)
    (separated :
      ∀ firstIndex secondIndex : Fin drawing.incidences.length,
        firstIndex ≠ secondIndex →
          RoutesAvoidEachOther
            (drawing.routeAt (drawing.incidenceAt firstIndex))
            (drawing.routeAt (drawing.incidenceAt secondIndex))) :
    drawing.VerticesAvoidRouteInteriors := by
  intro vertexIndex incidenceIndex
  dsimp only
  intro segmentIndex interior
  have vertexMember :
      drawing.vertexPositions.get vertexIndex ∈
        drawing.vertexPositions :=
    List.get_mem drawing.vertexPositions vertexIndex
  rcases covered
      (drawing.vertexPositions.get vertexIndex) vertexMember with
    ⟨coveringIndex, pointMember⟩
  by_cases same : coveringIndex = incidenceIndex
  · subst incidenceIndex
    exact
      (simple coveringIndex).2.1
        (drawing.vertexPositions.get vertexIndex) pointMember
        ((gridPolylineSegments
          (drawing.routeAt
            (drawing.incidenceAt coveringIndex))).get segmentIndex)
        (List.get_mem _ segmentIndex) interior
  · rcases List.mem_iff_get.mp pointMember with
      ⟨pointIndex, pointEqual⟩
    exact
      (separated coveringIndex incidenceIndex same).2.1
        pointIndex segmentIndex (by rw [pointEqual]; exact interior)

/-- Exact endpoints cover every vertex when every embedded clause has at
least one literal. -/
theorem vertexPositionsCoveredByRoutes_of_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (routesMatch : drawing.RoutesMatch)
    (clausesNonempty :
      ∀ clause ∈ drawing.formula, clause.literals ≠ []) :
    drawing.VertexPositionsCoveredByRoutes := by
  have physicalRoutesMatch :=
    drawing.physicalRoutesMatch routesMatch
  intro point pointMember
  simp only [vertexPositions, List.mem_append, List.mem_map]
    at pointMember
  rcases pointMember with variablePoint | clausePoint
  · rcases variablePoint with
      ⟨atom, variableMember, pointEqual⟩
    rw [variableVertices, List.mem_dedup] at variableMember
    rcases List.mem_flatMap.mp variableMember with
      ⟨clause, clauseMember, variableMember⟩
    rcases List.mem_map.mp variableMember with
      ⟨literal, literalMember, variableEqual⟩
    rcases List.mem_iff_get.mp clauseMember with
      ⟨clauseIndex, clauseEqual⟩
    rcases List.mem_iff_get.mp literalMember with
      ⟨literalIndex, literalEqual⟩
    have taggedClauseMember :
        (clause, clauseIndex.1) ∈ drawing.formula.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?,
        List.getElem?_eq_some_iff]
      exact ⟨clauseIndex.2, by simpa using clauseEqual⟩
    have taggedLiteralMember :
        (literal, literalIndex.1) ∈ clause.literals.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?,
        List.getElem?_eq_some_iff]
      exact ⟨literalIndex.2, by simpa using literalEqual⟩
    let incidence : EmbeddedCNFIncidence Variable :=
      ⟨clause, clauseIndex.1, literal, literalIndex.1⟩
    have incidenceMember : incidence ∈ drawing.incidences :=
      (mem_embeddedCNFIncidences_iff
        drawing.formula incidence).mpr
          ⟨taggedClauseMember, taggedLiteralMember⟩
    rcases List.mem_iff_get.mp incidenceMember with
      ⟨incidenceIndex, incidenceEqual⟩
    refine ⟨incidenceIndex, ?_⟩
    have endpointMember :
        drawing.variablePosition literal.1 ∈
          drawing.routes clauseIndex.1 literalIndex.1 :=
      mem_of_getLast?_eq_some
        (physicalRoutesMatch
          clause clauseIndex.1 taggedClauseMember
          literal literalIndex.1 taggedLiteralMember).2
    have incidenceAtEqual :
        drawing.incidenceAt incidenceIndex = incidence :=
      incidenceEqual
    rw [incidenceAtEqual]
    simpa [routeAt, ← variableEqual, ← pointEqual] using endpointMember
  · rcases clausePoint with
      ⟨clause, clauseMember, pointEqual⟩
    rcases List.mem_iff_get.mp clauseMember with
      ⟨clauseIndex, clauseEqual⟩
    have taggedClauseMember :
        (clause, clauseIndex.1) ∈ drawing.formula.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?,
        List.getElem?_eq_some_iff]
      exact ⟨clauseIndex.2, by simpa using clauseEqual⟩
    cases literalListEqual : clause.literals with
    | nil =>
        exact
          (clausesNonempty clause clauseMember literalListEqual).elim
    | cons literal rest =>
        have taggedLiteralMember :
            (literal, 0) ∈ clause.literals.zipIdx := by
          simp [literalListEqual]
        let incidence : EmbeddedCNFIncidence Variable :=
          ⟨clause, clauseIndex.1, literal, 0⟩
        have incidenceMember : incidence ∈ drawing.incidences :=
          (mem_embeddedCNFIncidences_iff
            drawing.formula incidence).mpr
              ⟨taggedClauseMember, taggedLiteralMember⟩
        rcases List.mem_iff_get.mp incidenceMember with
          ⟨incidenceIndex, incidenceEqual⟩
        refine ⟨incidenceIndex, ?_⟩
        have endpointLookup :
            (drawing.routes clauseIndex.1 0).head? =
              some clause.position :=
          (physicalRoutesMatch
            clause clauseIndex.1 taggedClauseMember
            literal 0 taggedLiteralMember).1
        have endpointMember :
            clause.position ∈ drawing.routes clauseIndex.1 0 :=
          List.mem_of_mem_head? (by simp [endpointLookup])
        have incidenceAtEqual :
            drawing.incidenceAt incidenceIndex = incidence :=
          incidenceEqual
        rw [incidenceAtEqual]
        simpa [routeAt, ← pointEqual] using endpointMember

end EmbeddedCNFIncidenceDrawing

end PlanarThreeSAT
end LeanTrominoes
