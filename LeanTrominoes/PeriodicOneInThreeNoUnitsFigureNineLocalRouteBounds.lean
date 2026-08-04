import LeanTrominoes.OrthogonalPolylineBoundingBox
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineLocalRoutes
import LeanTrominoes.PlanarOneInThreeNoUnitsFigureNineClauseExitFans

/-!
# Coordinate bounds for composed Figure 9 local routes

Every genuine route in each finite Figure 9-plus-unit-elimination template
lies in the same radius-73 square as the ordered clause-exit connectors.
Logical renaming leaves the route coordinates unchanged, and translation
places this square at the factor-72 refinement of the original source-clause
position.  The resulting physical bound is the local-neighborhood input to
the factor-144 lattice-clearance argument.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PlanarThreeSAT
open PeriodicEightOccurrenceSplit

/-- Every genuine empty-source template route lies in the common
radius-73 source neighborhood. -/
theorem zeroDrawing_routePoints_within_sourceNeighborhood :
    zeroDrawing.RoutePointsSatisfy
      (WithinCoordinateRadius 73 (0, 0)) := by
  native_decide

/-- Every genuine unit-source template route lies in the common radius-73
source neighborhood, independently of its polarity. -/
theorem oneDrawingFor_routePoints_within_sourceNeighborhood
    (first : Bool) :
    (oneDrawingFor first).RoutePointsSatisfy
      (WithinCoordinateRadius 73 (0, 0)) := by
  cases first <;> native_decide

/-- Every genuine binary-source template route lies in the common radius-73
source neighborhood, independently of its polarities. -/
theorem twoDrawingFor_routePoints_within_sourceNeighborhood
    (first second : Bool) :
    (twoDrawingFor first second).RoutePointsSatisfy
      (WithinCoordinateRadius 73 (0, 0)) := by
  cases first <;> cases second <;> native_decide

/-- Every genuine ternary-source template route lies in the common
radius-73 source neighborhood, independently of its polarities. -/
theorem fullDrawingFor_routePoints_within_sourceNeighborhood
    (first second third : Bool) :
    (fullDrawingFor first second third).RoutePointsSatisfy
      (WithinCoordinateRadius 73 (0, 0)) := by
  cases first <;> cases second <;> cases third <;> native_decide

/-- Every genuine route of the finite template selected at any source arity
lies in the common radius-73 source neighborhood. -/
theorem templateDrawing_routePoints_within_sourceNeighborhood
    {Variable : Type*}
    (source : PositionedPeriodicClause Variable) :
    (templateDrawing source).RoutePointsSatisfy
      (WithinCoordinateRadius 73 (0, 0)) := by
  rcases source with ⟨sourcePosition, literals⟩
  rcases literals with _ | ⟨first, rest⟩
  · exact zeroDrawing_routePoints_within_sourceNeighborhood
  · rcases rest with _ | ⟨second, rest⟩
    · exact oneDrawingFor_routePoints_within_sourceNeighborhood
        first.value
    · rcases rest with _ | ⟨third, tail⟩
      · exact twoDrawingFor_routePoints_within_sourceNeighborhood
          first.value second.value
      · exact fullDrawingFor_routePoints_within_sourceNeighborhood
          first.value second.value third.value

/-- Renaming and positioning a selected finite template translates its
radius-73 route-point certificate to the refined source-clause center. -/
theorem instantiatedDrawing_routePoints_within_sourceNeighborhood
    {Variable : Type*} [DecidableEq Variable]
    (sourceClauseIndex figureNineClauseStart : Nat)
    (source : PositionedPeriodicClause Variable) :
    (instantiatedDrawing
      sourceClauseIndex figureNineClauseStart source).RoutePointsSatisfy
        (WithinCoordinateRadius 73
          (Cell.scale composedGadgetScale source.position)) := by
  letI := nestedVariableDecidableEq (Variable := Variable)
  rw [instantiatedDrawing_eq]
  unfold EmbeddedCNFIncidenceDrawing.renameToImage
  refine
    ((templateDrawing_routePoints_within_sourceNeighborhood source).rename
      (instantiatedVariableMap
        sourceClauseIndex figureNineClauseStart source)
      (EmbeddedCNFIncidenceDrawing.imageVariablePosition
        (templateDrawing source)
        (instantiatedVariableMap
          sourceClauseIndex figureNineClauseStart source))).translate
      (Cell.scale composedGadgetScale source.position) ?_
  intro point pointBounded
  simpa [Cell.add] using
    pointBounded.translate
      (Cell.scale composedGadgetScale source.position)

/-- Metadata for a genuine final incidence exposes the original source
clause whose factor-72 center bounds every point of its selected physical
local route. -/
theorem localRoutes_points_within_sourceNeighborhood_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ metadata : ClauseMetadata Variable,
      (formulaClauseMetadata source)[clauseIndex]? = some metadata ∧
        metadata.clause = clause ∧
        (metadata.sourceClause, metadata.sourceClauseIndex) ∈
          source.clauses.zipIdx ∧
        ∀ point ∈ localRoutes source clauseIndex literalIndex,
          WithinCoordinateRadius 73
            (Cell.scale composedGadgetScale
              metadata.sourceClause.position) point := by
  letI := nestedVariableDecidableEq (Variable := Variable)
  rcases formulaClauseMetadata_lookup_valid_embedded
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual,
      sourceClauseMember, localClauseMember⟩
  have metadataLiteralMember :
      (literal, literalIndex) ∈
        metadata.clause.literals.zipIdx := by
    simpa [clauseEqual] using literalMember
  have metadataSourceMember :
      metadata.sourceClause ∈ source.clauses :=
    List.fst_mem_of_mem_zipIdx sourceClauseMember
  have metadataWidth :
      metadata.sourceClause.literals.length ≤ 3 := by
    apply sourceWidth metadata.sourceClause.literals
    exact List.mem_map.mpr
      ⟨metadata.sourceClause, metadataSourceMember, rfl⟩
  let drawing :=
    instantiatedDrawing
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause
  have drawingFormula :
      drawing.formula =
        composedClauseGadget
          metadata.sourceClauseIndex
          metadata.figureNineClauseStart
          metadata.sourceClause :=
    instantiatedDrawing_formula
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause metadataWidth
  have embeddedClauseMember :
      (PlanarOneInThreeNoUnits.embedPositionedClause
          metadata.clause,
        metadata.localClauseIndex) ∈ drawing.formula.zipIdx := by
    rw [drawingFormula]
    exact localClauseMember
  have embeddedLiteralMember :
      ((literal.atom, literal.value), literalIndex) ∈
        (PlanarOneInThreeNoUnits.embedPositionedClause
          metadata.clause).literals.zipIdx := by
    unfold PlanarOneInThreeNoUnits.embedPositionedClause
    rw [List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(literal, literalIndex), metadataLiteralMember, rfl⟩
  refine
    ⟨metadata, metadataLookup, clauseEqual,
      sourceClauseMember, ?_⟩
  intro point pointMember
  have bounded :=
    (instantiatedDrawing_routePoints_within_sourceNeighborhood
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause).of_members
        embeddedClauseMember embeddedLiteralMember
        (point := point)
  apply bounded
  simpa [localRoutes, metadataLookup, drawing] using pointMember

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
