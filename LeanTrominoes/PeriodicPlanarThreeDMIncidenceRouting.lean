import LeanTrominoes.PositionedPeriodicCNFIncidenceRouteLookup
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMTyped
import LeanTrominoes.PeriodicThreeDMContractionGeometry

/-!
# Reorienting exact-one incidences for planar 3DM assembly

The positioned exact-one incidence drawing directs an edge from a clause
prototype at its common anchor to a translated variable.  The planar 3DM
presentation stores the same connection in the opposite convention: its
variable-occurrence triple is the source at translate zero and references
the clause terminal at the negated literal offset.

This file performs exactly that change of basepoint.  It reverses the
certified incidence route and translates it by `anchor - literal.offset`.
The resulting route starts at the canonical variable position and ends at
the displayed clause position translated by the negated literal offset.
-/

namespace LeanTrominoes

open PeriodicOrthocrossing

namespace PeriodicVariablePlacement

/-- Physical translations respect addition of semantic lattice offsets. -/
theorem translation_add
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (first second : Cell) :
    placement.translation (Cell.add first second) =
      Cell.add (placement.translation first)
        (placement.translation second) := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [translation, Cell.scale, Cell.add, Prod.mk.injEq]
  constructor <;> ring

/-- Physical translations respect subtraction of semantic lattice offsets. -/
theorem translation_sub
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (first second : Cell) :
    placement.translation (Cell.sub first second) =
      Cell.sub (placement.translation first)
        (placement.translation second) := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [translation, Cell.scale, Cell.sub, Prod.mk.injEq]
  constructor <;> ring

end PeriodicVariablePlacement

namespace PositionedPeriodicCNF

/-- Reverse one certified clause-to-variable route and rebase it at the
variable prototype. -/
def PlanarIncidencePresentation.variableToClauseRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      PlanarIncidencePresentation source placement)
    (incidence : CNFIncidence Variable) : List Cell :=
  translatePolyline
    (placement.translation
      (Cell.sub
        (PeriodicCNF.clauseAnchor incidence.clause)
        incidence.literal.offset))
    (presentation.routes incidence.clauseIndex
      incidence.literalIndex).reverse

/-- The physical target of a variable-to-clause route is the displayed
clause vertex in the translate opposite the literal offset. -/
def variableToClauseTarget
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (positionedClause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable) : Cell :=
  Cell.add positionedClause.position
    (placement.translation
      (PeriodicOneInThreeToThreeDM.reverseOffset literal.offset))

/-- Reversing and rebasing an actual incidence route gives precisely the
endpoint convention used by the planar 3DM references. -/
theorem PlanarIncidencePresentation.variableToClauseRoute_endpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      PlanarIncidencePresentation source placement)
    {tagged : CNFIncidence Variable × Nat}
    (taggedMember :
      tagged ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx) :
    ∃ positionedClause : PositionedPeriodicClause Variable,
      ∃ literal : PeriodicLiteral Variable,
        (positionedClause, tagged.1.clauseIndex) ∈
            source.clauses.zipIdx ∧
          (literal, tagged.1.literalIndex) ∈
            positionedClause.literals.zipIdx ∧
          tagged.1 =
            ⟨tagged.1.clauseIndex, positionedClause.literals,
              tagged.1.literalIndex, literal⟩ ∧
          (presentation.variableToClauseRoute tagged.1).head? =
            some (placement.position literal.atom) ∧
          (presentation.variableToClauseRoute tagged.1).getLast? =
            some (variableToClauseTarget
              placement positionedClause literal) := by
  rcases tagged with ⟨incidence, edgeIndex⟩
  rcases incidenceMetadata_of_tagged
      source taggedMember with
    ⟨positionedClause, literal,
      clauseMember, literalMember, incidenceEq⟩
  have originalEndpoints :=
    presentation.route_endpoints_of_tagged taggedMember
  have clauseIndexLt :
      incidence.clauseIndex < source.clauses.length :=
    List.snd_lt_of_mem_zipIdx clauseMember
  have positionedClauseEq :
      source.clauses[incidence.clauseIndex] =
        positionedClause :=
    (List.mem_zipIdx' clauseMember).2.symm
  have incidenceClauseEq :
      incidence.clause = positionedClause.literals :=
    congrArg CNFIncidence.clause incidenceEq
  have incidenceLiteralEq :
      incidence.literal = literal :=
    congrArg CNFIncidence.literal incidenceEq
  have periodTranslationEq (offset : Cell) :
      (incidenceDrawing source placement
        presentation.routes).periodTranslation offset =
        placement.translation offset := by
    unfold PeriodicGridDrawing.periodTranslation
      PeriodicVariablePlacement.translation
    rw [incidenceDrawing_gridSize
      source placement presentation.routes
      presentation.periodPositive]
  have originalHead :
      (presentation.routes incidence.clauseIndex
        incidence.literalIndex).head? =
          some (canonicalClausePosition
            placement positionedClause) := by
    rw [incidenceEq] at originalEndpoints
    rw [incidenceVertexPositionAt_clause
      source placement incidence.clauseIndex clauseIndexLt,
      positionedClauseEq] at originalEndpoints
    exact originalEndpoints.1
  have originalLast :
      (presentation.routes incidence.clauseIndex
        incidence.literalIndex).getLast? =
          some (Cell.add
            (placement.position literal.atom)
            (placement.translation
              (Cell.sub literal.offset
                (PeriodicCNF.clauseAnchor
                  positionedClause.literals)))) := by
    rw [incidenceEq] at originalEndpoints
    simpa [periodTranslationEq] using originalEndpoints.2
  refine
    ⟨positionedClause, literal,
      clauseMember, literalMember, incidenceEq, ?_, ?_⟩
  · simp only [PlanarIncidencePresentation.variableToClauseRoute,
      translatePolyline, List.head?_map, List.head?_reverse,
      originalLast, Option.map_some]
    apply congrArg some
    rw [incidenceClauseEq, incidenceLiteralEq]
    rcases placement.position literal.atom with ⟨positionX, positionY⟩
    rcases PeriodicCNF.clauseAnchor positionedClause.literals with
      ⟨anchorX, anchorY⟩
    rcases literal.offset with ⟨literalX, literalY⟩
    apply Prod.ext <;>
      simp [PeriodicVariablePlacement.translation,
        Cell.scale, Cell.add, Cell.sub] <;> ring
  · simp only [PlanarIncidencePresentation.variableToClauseRoute,
      translatePolyline, List.getLast?_map,
      List.getLast?_reverse, originalHead, Option.map_some]
    apply congrArg some
    rw [incidenceClauseEq, incidenceLiteralEq]
    unfold variableToClauseTarget canonicalClausePosition
      PeriodicOneInThreeToThreeDM.reverseOffset
    rcases positionedClause.position with ⟨clauseX, clauseY⟩
    rcases PeriodicCNF.clauseAnchor positionedClause.literals with
      ⟨anchorX, anchorY⟩
    rcases literal.offset with ⟨literalX, literalY⟩
    apply Prod.ext <;>
      simp [PeriodicVariablePlacement.translation,
        Cell.scale, Cell.add, Cell.sub] <;> ring

/-- Reversal and rebasing preserve orthogonality of every certified
variable-to-clause route. -/
theorem PlanarIncidencePresentation.variableToClauseRoute_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      PlanarIncidencePresentation source placement)
    {tagged : CNFIncidence Variable × Nat}
    (taggedMember :
      tagged ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx) :
    OrthogonalPolyline
      (presentation.variableToClauseRoute tagged.1) := by
  have originalOrthogonal :
      OrthogonalPolyline
        (presentation.routes
          tagged.1.clauseIndex tagged.1.literalIndex) :=
    presentation.route_orthogonal_of_tagged taggedMember
  exact originalOrthogonal.reverse.translate _

end PositionedPeriodicCNF

end LeanTrominoes
