import LeanTrominoes.PeriodicOrthocrossingParallelCarrierSeparation
import LeanTrominoes.PeriodicOrthocrossingSameCarrierSeparation

/-!
# Separation of pairs of retained carrier lenses

Links on one source occurrence are separated by strict complete-carrier
order.  Parallel links on different occurrences are separated by their
continuous source corridors.  This leaves exactly the perpendicular-link
case for the crossover-boundary argument.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Two retained carrier links use perpendicular source axes. -/
def CarrierLinksPerpendicular
    (first second : EqualityLink CarrierNode) : Prop :=
  (first.first.isHorizontal = true ∧
      ¬second.first.isHorizontal = true) ∨
    (¬first.first.isHorizontal = true ∧
      second.first.isHorizontal = true)

instance (first second : EqualityLink CarrierNode) :
    Decidable (CarrierLinksPerpendicular first second) := by
  unfold CarrierLinksPerpendicular
  infer_instance

/-- Different-key links on a common axis have separated physical
rectangles. -/
theorem
    drawingCompleteCarrierLink_rectanglesSeparated_of_parallel_key_ne
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {firstLink secondLink : EqualityLink CarrierNode}
    (firstMem : firstLink ∈ drawingCompleteCarrierLinks graph)
    (secondMem : secondLink ∈ drawingCompleteCarrierLinks graph)
    (notPerpendicular :
      ¬CarrierLinksPerpendicular firstLink secondLink)
    (keyDifferent :
      firstLink.first.carrierKey ≠ secondLink.first.carrierKey) :
    ClosedGridRectanglesSeparated
      (drawingCompleteCarrierLinkRectangleLower graph firstLink)
      (drawingCompleteCarrierLinkRectangleUpper graph firstLink)
      (drawingCompleteCarrierLinkRectangleLower graph secondLink)
      (drawingCompleteCarrierLinkRectangleUpper graph secondLink) := by
  by_cases firstHorizontal :
      firstLink.first.isHorizontal = true
  · by_cases secondHorizontal :
        secondLink.first.isHorizontal = true
    · exact
        drawingCompleteCarrierLink_rectanglesSeparated_of_horizontal_key_ne
          wellFormed degree isLocal
          firstMem secondMem firstHorizontal secondHorizontal keyDifferent
    · exact False.elim
        (notPerpendicular
          (Or.inl ⟨firstHorizontal, secondHorizontal⟩))
  · by_cases secondHorizontal :
        secondLink.first.isHorizontal = true
    · exact False.elim
        (notPerpendicular
          (Or.inr ⟨firstHorizontal, secondHorizontal⟩))
    · exact
        drawingCompleteCarrierLink_rectanglesSeparated_of_vertical_key_ne
          wellFormed degree isLocal
          firstMem secondMem firstHorizontal secondHorizontal keyDifferent

/-- Every selected route pair from two distinct nonperpendicular carrier
lenses avoids one another. -/
theorem
    drawingPlanarSATCarrierCarrierRoutesAvoidEachOther_of_not_perpendicular
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {firstLink secondLink : EqualityLink CarrierNode}
    (firstMem :
      firstLink ∈ drawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (secondMem :
      secondLink ∈ drawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (different : firstLink ≠ secondLink)
    (notPerpendicular :
      ¬CarrierLinksPerpendicular firstLink secondLink)
    {firstClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {firstClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula firstLink).formula.zipIdx)
    {firstLiteral : PlanarSATVariable Variable × Bool}
    {firstLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    {secondClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {secondClauseIndex : Nat}
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula secondLink).formula.zipIdx)
    {secondLiteral : PlanarSATVariable Variable × Bool}
    {secondLiteralIndex : Nat}
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula firstLink).routes
          firstClauseIndex firstLiteralIndex)
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula secondLink).routes
          secondClauseIndex secondLiteralIndex) := by
  by_cases sameKey :
      firstLink.first.carrierKey =
        secondLink.first.carrierKey
  · exact
      drawingPlanarSATCarrierCarrierRoutesAvoidEachOther_of_same_key
        wellFormed degree isLocal
        firstMem secondMem different sameKey
        firstClauseMember firstLiteralMember
        secondClauseMember secondLiteralMember
  · have rectanglesSeparated :=
      drawingCompleteCarrierLink_rectanglesSeparated_of_parallel_key_ne
        wellFormed degree isLocal
        firstMem secondMem notPerpendicular sameKey
    exact
      drawingPlanarSATCarrierCarrierRoutesAvoidEachOther_of_rectanglesSeparated
        wellFormed degree isLocal
        firstMem secondMem rectanglesSeparated
        firstClauseMember firstLiteralMember
        secondClauseMember secondLiteralMember

end PeriodicOrthocrossing
end LeanTrominoes
