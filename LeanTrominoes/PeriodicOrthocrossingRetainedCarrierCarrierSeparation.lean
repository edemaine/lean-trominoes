import LeanTrominoes.PeriodicOrthocrossingRetainedParallelCarrierSeparation
import LeanTrominoes.PeriodicOrthocrossingCarrierCarrierSeparation

/-!
# Separation of selected retained nonperpendicular carriers

Same-key selected links are separated by strict chain order.  Different-key
parallel links are separated by their source corridors.  Thus only the
perpendicular-link case remains.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Different-key selected links on a common axis have separated physical
rectangles. -/
theorem
    retainedDrawingCompleteCarrierLink_rectanglesSeparated_of_parallel_key_ne
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {firstLink secondLink : EqualityLink CarrierNode}
    (firstMem :
      firstLink ∈ retainedDrawingCompleteCarrierLinks graph)
    (secondMem :
      secondLink ∈ retainedDrawingCompleteCarrierLinks graph)
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
        retainedDrawingCompleteCarrierLink_rectanglesSeparated_of_horizontal_key_ne
          wellFormed degree isLocal firstMem secondMem
          firstHorizontal secondHorizontal keyDifferent
    · exact False.elim
        (notPerpendicular
          (Or.inl ⟨firstHorizontal, secondHorizontal⟩))
  · by_cases secondHorizontal :
        secondLink.first.isHorizontal = true
    · exact False.elim
        (notPerpendicular
          (Or.inr ⟨firstHorizontal, secondHorizontal⟩))
    · exact
        retainedDrawingCompleteCarrierLink_rectanglesSeparated_of_vertical_key_ne
          wellFormed degree isLocal firstMem secondMem
          firstHorizontal secondHorizontal keyDifferent

/-- Every genuine route pair from two distinct nonperpendicular selected
retained lenses avoids one another. -/
theorem
    retainedDrawingPlanarSATCarrierCarrierRoutesAvoidEachOther_of_not_perpendicular
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
      firstLink ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (secondMem :
      secondLink ∈ retainedDrawingCompleteCarrierLinks
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
      retainedDrawingPlanarSATCarrierCarrierRoutesAvoidEachOther_of_same_key
        wellFormed degree isLocal firstMem secondMem different sameKey
        firstClauseMember firstLiteralMember
        secondClauseMember secondLiteralMember
  · have rectanglesSeparated :=
      retainedDrawingCompleteCarrierLink_rectanglesSeparated_of_parallel_key_ne
        wellFormed degree isLocal firstMem secondMem
        notPerpendicular sameKey
    exact
      retainedDrawingPlanarSATCarrierCarrierRoutesAvoidEachOther_of_rectanglesSeparated
        wellFormed degree isLocal firstMem secondMem rectanglesSeparated
        firstClauseMember firstLiteralMember
        secondClauseMember secondLiteralMember

end PeriodicOrthocrossing
end LeanTrominoes
