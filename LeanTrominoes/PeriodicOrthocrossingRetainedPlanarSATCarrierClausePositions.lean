import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATNoncarrierClausePositions
import LeanTrominoes.PeriodicOrthocrossingRetainedSameCarrierSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPerpendicularCarrierSeparation

/-!
# Distinct clause positions in retained straight-carrier lenses

A carrier equality clause lies in its lens's narrow rectangle.  Distinct
lenses have strictly separated rectangles except when consecutive links share
one carrier node.  In that exceptional case, the clauses lie three or six
cells after their respective first endpoints, while each lens advances by at
least eight cells, so the clause positions remain distinct.
-/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- A represented carrier clause uses one of its link's two explicit clause
positions. -/
theorem carrierClause_position_eq_forward_or_backward
    {Variable : Type*} [DecidableEq Variable]
    {link : EqualityLink CarrierNode}
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (member :
      (clause, clauseIndex) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) link).zipIdx) :
    clause.position = link.positions.forward ∨
      clause.position = link.positions.backward := by
  simp [drawingPlanarSATCarrierFormulaAt, equalityInstance,
    EmbeddedClause.rename, EmbeddedClause.map] at member
  rcases member with ⟨clauseEq, _⟩ | ⟨clauseEq, _⟩
  · left
    rw [clauseEq]
  · right
    rw [clauseEq]

/-- Clause vertices of consecutive lenses cannot coincide across their shared
carrier endpoint. -/
theorem retainedCarrierClausePosition_ne_of_shared_endpoint
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {earlier later : EqualityLink CarrierNode}
    (earlierMem :
      earlier ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (laterMem :
      later ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (shared : earlier.second = later.first)
    {earlierClause laterClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {earlierClauseIndex laterClauseIndex : Nat}
    (earlierClauseMember :
      (earlierClause, earlierClauseIndex) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) earlier).zipIdx)
    (laterClauseMember :
      (laterClause, laterClauseIndex) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) later).zipIdx) :
    earlierClause.position ≠ laterClause.position := by
  have earlierPosition :=
    carrierClause_position_eq_forward_or_backward earlierClauseMember
  have laterPosition :=
    carrierClause_position_eq_forward_or_backward laterClauseMember
  have earlierGeometry :=
    retainedDrawingCompleteCarrierLink_lensGeometry
      wellFormed degree isLocal earlierMem
  have laterGeometry :=
    retainedDrawingCompleteCarrierLink_lensGeometry
      wellFormed degree isLocal laterMem
  have earlierDirection :=
    retainedDrawingCompleteCarrierLink_carrierDirection_eq_axis
      wellFormed degree isLocal earlierMem
  have laterDirection :=
    retainedDrawingCompleteCarrierLink_carrierDirection_eq_axis
      wellFormed degree isLocal laterMem
  have earlierAxis :=
    retainedDrawingCompleteCarrierLink_first_isHorizontal_iff_second
      wellFormed degree isLocal earlierMem
  have clearance :=
    retainedDrawingCompleteCarrierLink_hasForwardClearance
      wellFormed degree isLocal earlierMem
  by_cases horizontal : earlier.first.isHorizontal = true
  · have laterHorizontal : later.first.isHorizontal = true := by
      rw [← shared]
      exact earlierAxis.mp horizontal
    rw [if_pos horizontal] at earlierDirection
    rw [if_pos laterHorizontal] at laterDirection
    change
      AxisDirection.between
          (earlier.first.position (PeriodicCNF.incidenceGraph formula))
          (earlier.second.position (PeriodicCNF.incidenceGraph formula)) =
        .east at earlierDirection
    change
      AxisDirection.between
          (later.first.position (PeriodicCNF.incidenceGraph formula))
          (later.second.position (PeriodicCNF.incidenceGraph formula)) =
        .east at laterDirection
    rw [earlierGeometry.positions] at earlierPosition
    rw [laterGeometry.positions] at laterPosition
    rw [earlierDirection] at earlierPosition
    rw [laterDirection] at laterPosition
    unfold CarrierNode.HasForwardClearance at clearance
    rw [if_pos horizontal] at clearance
    rcases earlierPosition with earlierPosition | earlierPosition <;>
      rcases laterPosition with laterPosition | laterPosition <;>
      intro equal
    all_goals
      rw [earlierPosition, laterPosition] at equal
      rw [shared] at clearance
      simp only [AxisDirection.placePoint, AxisDirection.orientPoint,
        Cell.add] at equal
      have equalX := congrArg Prod.fst equal
      simp only at equalX
      omega
  · have laterVertical : ¬later.first.isHorizontal = true := by
      intro laterHorizontal
      apply horizontal
      exact earlierAxis.mpr (by simpa [shared] using laterHorizontal)
    rw [if_neg horizontal] at earlierDirection
    rw [if_neg laterVertical] at laterDirection
    change
      AxisDirection.between
          (earlier.first.position (PeriodicCNF.incidenceGraph formula))
          (earlier.second.position (PeriodicCNF.incidenceGraph formula)) =
        .north at earlierDirection
    change
      AxisDirection.between
          (later.first.position (PeriodicCNF.incidenceGraph formula))
          (later.second.position (PeriodicCNF.incidenceGraph formula)) =
        .north at laterDirection
    rw [earlierGeometry.positions] at earlierPosition
    rw [laterGeometry.positions] at laterPosition
    rw [earlierDirection] at earlierPosition
    rw [laterDirection] at laterPosition
    unfold CarrierNode.HasForwardClearance at clearance
    rw [if_neg horizontal] at clearance
    rcases earlierPosition with earlierPosition | earlierPosition <;>
      rcases laterPosition with laterPosition | laterPosition <;>
      intro equal
    all_goals
      rw [earlierPosition, laterPosition] at equal
      rw [shared] at clearance
      simp only [AxisDirection.placePoint, AxisDirection.orientPoint,
        Cell.add] at equal
      have equalY := congrArg Prod.snd equal
      simp only at equalY
      omega

/-- Every clause vertex of a retained carrier lens lies in the lens's explicit
narrow rectangle. -/
theorem retainedCarrierClausePosition_bounded
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).formula.zipIdx) :
    InClosedGridRectangle
      (drawingCompleteCarrierLinkRectangleLower
        (PeriodicCNF.incidenceGraph formula) link)
      (drawingCompleteCarrierLinkRectangleUpper
        (PeriodicCNF.incidenceGraph formula) link)
      clause.position := by
  have nonempty : clause.literals ≠ [] := by
    have sourceMember := clauseMember
    rw [retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula
      wellFormed degree isLocal linkMem] at sourceMember
    simp [drawingPlanarSATCarrierFormulaAt, equalityInstance,
      EmbeddedClause.rename, EmbeddedClause.map] at sourceMember
    rcases sourceMember with ⟨clauseEq, _⟩ | ⟨clauseEq, _⟩ <;>
      rw [clauseEq] <;> simp
  cases literalsEq : clause.literals with
  | nil => exact (nonempty literalsEq).elim
  | cons literal rest =>
      have literalMember :
          (literal, 0) ∈ clause.literals.zipIdx := by
        simp [literalsEq]
      have endpoints :=
        (drawingPlanarSATCarrierLensIncidenceDrawing formula link)
          |>.physicalRoutesMatch
            (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_isValid
              wellFormed degree isLocal linkMem).1
            clause clauseIndex clauseMember
            literal 0 literalMember
      have positionMember :
          clause.position ∈
            (drawingPlanarSATCarrierLensIncidenceDrawing
              formula link).routes clauseIndex 0 :=
        List.mem_of_mem_head? (by simp [endpoints.1])
      exact
        (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_bounded
          wellFormed degree isLocal linkMem).of_members
            clauseMember literalMember positionMember

/-- Equal clause positions from retained carrier lenses identify the same
physical lens. -/
theorem retainedCarrierLinks_eq_of_clause_position_eq
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
    {firstClause secondClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula firstLink).formula.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula secondLink).formula.zipIdx)
    (positionEq :
      firstClause.position = secondClause.position) :
    firstLink = secondLink := by
  by_contra different
  have firstBounded :=
    retainedCarrierClausePosition_bounded wellFormed degree isLocal
      firstMem firstClauseMember
  have secondBounded :=
    retainedCarrierClausePosition_bounded wellFormed degree isLocal
      secondMem secondClauseMember
  have separatedContradiction
      (separated :
        ClosedGridRectanglesSeparated
          (drawingCompleteCarrierLinkRectangleLower
            (PeriodicCNF.incidenceGraph formula) firstLink)
          (drawingCompleteCarrierLinkRectangleUpper
            (PeriodicCNF.incidenceGraph formula) firstLink)
          (drawingCompleteCarrierLinkRectangleLower
            (PeriodicCNF.incidenceGraph formula) secondLink)
          (drawingCompleteCarrierLinkRectangleUpper
            (PeriodicCNF.incidenceGraph formula) secondLink)) :
      False :=
    (ne_of_inClosedGridRectangles_of_separated
      firstBounded secondBounded separated) positionEq
  by_cases perpendicular :
      CarrierLinksPerpendicular firstLink secondLink
  · exact separatedContradiction
      (retainedDrawingCompleteCarrierLink_rectanglesSeparated_of_perpendicular
        wellFormed degree isLocal firstMem secondMem perpendicular)
  · by_cases sameKey :
        firstLink.first.carrierKey =
          secondLink.first.carrierKey
    · rcases
        retainedDrawingCompleteCarrierLinks_same_key_orderCoordinate
          wellFormed degree isLocal firstMem secondMem
          different sameKey with
        firstBeforeSecond | secondBeforeFirst
      · by_cases shared : firstLink.second = secondLink.first
        · have firstFormulaMember := firstClauseMember
          have secondFormulaMember := secondClauseMember
          rw [retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula
            wellFormed degree isLocal firstMem] at firstFormulaMember
          rw [retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula
            wellFormed degree isLocal secondMem] at secondFormulaMember
          exact
            (retainedCarrierClausePosition_ne_of_shared_endpoint
              wellFormed degree isLocal
              firstMem secondMem shared
              firstFormulaMember secondFormulaMember) positionEq
        · exact separatedContradiction
            (retainedDrawingCompleteCarrierLinks_rectanglesSeparated_of_order_of_ne
              wellFormed degree isLocal firstMem secondMem
              sameKey firstBeforeSecond shared)
      · by_cases shared : secondLink.second = firstLink.first
        · have firstFormulaMember := firstClauseMember
          have secondFormulaMember := secondClauseMember
          rw [retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula
            wellFormed degree isLocal firstMem] at firstFormulaMember
          rw [retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula
            wellFormed degree isLocal secondMem] at secondFormulaMember
          exact
            (retainedCarrierClausePosition_ne_of_shared_endpoint
              wellFormed degree isLocal
              secondMem firstMem shared
              secondFormulaMember firstFormulaMember) positionEq.symm
        · exact separatedContradiction
            ((retainedDrawingCompleteCarrierLinks_rectanglesSeparated_of_order_of_ne
              wellFormed degree isLocal secondMem firstMem
              sameKey.symm secondBeforeFirst shared).symm)
    · exact separatedContradiction
        (retainedDrawingCompleteCarrierLink_rectanglesSeparated_of_parallel_key_ne
          wellFormed degree isLocal firstMem secondMem
          perpendicular sameKey)

/-- At the metadata level, equal positions from two carrier clauses identify
the same carrier component. -/
theorem retainedCarrierComponents_eq_of_clause_position_eq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (first second : DrawingPlanarSATClauseMetadata Variable)
    (firstValid : first.RetainedValid formula)
    (secondValid : second.RetainedValid formula)
    (firstLink secondLink : EqualityLink CarrierNode)
    (firstCarrier :
      first.source.component = .carrier firstLink)
    (secondCarrier :
      second.source.component = .carrier secondLink)
    (positionEq :
      first.clause.position = second.clause.position) :
    first.source.component = second.source.component := by
  rcases first with ⟨firstClause, firstSource⟩
  rcases firstSource.exists_eq_carrier_of_component_eq
      firstLink firstCarrier with
    ⟨firstClauseIndex, firstSourceEq⟩
  subst firstSource
  rcases second with ⟨secondClause, secondSource⟩
  rcases secondSource.exists_eq_carrier_of_component_eq
      secondLink secondCarrier with
    ⟨secondClauseIndex, secondSourceEq⟩
  subst secondSource
  have firstClauseMember :=
    (⟨firstClause, .carrier firstLink firstClauseIndex⟩ :
      DrawingPlanarSATClauseMetadata Variable)
      |>.retainedLocalClauseMember
        wellFormed degree isLocal firstValid
  have secondClauseMember :=
    (⟨secondClause, .carrier secondLink secondClauseIndex⟩ :
      DrawingPlanarSATClauseMetadata Variable)
      |>.retainedLocalClauseMember
        wellFormed degree isLocal secondValid
  have linksEq :=
    retainedCarrierLinks_eq_of_clause_position_eq
      wellFormed degree isLocal
      firstValid.1 secondValid.1
      firstClauseMember secondClauseMember positionEq
  subst secondLink
  rfl

end LeanTrominoes.PeriodicOrthocrossing
