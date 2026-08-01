import LeanTrominoes.PeriodicEightOccurrenceSplitCyclePlanarity
import LeanTrominoes.OrthogonalPolylineBoundingBox

/-!
# Macrocell separation of positioned occurrence-splitting cycles

Every Figure 7 implication route lies in the inner `12 × 12` square of its
`24 × 24` occurrence-splitting macrocell.  Since source positions are
refined by factor 36, cycles centered at distinct source positions are
strictly contact-free.  Together with the local Figure 7 certificate, this
gives complete pairwise route separation across the flattened cycle suffix,
assuming only injectivity of source positions on atoms that actually occur.
-/

namespace LeanTrominoes
namespace OccurrenceSplitRing

open PlanarThreeSAT

/-- Every local implication-clause port lies in the inner square. -/
theorem cycleClausePosition_inClosedGridRectangle
    (vertex : RingVertex) :
    InClosedGridRectangle (6, 6) (18, 18)
      (cycleClausePosition vertex) := by
  cases vertex with
  | separator => native_decide
  | port port =>
      cases port <;> native_decide

/-- Every implication clause in the local Figure 7 presentation has its
vertex in the inner square. -/
theorem cycleFormula_clausePosition_inClosedGridRectangle
    {clause : EmbeddedClause RingVertex}
    (clauseMember : clause ∈ cycleFormula) :
    InClosedGridRectangle (6, 6) (18, 18)
      clause.position := by
  rw [cycleFormula] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨vertex, _vertexMember, rfl⟩
  exact cycleClausePosition_inClosedGridRectangle vertex

/-- Every local implication-cycle variable lies in the inner square. -/
theorem ringVariablePosition_inClosedGridRectangle
    (vertex : RingVertex) :
    InClosedGridRectangle (6, 6) (18, 18)
      (ringVariablePosition vertex) := by
  cases vertex with
  | separator => native_decide
  | port port =>
      cases port <;> native_decide

/-- Both endpoints of every local implication route lie in the inner
square; invalid literal indices select the empty route. -/
theorem cycleRoute_inClosedGridRectangle
    (vertex : RingVertex)
    (literalIndex : Nat)
    {point : Cell}
    (pointMember : point ∈ cycleRoute vertex literalIndex) :
    InClosedGridRectangle (6, 6) (18, 18) point := by
  rcases literalIndex with _ | literalIndex
  · simp [cycleRoute] at pointMember
    rcases pointMember with rfl | rfl
    · exact cycleClausePosition_inClosedGridRectangle vertex
    · exact ringVariablePosition_inClosedGridRectangle vertex
  · rcases literalIndex with _ | literalIndex
    · simp [cycleRoute] at pointMember
      rcases pointMember with rfl | rfl
      · exact cycleClausePosition_inClosedGridRectangle vertex
      · exact
          ringVariablePosition_inClosedGridRectangle vertex.next
    · simp [cycleRoute] at pointMember

/-- Every point selected by the total local implication-route lookup lies
inside the inner square; invalid indices select the empty route. -/
theorem cycleRoutes_inClosedGridRectangle
    (clauseIndex literalIndex : Nat)
    {point : Cell}
    (pointMember :
      point ∈ cycleRoutes clauseIndex literalIndex) :
    InClosedGridRectangle (6, 6) (18, 18) point := by
  unfold cycleRoutes at pointMember
  split at pointMember
  · exact
      cycleRoute_inClosedGridRectangle
        (presentedCycleVertices.getD clauseIndex .separator)
        literalIndex pointMember
  · simp at pointMember

end OccurrenceSplitRing

namespace PeriodicEightOccurrenceSplitPositioned

open OccurrenceSplitRing
open PlanarThreeSAT

/-- Lower corner of the inner route-containing square of one positioned
implication ring. -/
def positionedCycleRouteLower
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) : Cell :=
  Cell.add (macroOrigin sourcePlacement atom) (6, 6)

/-- Upper corner of the inner route-containing square of one positioned
implication ring. -/
def positionedCycleRouteUpper
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) : Cell :=
  Cell.add (macroOrigin sourcePlacement atom) (18, 18)

/-- Every positioned Figure 7 ring-variable vertex lies in the same inner
macrocell square as its implication routes. -/
theorem positionedCycleRingVertex_inClosedGridRectangle
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable)
    (vertex : RingVertex) :
    InClosedGridRectangle
      (positionedCycleRouteLower sourcePlacement atom)
      (positionedCycleRouteUpper sourcePlacement atom)
      ((placement sourcePlacement).position
        (PeriodicEightOccurrenceSplit.ringCopy atom vertex)) := by
  rw [placement_copy_eq_translatedCycleVariablePosition]
  change
    InClosedGridRectangle
      (positionedCycleRouteLower sourcePlacement atom)
      (positionedCycleRouteUpper sourcePlacement atom)
      (Cell.add (macroOrigin sourcePlacement atom)
        (ringVariablePosition vertex))
  have localBounded :=
    ringVariablePosition_inClosedGridRectangle vertex
  rcases originEq : macroOrigin sourcePlacement atom with
    ⟨originX, originY⟩
  rcases positionEq : ringVariablePosition vertex with
    ⟨pointX, pointY⟩
  simp only [positionedCycleRouteLower,
    positionedCycleRouteUpper, InClosedGridRectangle,
    originEq, positionEq, Cell.add] at localBounded ⊢
  omega

/-- Every genuine positioned implication-clause vertex lies in its atom's
inner macrocell square. -/
theorem positionedCycleClausePosition_inClosedGridRectangle
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (cycleClausesFor sourcePlacement atom).zipIdx) :
    InClosedGridRectangle
      (positionedCycleRouteLower sourcePlacement atom)
      (positionedCycleRouteUpper sourcePlacement atom)
      clause.position := by
  rw [cycleClausesFor_eq_cycleFormula,
    List.zipIdx_map] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedClause, taggedClauseMember,
      taggedClauseEqual⟩
  have positionedClauseEqual :
      clause =
        positionedLocalCycleClause
          sourcePlacement atom taggedClause.1 :=
    (congrArg Prod.fst taggedClauseEqual).symm
  subst clause
  have localBounded :=
    cycleFormula_clausePosition_inClosedGridRectangle
      (List.fst_mem_of_mem_zipIdx taggedClauseMember)
  rcases originEq : macroOrigin sourcePlacement atom with
    ⟨originX, originY⟩
  rcases positionEq : taggedClause.1.position with
    ⟨pointX, pointY⟩
  simp only [positionedCycleRouteLower,
    positionedCycleRouteUpper, positionedLocalCycleClause,
    InClosedGridRectangle, originEq, positionEq, Cell.add]
    at localBounded ⊢
  omega

/-- Translation puts every point of a positioned implication route in its
atom's inner macrocell square. -/
theorem positionedCycleRoutes_inClosedGridRectangle
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable)
    (clauseIndex literalIndex : Nat)
    {point : Cell}
    (pointMember :
      point ∈
        positionedCycleRoutes sourcePlacement atom
          clauseIndex literalIndex) :
    InClosedGridRectangle
      (positionedCycleRouteLower sourcePlacement atom)
      (positionedCycleRouteUpper sourcePlacement atom)
      point := by
  change
    point ∈
      (cycleRoutes clauseIndex literalIndex).map
        (Cell.add (macroOrigin sourcePlacement atom))
    at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localPointMember, rfl⟩
  have localBounded :=
    cycleRoutes_inClosedGridRectangle
      clauseIndex literalIndex localPointMember
  rcases originEq : macroOrigin sourcePlacement atom with
    ⟨originX, originY⟩
  rcases localPoint with ⟨pointX, pointY⟩
  simp only [positionedCycleRouteLower,
    positionedCycleRouteUpper, InClosedGridRectangle,
    originEq, Cell.add] at localBounded ⊢
  omega

/-- Distinct integer source positions yield strictly separated inner cycle
squares after the factor-36 refinement. -/
theorem positionedCycleRouteRectangles_separated_of_positions_ne
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {firstAtom secondAtom : Variable}
    (positionsDifferent :
      sourcePlacement.position firstAtom ≠
        sourcePlacement.position secondAtom) :
    ClosedGridRectanglesSeparated
      (positionedCycleRouteLower sourcePlacement firstAtom)
      (positionedCycleRouteUpper sourcePlacement firstAtom)
      (positionedCycleRouteLower sourcePlacement secondAtom)
      (positionedCycleRouteUpper sourcePlacement secondAtom) := by
  rcases positionEqFirst :
      sourcePlacement.position firstAtom with
    ⟨firstX, firstY⟩
  rcases positionEqSecond :
      sourcePlacement.position secondAtom with
    ⟨secondX, secondY⟩
  have coordinateDifferent :
      firstX ≠ secondX ∨ firstY ≠ secondY := by
    by_cases horizontalDifferent : firstX ≠ secondX
    · exact Or.inl horizontalDifferent
    · apply Or.inr
      intro verticalEqual
      apply positionsDifferent
      rw [positionEqFirst, positionEqSecond]
      exact Prod.ext
        (not_ne_iff.mp horizontalDifferent) verticalEqual
  simp only [positionedCycleRouteLower,
    positionedCycleRouteUpper, macroOrigin,
    refinementScale, ClosedGridRectanglesSeparated,
    positionEqFirst, positionEqSecond,
    Cell.add, Cell.sub, Cell.scale]
  rcases coordinateDifferent with
      horizontalDifferent | verticalDifferent <;>
    omega

/-- Positioned implication routes belonging to distinct source positions
are contact-free. -/
theorem positionedCycleRoutes_strictlyAvoid_of_positions_ne
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {firstAtom secondAtom : Variable}
    (positionsDifferent :
      sourcePlacement.position firstAtom ≠
        sourcePlacement.position secondAtom)
    (firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex : Nat) :
    EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther
      (positionedCycleRoutes sourcePlacement firstAtom
        firstClauseIndex firstLiteralIndex)
      (positionedCycleRoutes sourcePlacement secondAtom
        secondClauseIndex secondLiteralIndex) := by
  exact
    routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
      (fun point pointMember =>
        positionedCycleRoutes_inClosedGridRectangle
          sourcePlacement firstAtom
          firstClauseIndex firstLiteralIndex pointMember)
      (fun point pointMember =>
        positionedCycleRoutes_inClosedGridRectangle
          sourcePlacement secondAtom
          secondClauseIndex secondLiteralIndex pointMember)
      (positionedCycleRouteRectangles_separated_of_positions_ne
        sourcePlacement positionsDifferent)

/-- A ring-variable vertex in one source macrocell cannot lie in the
interior of a cycle-route segment in a distinct source macrocell. -/
theorem positionedCycleRingVertex_avoidsRouteInterior_of_positions_ne
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {vertexAtom routeAtom : Variable}
    (positionsDifferent :
      sourcePlacement.position vertexAtom ≠
        sourcePlacement.position routeAtom)
    (vertex : RingVertex)
    (clauseIndex literalIndex : Nat)
    {segment : GridSegment}
    (segmentMember :
      segment ∈ gridPolylineSegments
        (positionedCycleRoutes sourcePlacement routeAtom
          clauseIndex literalIndex)) :
    ¬segment.InteriorContains
      ((placement sourcePlacement).position
        (PeriodicEightOccurrenceSplit.ringCopy vertexAtom vertex)) := by
  have endpoints :=
    gridPolylineSegments_endpoints_mem segmentMember
  exact
    not_interiorContains_of_inClosedGridRectangles_of_separated
      (positionedCycleRingVertex_inClosedGridRectangle
        sourcePlacement vertexAtom vertex)
      (positionedCycleRoutes_inClosedGridRectangle
        sourcePlacement routeAtom clauseIndex literalIndex
        endpoints.1)
      (positionedCycleRoutes_inClosedGridRectangle
        sourcePlacement routeAtom clauseIndex literalIndex
        endpoints.2)
      (positionedCycleRouteRectangles_separated_of_positions_ne
        sourcePlacement positionsDifferent)

/-- A cycle-clause vertex in one source macrocell cannot lie in the
interior of a cycle-route segment in a distinct source macrocell. -/
theorem positionedCycleClauseVertex_avoidsRouteInterior_of_positions_ne
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {vertexAtom routeAtom : Variable}
    (positionsDifferent :
      sourcePlacement.position vertexAtom ≠
        sourcePlacement.position routeAtom)
    {vertexClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {vertexClauseIndex : Nat}
    (vertexClauseMember :
      (vertexClause, vertexClauseIndex) ∈
        (cycleClausesFor sourcePlacement vertexAtom).zipIdx)
    (routeClauseIndex literalIndex : Nat)
    {segment : GridSegment}
    (segmentMember :
      segment ∈ gridPolylineSegments
        (positionedCycleRoutes sourcePlacement routeAtom
          routeClauseIndex literalIndex)) :
    ¬segment.InteriorContains vertexClause.position := by
  have endpoints :=
    gridPolylineSegments_endpoints_mem segmentMember
  exact
    not_interiorContains_of_inClosedGridRectangles_of_separated
      (positionedCycleClausePosition_inClosedGridRectangle
        sourcePlacement vertexAtom vertexClauseMember)
      (positionedCycleRoutes_inClosedGridRectangle
        sourcePlacement routeAtom routeClauseIndex literalIndex
        endpoints.1)
      (positionedCycleRoutes_inClosedGridRectangle
        sourcePlacement routeAtom routeClauseIndex literalIndex
        endpoints.2)
      (positionedCycleRouteRectangles_separated_of_positions_ne
        sourcePlacement positionsDifferent)

/-- Every explicit ring-copy vertex avoids every genuine route segment in
the flattened implication-cycle suffix.  The owning atom's local Figure 7
certificate handles its own ring; strict macrocell separation handles every
other ring. -/
theorem allCycleRingVertex_avoidsRouteInterior
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (positionInjective :
      ∀ {firstAtom secondAtom : Variable},
        firstAtom ∈
            PeriodicThreeSATThree.sourceVariables source.erase →
          secondAtom ∈
            PeriodicThreeSATThree.sourceVariables source.erase →
          sourcePlacement.position firstAtom =
              sourcePlacement.position secondAtom →
            firstAtom = secondAtom)
    {vertexAtom : Variable}
    (vertexAtomMember :
      vertexAtom ∈
        PeriodicThreeSATThree.sourceVariables source.erase)
    (vertex : RingVertex)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {cycleIndex : Nat}
    (clauseMember :
      (clause, cycleIndex) ∈
        (allCycleClauses source sourcePlacement).zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    {segment : GridSegment}
    (segmentMember :
      segment ∈ gridPolylineSegments
        (allCycleRoutes source sourcePlacement
          cycleIndex literalIndex)) :
    ¬segment.InteriorContains
      ((placement sourcePlacement).position
        (PeriodicEightOccurrenceSplit.ringCopy
          vertexAtom vertex)) := by
  rcases allCycleClauseMetadata_lookup_valid
      source sourcePlacement clauseMember with
    ⟨metadata, metadataLookup, clauseEqual,
      localClauseMember⟩
  have routeAtomMember :=
    allCycleClauseMetadata_lookup_atom_mem
      source sourcePlacement metadataLookup
  by_cases atomsEqual : vertexAtom = metadata.atom
  · have localAvoid :=
      positionedCycleRingVertex_avoidsRouteInterior
        sourcePlacement metadata.atom vertex
        localClauseMember
        (clauseEqual ▸ literalMember)
        (by
          simpa [allCycleRoutes, metadataLookup] using segmentMember)
    simpa [atomsEqual] using localAvoid
  · have positionsDifferent :
      sourcePlacement.position vertexAtom ≠
        sourcePlacement.position metadata.atom := by
      intro positionsEqual
      exact atomsEqual
        (positionInjective vertexAtomMember routeAtomMember
          positionsEqual)
    apply
      positionedCycleRingVertex_avoidsRouteInterior_of_positions_ne
        sourcePlacement positionsDifferent vertex
        metadata.localClauseIndex literalIndex
    simpa [allCycleRoutes, metadataLookup] using segmentMember

/-- Every genuine clause vertex in the flattened implication-cycle suffix
avoids every genuine route interior in that suffix.  Same-atom interactions
come from the exact local Figure 7 certificate; different atoms are strictly
macrocell-separated. -/
theorem allCycleClauseVertex_avoidsRouteInterior
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (positionInjective :
      ∀ {firstAtom secondAtom : Variable},
        firstAtom ∈
            PeriodicThreeSATThree.sourceVariables source.erase →
          secondAtom ∈
            PeriodicThreeSATThree.sourceVariables source.erase →
          sourcePlacement.position firstAtom =
              sourcePlacement.position secondAtom →
            firstAtom = secondAtom)
    {vertexClause routeClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {vertexCycleIndex routeCycleIndex : Nat}
    (vertexClauseMember :
      (vertexClause, vertexCycleIndex) ∈
        (allCycleClauses source sourcePlacement).zipIdx)
    (routeClauseMember :
      (routeClause, routeCycleIndex) ∈
        (allCycleClauses source sourcePlacement).zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ routeClause.literals.zipIdx)
    {segment : GridSegment}
    (segmentMember :
      segment ∈ gridPolylineSegments
        (allCycleRoutes source sourcePlacement
          routeCycleIndex literalIndex)) :
    ¬segment.InteriorContains vertexClause.position := by
  rcases allCycleClauseMetadata_lookup_valid
      source sourcePlacement vertexClauseMember with
    ⟨vertexMetadata, vertexMetadataLookup,
      vertexClauseEqual, localVertexClauseMember⟩
  rcases allCycleClauseMetadata_lookup_valid
      source sourcePlacement routeClauseMember with
    ⟨routeMetadata, routeMetadataLookup,
      routeClauseEqual, localRouteClauseMember⟩
  by_cases atomsEqual :
      vertexMetadata.atom = routeMetadata.atom
  · have localRouteClauseMember' :
      (routeMetadata.clause,
          routeMetadata.localClauseIndex) ∈
        (cycleClausesFor sourcePlacement
          vertexMetadata.atom).zipIdx := by
      simpa [atomsEqual] using localRouteClauseMember
    have localAvoid :=
      positionedCycleClauseVertex_avoidsRouteInterior
        sourcePlacement vertexMetadata.atom
        localVertexClauseMember localRouteClauseMember'
        (routeClauseEqual ▸ literalMember)
        (by
          simpa [allCycleRoutes, routeMetadataLookup,
            atomsEqual] using
            segmentMember)
    simpa [vertexClauseEqual] using localAvoid
  · have vertexAtomMember :=
      allCycleClauseMetadata_lookup_atom_mem
        source sourcePlacement vertexMetadataLookup
    have routeAtomMember :=
      allCycleClauseMetadata_lookup_atom_mem
        source sourcePlacement routeMetadataLookup
    have positionsDifferent :
        sourcePlacement.position vertexMetadata.atom ≠
          sourcePlacement.position routeMetadata.atom := by
      intro positionsEqual
      exact atomsEqual
        (positionInjective vertexAtomMember routeAtomMember
          positionsEqual)
    have macroAvoid :=
      positionedCycleClauseVertex_avoidsRouteInterior_of_positions_ne
        sourcePlacement positionsDifferent localVertexClauseMember
        routeMetadata.localClauseIndex literalIndex
        (by
          simpa [allCycleRoutes, routeMetadataLookup] using
            segmentMember)
    simpa [vertexClauseEqual] using macroAvoid

/-- The flattened implication-cycle family is pairwise continuously
separated.  Same-atom pairs use the exact local Figure 7 certificate;
different-atom pairs use strict macrocell separation. -/
theorem allCycleRoutes_avoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (positionInjective :
      ∀ {firstAtom secondAtom : Variable},
        firstAtom ∈
            PeriodicThreeSATThree.sourceVariables source.erase →
          secondAtom ∈
            PeriodicThreeSATThree.sourceVariables source.erase →
          sourcePlacement.position firstAtom =
              sourcePlacement.position secondAtom →
            firstAtom = secondAtom)
    {firstClause secondClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {firstCycleIndex secondCycleIndex : Nat}
    (firstClauseMember :
      (firstClause, firstCycleIndex) ∈
        (allCycleClauses source sourcePlacement).zipIdx)
    (secondClauseMember :
      (secondClause, secondCycleIndex) ∈
        (allCycleClauses source sourcePlacement).zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral
        (ThreeOccurrenceVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (incidencesDistinct :
      firstCycleIndex ≠ secondCycleIndex ∨
        firstLiteralIndex ≠ secondLiteralIndex) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (allCycleRoutes source sourcePlacement
        firstCycleIndex firstLiteralIndex)
      (allCycleRoutes source sourcePlacement
        secondCycleIndex secondLiteralIndex) := by
  rcases allCycleClauseMetadata_lookup_valid
      source sourcePlacement firstClauseMember with
    ⟨firstMetadata, firstMetadataLookup,
      _firstClauseEqual, _firstLocalClauseMember⟩
  rcases allCycleClauseMetadata_lookup_valid
      source sourcePlacement secondClauseMember with
    ⟨secondMetadata, secondMetadataLookup,
      _secondClauseEqual, _secondLocalClauseMember⟩
  by_cases atomsEqual :
      firstMetadata.atom = secondMetadata.atom
  · apply allCycleRoutes_avoidEachOther_of_same_atom
      source sourcePlacement
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember
    · simp [allCycleClauseAtom?, firstMetadataLookup,
        secondMetadataLookup, atomsEqual]
    · exact incidencesDistinct
  · have firstAtomMember :=
      allCycleClauseMetadata_lookup_atom_mem
        source sourcePlacement firstMetadataLookup
    have secondAtomMember :=
      allCycleClauseMetadata_lookup_atom_mem
        source sourcePlacement secondMetadataLookup
    have positionsDifferent :
        sourcePlacement.position firstMetadata.atom ≠
          sourcePlacement.position secondMetadata.atom := by
      intro positionsEqual
      exact atomsEqual
        (positionInjective firstAtomMember secondAtomMember
          positionsEqual)
    have strict :=
      positionedCycleRoutes_strictlyAvoid_of_positions_ne
        sourcePlacement positionsDifferent
        firstMetadata.localClauseIndex firstLiteralIndex
        secondMetadata.localClauseIndex secondLiteralIndex
    simpa [allCycleRoutes, firstMetadataLookup,
      secondMetadataLookup] using
        strict.toRoutesAvoidEachOther

end PeriodicEightOccurrenceSplitPositioned
end LeanTrominoes
