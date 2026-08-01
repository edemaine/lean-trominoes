import LeanTrominoes.PeriodicCNFPlanarEightOccurrenceSplitPositioned
import LeanTrominoes.OccurrenceSplitRingCycleDrawing
import LeanTrominoes.EmbeddedCNFIncidenceDrawingRenaming
import LeanTrominoes.EmbeddedCNFIncidenceDrawingPlanarity

/-!
# Certified Figure 7 cycles inside positioned occurrence splitting

This module identifies each atom's appended implication clauses with the
standalone Figure 7 cycle drawing.  The correspondence is definitional:
translate the local coordinates by the atom's macrocell origin and rename
each compass `Port` to the corresponding fixed occurrence copy.

Consequently the translated local routes carry the complete finite
endpoint, orthogonality, and continuous-planarity certificate at every
input-dependent atom position.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplitPositioned

open OccurrenceSplitRing
open PlanarThreeSAT

/-- Translate and rename one local Figure 7 implication clause. -/
def positionedLocalCycleClause
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable)
    (clause : EmbeddedClause RingVertex) :
    PositionedPeriodicClause
      (ThreeOccurrenceVariable Variable) where
  position :=
    Cell.add
      (macroOrigin sourcePlacement atom) clause.position
  literals := periodicCycleClause atom clause

/-- One atom's positioned implication clauses are exactly the translated,
renamed local cycle template. -/
theorem cycleClausesFor_eq_cycleFormula
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) :
    cycleClausesFor sourcePlacement atom =
      cycleFormula.map
        (positionedLocalCycleClause
          sourcePlacement atom) := by
  rfl

/-- The certified translated local routes used for one atom's cycle block. -/
def positionedCycleRoutes
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    (translatedCycleDrawing
      (macroOrigin sourcePlacement atom)).routes
        clauseIndex literalIndex

/-- Every per-atom cycle route family inherits the complete local
certificate. -/
theorem positionedCycleDrawing_isValid
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) :
    (translatedCycleDrawing
      (macroOrigin sourcePlacement atom)).IsValid :=
  translatedCycleDrawing_isValid _

/-- The refined placement of every source or separator copy agrees with the
translated local cycle drawing's variable vertex. -/
theorem placement_copy_eq_translatedCycleVariablePosition
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (vertex : RingVertex) :
    (placement sourcePlacement).position
        (PeriodicEightOccurrenceSplit.ringCopy atom vertex) =
      (translatedCycleDrawing
        (macroOrigin sourcePlacement atom)).variablePosition
          vertex := by
  cases vertex with
  | separator => rfl
  | port port =>
      cases port <;> rfl

/-- One positioned implication ring, including its translated coordinates
and input-dependent occurrence-copy names, as a finite incidence drawing. -/
def positionedCycleDrawing
    {Variable : Type*} [DecidableEq Variable]
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) :
    EmbeddedCNFIncidenceDrawing
      (ThreeOccurrenceVariable Variable) :=
  (translatedCycleDrawing
      (macroOrigin sourcePlacement atom)).rename
    (PeriodicEightOccurrenceSplit.ringCopy atom)
    (placement sourcePlacement).position

/-- The positioned finite drawing uses the same presentation-indexed route
family as the global occurrence-splitting construction. -/
@[simp]
theorem positionedCycleDrawing_routes
    {Variable : Type*} [DecidableEq Variable]
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) :
    (positionedCycleDrawing sourcePlacement atom).routes =
      positionedCycleRoutes sourcePlacement atom := by
  rfl

/-- Translation and injective occurrence-copy renaming preserve the complete
finite planarity certificate of each Figure 7 implication ring. -/
theorem renamedPositionedCycleDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) :
    (positionedCycleDrawing sourcePlacement atom).IsValid := by
  apply
    EmbeddedCNFIncidenceDrawing.isValid_rename
      (PeriodicEightOccurrenceSplit.ringCopy atom)
      (placement sourcePlacement).position
  · intro first _firstMember second _secondMember equal
    exact
      PeriodicEightOccurrenceSplit.ringCopy_injective atom equal
  · intro vertex _vertexMember
    exact
      placement_copy_eq_translatedCycleVariablePosition
        sourcePlacement atom vertex
  · exact
      translatedCycleDrawing_isValid
        (macroOrigin sourcePlacement atom)

/-- Every variable vertex of one positioned Figure 7 ring avoids the
interior of every genuine route segment in that ring. -/
theorem positionedCycleRingVertex_avoidsRouteInterior
    {Variable : Type*} [DecidableEq Variable]
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable)
    (vertex : RingVertex)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (cycleClausesFor sourcePlacement atom).zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    {segment : GridSegment}
    (segmentMember :
      segment ∈ gridPolylineSegments
        (positionedCycleRoutes sourcePlacement atom
          clauseIndex literalIndex)) :
    ¬segment.InteriorContains
      ((placement sourcePlacement).position
        (PeriodicEightOccurrenceSplit.ringCopy atom vertex)) := by
  rw [cycleClausesFor_eq_cycleFormula,
    List.zipIdx_map] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedClause, taggedClauseMember,
      taggedClauseEqual⟩
  have clauseIndexEqual :
      taggedClause.2 = clauseIndex :=
    congrArg Prod.snd taggedClauseEqual
  have positionedClauseEqual :
      clause =
        positionedLocalCycleClause
          sourcePlacement atom taggedClause.1 :=
    (congrArg Prod.fst taggedClauseEqual).symm
  subst clauseIndex
  subst clause
  change
    (literal, literalIndex) ∈
      (taggedClause.1.literals.map fun sourceLiteral =>
        ⟨PeriodicEightOccurrenceSplit.ringCopy
            atom sourceLiteral.1,
          (0, 0), sourceLiteral.2⟩).zipIdx
    at literalMember
  rw [List.zipIdx_map] at literalMember
  rcases List.mem_map.mp literalMember with
    ⟨taggedLiteral, taggedLiteralMember,
      taggedLiteralEqual⟩
  have literalIndexEqual :
      taggedLiteral.2 = literalIndex :=
    congrArg Prod.snd taggedLiteralEqual
  subst literalIndex
  let offset := macroOrigin sourcePlacement atom
  have localVariableMember :
      vertex ∈ (translatedCycleDrawing offset).variableVertices := by
    change vertex ∈ cycleDrawing.variableVertices
    cases vertex with
    | separator => native_decide
    | port port =>
        cases port <;> native_decide
  have translatedVertexMember :
      (translatedCycleDrawing offset).variablePosition vertex ∈
        (translatedCycleDrawing offset).vertexPositions := by
    exact List.mem_append_left _
      (List.mem_map.mpr
        ⟨vertex, localVariableMember, rfl⟩)
  have translatedClauseMember :
      (taggedClause.1.translate offset,
          taggedClause.2) ∈
        (translatedCycleDrawing offset).formula.zipIdx := by
    change
      (taggedClause.1.translate offset,
          taggedClause.2) ∈
        (cycleFormula.map
          (EmbeddedClause.translate offset)).zipIdx
    rw [List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨taggedClause, taggedClauseMember, rfl⟩
  have avoids :=
    (translatedCycleDrawing offset)
      |>.embeddedVertex_avoidsRouteInterior_of_members
        (translatedCycleDrawing_isValid offset).2.2
        translatedVertexMember
        translatedClauseMember taggedLiteralMember segmentMember
  rw [placement_copy_eq_translatedCycleVariablePosition]
  exact avoids

/-- Every genuine route in a positioned implication ring is simple. -/
theorem positionedCycleRoute_isSimple
    {Variable : Type*} [DecidableEq Variable]
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (cycleClausesFor sourcePlacement atom).zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    LocalIncidenceDrawing.RouteIsSimple
      (positionedCycleRoutes
        sourcePlacement atom clauseIndex literalIndex) := by
  rw [cycleClausesFor_eq_cycleFormula,
    List.zipIdx_map] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedClause, taggedClauseMember,
      taggedClauseEqual⟩
  have clauseIndexEqual :
      taggedClause.2 = clauseIndex :=
    congrArg Prod.snd taggedClauseEqual
  have positionedClauseEqual :
      clause =
        positionedLocalCycleClause
          sourcePlacement atom taggedClause.1 :=
    (congrArg Prod.fst taggedClauseEqual).symm
  subst clauseIndex
  subst clause
  change
    (literal, literalIndex) ∈
      (taggedClause.1.literals.map fun sourceLiteral =>
        ⟨PeriodicEightOccurrenceSplit.ringCopy
            atom sourceLiteral.1,
          (0, 0), sourceLiteral.2⟩).zipIdx
    at literalMember
  rw [List.zipIdx_map] at literalMember
  rcases List.mem_map.mp literalMember with
    ⟨taggedLiteral, taggedLiteralMember,
      taggedLiteralEqual⟩
  have literalIndexEqual :
      taggedLiteral.2 = literalIndex :=
    congrArg Prod.snd taggedLiteralEqual
  subst literalIndex
  let offset := macroOrigin sourcePlacement atom
  have translatedClauseMember :
      (taggedClause.1.translate offset,
          taggedClause.2) ∈
        (translatedCycleDrawing offset).formula.zipIdx := by
    change
      (taggedClause.1.translate offset,
          taggedClause.2) ∈
        (cycleFormula.map
          (EmbeddedClause.translate offset)).zipIdx
    rw [List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨taggedClause, taggedClauseMember, rfl⟩
  have simple :=
    (translatedCycleDrawing offset)
      |>.embeddedRoute_isSimple_of_members
        (translatedCycleDrawing_isValid offset).2.2
        translatedClauseMember taggedLiteralMember
  simpa [positionedCycleRoutes, offset] using simple

/-- Distinct genuine incidences in one positioned implication ring satisfy
the complete continuous two-route separation predicate. -/
theorem positionedCycleRoutes_avoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable)
    {firstClause secondClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (cycleClausesFor sourcePlacement atom).zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (cycleClausesFor sourcePlacement atom).zipIdx)
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
      firstClauseIndex ≠ secondClauseIndex ∨
        firstLiteralIndex ≠ secondLiteralIndex) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (positionedCycleRoutes
        sourcePlacement atom
        firstClauseIndex firstLiteralIndex)
      (positionedCycleRoutes
        sourcePlacement atom
        secondClauseIndex secondLiteralIndex) := by
  rw [cycleClausesFor_eq_cycleFormula,
    List.zipIdx_map] at firstClauseMember secondClauseMember
  rcases List.mem_map.mp firstClauseMember with
    ⟨firstTaggedClause, firstTaggedClauseMember,
      firstTaggedClauseEqual⟩
  rcases List.mem_map.mp secondClauseMember with
    ⟨secondTaggedClause, secondTaggedClauseMember,
      secondTaggedClauseEqual⟩
  have firstClauseIndexEqual :
      firstTaggedClause.2 = firstClauseIndex :=
    congrArg Prod.snd firstTaggedClauseEqual
  have secondClauseIndexEqual :
      secondTaggedClause.2 = secondClauseIndex :=
    congrArg Prod.snd secondTaggedClauseEqual
  have firstPositionedClauseEqual :
      firstClause =
        positionedLocalCycleClause
          sourcePlacement atom firstTaggedClause.1 :=
    (congrArg Prod.fst firstTaggedClauseEqual).symm
  have secondPositionedClauseEqual :
      secondClause =
        positionedLocalCycleClause
          sourcePlacement atom secondTaggedClause.1 :=
    (congrArg Prod.fst secondTaggedClauseEqual).symm
  subst firstClauseIndex
  subst secondClauseIndex
  subst firstClause
  subst secondClause
  change
    (firstLiteral, firstLiteralIndex) ∈
      (firstTaggedClause.1.literals.map fun sourceLiteral =>
        ⟨PeriodicEightOccurrenceSplit.ringCopy
            atom sourceLiteral.1,
          (0, 0), sourceLiteral.2⟩).zipIdx
    at firstLiteralMember
  change
    (secondLiteral, secondLiteralIndex) ∈
      (secondTaggedClause.1.literals.map fun sourceLiteral =>
        ⟨PeriodicEightOccurrenceSplit.ringCopy
            atom sourceLiteral.1,
          (0, 0), sourceLiteral.2⟩).zipIdx
    at secondLiteralMember
  rw [List.zipIdx_map] at firstLiteralMember secondLiteralMember
  rcases List.mem_map.mp firstLiteralMember with
    ⟨firstTaggedLiteral, firstTaggedLiteralMember,
      firstTaggedLiteralEqual⟩
  rcases List.mem_map.mp secondLiteralMember with
    ⟨secondTaggedLiteral, secondTaggedLiteralMember,
      secondTaggedLiteralEqual⟩
  have firstLiteralIndexEqual :
      firstTaggedLiteral.2 = firstLiteralIndex :=
    congrArg Prod.snd firstTaggedLiteralEqual
  have secondLiteralIndexEqual :
      secondTaggedLiteral.2 = secondLiteralIndex :=
    congrArg Prod.snd secondTaggedLiteralEqual
  subst firstLiteralIndex
  subst secondLiteralIndex
  let offset := macroOrigin sourcePlacement atom
  have firstTranslatedClauseMember :
      (firstTaggedClause.1.translate offset,
          firstTaggedClause.2) ∈
        (translatedCycleDrawing offset).formula.zipIdx := by
    change
      (firstTaggedClause.1.translate offset,
          firstTaggedClause.2) ∈
        (cycleFormula.map
          (EmbeddedClause.translate offset)).zipIdx
    rw [List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨firstTaggedClause, firstTaggedClauseMember, rfl⟩
  have secondTranslatedClauseMember :
      (secondTaggedClause.1.translate offset,
          secondTaggedClause.2) ∈
        (translatedCycleDrawing offset).formula.zipIdx := by
    change
      (secondTaggedClause.1.translate offset,
          secondTaggedClause.2) ∈
        (cycleFormula.map
          (EmbeddedClause.translate offset)).zipIdx
    rw [List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨secondTaggedClause, secondTaggedClauseMember, rfl⟩
  have separated :=
    (translatedCycleDrawing offset)
      |>.embeddedRoutes_avoidEachOther_of_members
        (translatedCycleDrawing_isValid offset).2.2
        firstTranslatedClauseMember secondTranslatedClauseMember
        firstTaggedLiteralMember secondTaggedLiteralMember
        incidencesDistinct
  simpa [positionedCycleRoutes, offset] using separated

end PeriodicEightOccurrenceSplitPositioned
end LeanTrominoes
