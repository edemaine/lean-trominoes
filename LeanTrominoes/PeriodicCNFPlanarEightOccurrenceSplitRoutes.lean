import LeanTrominoes.PeriodicEightOccurrenceSplitPositionedCycleIndex
import LeanTrominoes.PositionedPeriodicCNFDeduplicationRoutes
import LeanTrominoes.PositionedPeriodicCNFOrthogonalIncidenceRoutes

/-!
# Endpoint-compatible routes for fixed-eight occurrence splitting

This module equips the positioned Figure 7 formula with a canonical
orthogonal route family.  It proves the exact periodic incidence endpoints
and axis alignment needed by later noncrossing ring-splicing refinements.
-/

namespace LeanTrominoes

namespace PeriodicEightOccurrenceSplitPositioned

open OccurrenceSplitRing
open PlanarThreeSAT

/-- Extract the orthogonal-polyline fact for one genuine incidence from a
finite embedded drawing's indexed orthogonality certificate. -/
theorem embeddedRoute_orthogonal_of_members
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (orthogonal : drawing.IsOrthogonal)
    {clause : EmbeddedClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ drawing.formula.zipIdx)
    {literal : Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈
        clause.literals.zipIdx) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (drawing.routes clauseIndex literalIndex) := by
  let incidence : EmbeddedCNFIncidence Variable :=
    ⟨clause, clauseIndex, literal, literalIndex⟩
  have incidenceMember :
      incidence ∈ drawing.incidences := by
    exact (mem_embeddedCNFIncidences_iff
      drawing.formula incidence).mpr
        ⟨clauseMember, literalMember⟩
  rcases List.mem_iff_get.mp incidenceMember with
    ⟨incidenceIndex, incidenceEqual⟩
  have incidenceAtEqual :
      drawing.incidenceAt incidenceIndex = incidence := by
    exact incidenceEqual
  have routeEqual :
      drawing.routeAt
          (drawing.incidenceAt incidenceIndex) =
        drawing.routes clauseIndex literalIndex := by
    rw [incidenceAtEqual]
    rfl
  have routeSegmentsOrthogonal :
      ∀ segmentIndex :
          Fin (gridPolylineSegments
            (drawing.routes
              clauseIndex literalIndex)).length,
        ((gridPolylineSegments
          (drawing.routes clauseIndex literalIndex)).get
            segmentIndex).IsAxisAligned := by
    have indexedOrthogonal :=
      orthogonal incidenceIndex
    rw [routeEqual] at indexedOrthogonal
    exact indexedOrthogonal
  apply
    (PeriodicOrthocrossing.orthogonalPolyline_iff_segments _).mpr
  intro segment segmentMember
  rcases List.mem_iff_get.mp segmentMember with
    ⟨segmentIndex, segmentEqual⟩
  exact segmentEqual ▸
    routeSegmentsOrthogonal segmentIndex

/-- The certified routes of one positioned implication ring meet the
positioned clauses and the refined fixed-copy placement exactly. -/
theorem positionedCycleRoutes_physicalRoutesMatch
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) :
    PositionedPeriodicCNF.PhysicalIncidenceRoutesMatch
      ⟨cycleClausesFor sourcePlacement atom⟩
      (placement sourcePlacement)
      (positionedCycleRoutes sourcePlacement atom) := by
  intro positionedClause clauseIndex clauseMember
    positionedLiteral literalIndex literalMember
  rw [cycleClausesFor_eq_cycleFormula,
    List.zipIdx_map] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedClause, taggedClauseMember,
      taggedClauseEqual⟩
  have clauseIndexEqual :
      taggedClause.2 = clauseIndex :=
    congrArg Prod.snd taggedClauseEqual
  have positionedClauseEqual :
      positionedClause =
        positionedLocalCycleClause
          sourcePlacement atom taggedClause.1 :=
    (congrArg Prod.fst taggedClauseEqual).symm
  subst clauseIndex
  subst positionedClause
  change
    (positionedLiteral, literalIndex) ∈
      (taggedClause.1.literals.map fun literal =>
        ⟨PeriodicEightOccurrenceSplit.ringCopy
            atom literal.1,
          (0, 0), literal.2⟩).zipIdx
    at literalMember
  rw [List.zipIdx_map] at literalMember
  rcases List.mem_map.mp literalMember with
    ⟨taggedLiteral, taggedLiteralMember,
      taggedLiteralEqual⟩
  have literalIndexEqual :
      taggedLiteral.2 = literalIndex :=
    congrArg Prod.snd taggedLiteralEqual
  have positionedLiteralEqual :
      positionedLiteral =
        ⟨PeriodicEightOccurrenceSplit.ringCopy
            atom taggedLiteral.1.1,
          (0, 0), taggedLiteral.1.2⟩ :=
    (congrArg Prod.fst taggedLiteralEqual).symm
  subst literalIndex
  subst positionedLiteral
  have localEndpoints :=
    EmbeddedCNFIncidenceDrawing.physicalRoutesMatch
      cycleDrawing cycleDrawing_routesMatch
      taggedClause.1 taggedClause.2 taggedClauseMember
      taggedLiteral.1 taggedLiteral.2 taggedLiteralMember
  constructor
  · simpa [positionedCycleRoutes,
      translatedCycleDrawing,
      EmbeddedCNFIncidenceDrawing.translate,
      positionedLocalCycleClause,
      localEndpoints.1]
  · simpa [positionedCycleRoutes,
      translatedCycleDrawing,
      EmbeddedCNFIncidenceDrawing.translate,
      PeriodicVariablePlacement.literalPosition,
      PeriodicVariablePlacement.translation,
      placement_copy_eq_translatedCycleVariablePosition,
      localEndpoints.2, Cell.add, Cell.scale]

/-- Every positioned implication clause is anchored at the zero logical
offset. -/
theorem cycleClausesFor_clauseAnchor_eq_zero
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (cycleClausesFor
          sourcePlacement atom).zipIdx) :
    PeriodicCNF.clauseAnchor clause.literals =
      (0, 0) := by
  rw [cycleClausesFor_eq_cycleFormula,
    List.zipIdx_map] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedClause, taggedClauseMember,
      taggedClauseEqual⟩
  have clauseEqual :
      clause =
        positionedLocalCycleClause
          sourcePlacement atom taggedClause.1 :=
    (congrArg Prod.fst taggedClauseEqual).symm
  subst clause
  have localClauseMember :
      taggedClause.1 ∈ cycleFormula :=
    List.fst_mem_of_mem_zipIdx taggedClauseMember
  rw [cycleFormula] at localClauseMember
  rcases List.mem_map.mp localClauseMember with
    ⟨port, _portMember, localClauseEqual⟩
  rw [← localClauseEqual]
  rfl

/-- Every literal in a positioned implication clause has zero logical
offset. -/
theorem cycleClausesFor_literal_offset_eq_zero
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (cycleClausesFor
          sourcePlacement atom).zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈
        clause.literals.zipIdx) :
    literal.offset = (0, 0) := by
  rw [cycleClausesFor_eq_cycleFormula,
    List.zipIdx_map] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedClause, _taggedClauseMember,
      taggedClauseEqual⟩
  have clauseEqual :
      clause =
        positionedLocalCycleClause
          sourcePlacement atom taggedClause.1 :=
    (congrArg Prod.fst taggedClauseEqual).symm
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
    ⟨taggedLiteral, _taggedLiteralMember,
      taggedLiteralEqual⟩
  have literalEqual :
      literal =
        ⟨PeriodicEightOccurrenceSplit.ringCopy
            atom taggedLiteral.1.1,
          (0, 0), taggedLiteral.1.2⟩ :=
    (congrArg Prod.fst taggedLiteralEqual).symm
  subst literal
  rfl

/-- Every genuine route in one positioned implication ring inherits the
translated local axis-alignment certificate. -/
theorem positionedCycleRoutes_orthogonal
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (cycleClausesFor
          sourcePlacement atom).zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈
        clause.literals.zipIdx) :
    PeriodicOrthocrossing.OrthogonalPolyline
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
  have routeOrthogonal :=
    embeddedRoute_orthogonal_of_members
      (translatedCycleDrawing offset)
      (translatedCycleDrawing_isValid offset).2.1
      translatedClauseMember taggedLiteralMember
  simpa [positionedCycleRoutes, offset] using
    routeOrthogonal

/-- The indexed union of all certified cycle blocks meets every flattened
positioned cycle clause and fixed-copy literal endpoint. -/
theorem allCycleRoutes_physicalRoutesMatch
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable) :
    PositionedPeriodicCNF.PhysicalIncidenceRoutesMatch
      ⟨allCycleClauses source sourcePlacement⟩
      (placement sourcePlacement)
      (allCycleRoutes source sourcePlacement) := by
  intro clause cycleIndex clauseMember
    literal literalIndex literalMember
  rcases allCycleClauseMetadata_lookup_valid
      source sourcePlacement clauseMember with
    ⟨metadata, metadataLookup, clauseEqual,
      localClauseMember⟩
  have localEndpoints :=
    positionedCycleRoutes_physicalRoutesMatch
      sourcePlacement metadata.atom
      metadata.clause metadata.localClauseIndex
      localClauseMember literal literalIndex
      (clauseEqual ▸ literalMember)
  simpa [allCycleRoutes, metadataLookup,
    clauseEqual] using localEndpoints

/-- Flattening the cycle blocks preserves their zero logical anchors. -/
theorem allCycleClauses_clauseAnchor_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {cycleIndex : Nat}
    (clauseMember :
      (clause, cycleIndex) ∈
        (allCycleClauses source sourcePlacement).zipIdx) :
    PeriodicCNF.clauseAnchor clause.literals =
      (0, 0) := by
  rcases allCycleClauseMetadata_lookup_valid
      source sourcePlacement clauseMember with
    ⟨metadata, _metadataLookup, clauseEqual,
      localClauseMember⟩
  subst clause
  exact cycleClausesFor_clauseAnchor_eq_zero
    sourcePlacement metadata.atom localClauseMember

/-- Flattening the cycle blocks preserves the zero offset of every local
implication literal. -/
theorem allCycleClauses_literal_offset_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
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
      (literal, literalIndex) ∈
        clause.literals.zipIdx) :
    literal.offset = (0, 0) := by
  rcases allCycleClauseMetadata_lookup_valid
      source sourcePlacement clauseMember with
    ⟨metadata, _metadataLookup, clauseEqual,
      localClauseMember⟩
  subst clause
  exact cycleClausesFor_literal_offset_eq_zero
    sourcePlacement metadata.atom localClauseMember
      literalMember

/-- Every genuine route in the flattened cycle suffix inherits its local
translated axis-alignment certificate. -/
theorem allCycleRoutes_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
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
      (literal, literalIndex) ∈
        clause.literals.zipIdx) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (allCycleRoutes source sourcePlacement
        cycleIndex literalIndex) := by
  rcases allCycleClauseMetadata_lookup_valid
      source sourcePlacement clauseMember with
    ⟨metadata, metadataLookup, clauseEqual,
      localClauseMember⟩
  have localOrthogonal :=
    positionedCycleRoutes_orthogonal
      sourcePlacement metadata.atom localClauseMember
      (clauseEqual ▸ literalMember)
  simpa [allCycleRoutes, metadataLookup] using
    localOrthogonal

/-- Use the generic canonical routes for copied source clauses and the
translated, certified Figure 7 routes for the appended implication-cycle
clauses. -/
def cycleSplicedIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (occurrencePorts :
      PeriodicEightOccurrenceSplit.OccurrencePorts) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    if clauseIndex <
        (occurrenceClauses source occurrencePorts).length
    then
      PositionedPeriodicCNF.orthogonalIncidenceRoutes
        (formula source sourcePlacement occurrencePorts)
        (placement sourcePlacement)
        clauseIndex literalIndex
    else
      allCycleRoutes source sourcePlacement
        (clauseIndex -
          (occurrenceClauses
            source occurrencePorts).length)
        literalIndex

/-- Before the formula append boundary, the spliced family is exactly the
generic canonical family. -/
theorem cycleSplicedIncidenceRoutes_occurrence
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (occurrencePorts :
      PeriodicEightOccurrenceSplit.OccurrencePorts)
    (clauseIndex literalIndex : Nat)
    (occurrenceIndex :
      clauseIndex <
        (occurrenceClauses source occurrencePorts).length) :
    cycleSplicedIncidenceRoutes
        source sourcePlacement occurrencePorts
        clauseIndex literalIndex =
      PositionedPeriodicCNF.orthogonalIncidenceRoutes
        (formula source sourcePlacement occurrencePorts)
        (placement sourcePlacement)
        clauseIndex literalIndex := by
  simp [cycleSplicedIncidenceRoutes, occurrenceIndex]

/-- At an index in the appended suffix, the spliced family is exactly the
parallel certified cycle-route lookup. -/
theorem cycleSplicedIncidenceRoutes_cycle
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (occurrencePorts :
      PeriodicEightOccurrenceSplit.OccurrencePorts)
    (cycleIndex literalIndex : Nat) :
    cycleSplicedIncidenceRoutes
        source sourcePlacement occurrencePorts
        ((occurrenceClauses
            source occurrencePorts).length +
          cycleIndex)
        literalIndex =
      allCycleRoutes source sourcePlacement
        cycleIndex literalIndex := by
  simp [cycleSplicedIncidenceRoutes]

/-- A clause beyond the copied-source prefix belongs to the appended cycle
list at the prefix-relative index. -/
theorem cycleClauseMember_of_formula_member
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (occurrencePorts :
      PeriodicEightOccurrenceSplit.OccurrencePorts)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (formula source sourcePlacement
          occurrencePorts).clauses.zipIdx)
    (cycleIndex :
      ¬clauseIndex <
        (occurrenceClauses
          source occurrencePorts).length) :
    (clause,
        clauseIndex -
          (occurrenceClauses
            source occurrencePorts).length) ∈
      (allCycleClauses source sourcePlacement).zipIdx := by
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp clauseMember
  change
    (occurrenceClauses source occurrencePorts ++
        allCycleClauses source sourcePlacement)[clauseIndex]? =
      some clause
    at clauseLookup
  rw [List.getElem?_append_right
      (Nat.le_of_not_gt cycleIndex)]
    at clauseLookup
  apply List.mem_zipIdx_iff_getElem?.mpr
  exact clauseLookup

/-- Every genuine route in the partially spliced family retains the same
canonical periodic endpoints as the generic route family. -/
theorem cycleSplicedIncidenceRoutes_endpoints
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (occurrencePorts :
      PeriodicEightOccurrenceSplit.OccurrencePorts)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (formula source sourcePlacement
          occurrencePorts).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈
        clause.literals.zipIdx) :
    (cycleSplicedIncidenceRoutes
        source sourcePlacement occurrencePorts
        clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (placement sourcePlacement) clause) ∧
      (cycleSplicedIncidenceRoutes
        source sourcePlacement occurrencePorts
        clauseIndex literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (placement sourcePlacement) clause literal) := by
  by_cases occurrenceIndex :
      clauseIndex <
        (occurrenceClauses source occurrencePorts).length
  · rw [cycleSplicedIncidenceRoutes_occurrence
      source sourcePlacement occurrencePorts
      clauseIndex literalIndex occurrenceIndex]
    rw [PositionedPeriodicCNF.orthogonalIncidenceRoutes_of_members
      (formula source sourcePlacement occurrencePorts)
      (placement sourcePlacement)
      clauseMember literalMember]
    simp
  · have cycleClauseMember :=
      cycleClauseMember_of_formula_member
        source sourcePlacement occurrencePorts
        clauseMember occurrenceIndex
    have cycleEndpoints :=
      allCycleRoutes_physicalRoutesMatch
        source sourcePlacement
        clause
        (clauseIndex -
          (occurrenceClauses
            source occurrencePorts).length)
        cycleClauseMember literal literalIndex
        literalMember
    have clauseIndexDecomposition :
        clauseIndex =
          (occurrenceClauses
            source occurrencePorts).length +
            (clauseIndex -
              (occurrenceClauses
                source occurrencePorts).length) := by
      omega
    rw [clauseIndexDecomposition,
      cycleSplicedIncidenceRoutes_cycle]
    have anchorZero :=
      allCycleClauses_clauseAnchor_eq_zero
        source sourcePlacement cycleClauseMember
    have offsetZero :=
      allCycleClauses_literal_offset_eq_zero
        source sourcePlacement cycleClauseMember
        literalMember
    constructor
    · simpa [PositionedPeriodicCNF.canonicalClausePosition,
        anchorZero,
        PeriodicVariablePlacement.translation,
        Cell.sub, Cell.scale] using cycleEndpoints.1
    · simpa [PositionedPeriodicCNF.canonicalLiteralPosition,
        PeriodicVariablePlacement.literalPosition,
        anchorZero, offsetZero,
        PeriodicVariablePlacement.translation,
        Cell.add, Cell.sub, Cell.scale] using
          cycleEndpoints.2

/-- Every genuine route in the partially spliced family is an orthogonal
polyline. -/
theorem cycleSplicedIncidenceRoutes_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (occurrencePorts :
      PeriodicEightOccurrenceSplit.OccurrencePorts)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (formula source sourcePlacement
          occurrencePorts).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈
        clause.literals.zipIdx) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (cycleSplicedIncidenceRoutes
        source sourcePlacement occurrencePorts
        clauseIndex literalIndex) := by
  by_cases occurrenceIndex :
      clauseIndex <
        (occurrenceClauses source occurrencePorts).length
  · rw [cycleSplicedIncidenceRoutes_occurrence
      source sourcePlacement occurrencePorts
      clauseIndex literalIndex occurrenceIndex]
    rw [PositionedPeriodicCNF.orthogonalIncidenceRoutes_of_members
      (formula source sourcePlacement occurrencePorts)
      (placement sourcePlacement)
      clauseMember literalMember]
    exact
      PositionedPeriodicCNF.orthogonalDetour_orthogonal _ _
  · have cycleClauseMember :=
      cycleClauseMember_of_formula_member
        source sourcePlacement occurrencePorts
        clauseMember occurrenceIndex
    have clauseIndexDecomposition :
        clauseIndex =
          (occurrenceClauses
            source occurrencePorts).length +
            (clauseIndex -
              (occurrenceClauses
                source occurrencePorts).length) := by
      omega
    rw [clauseIndexDecomposition,
      cycleSplicedIncidenceRoutes_cycle]
    exact allCycleRoutes_orthogonal
      source sourcePlacement cycleClauseMember
      literalMember

/-- Metadata-rich incidences retrieve the canonical endpoints of the
partially spliced route family. -/
theorem cycleSplicedIncidenceRoutes_endpoints_of_tagged
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (occurrencePorts :
      PeriodicEightOccurrenceSplit.OccurrencePorts)
    {tagged :
      CNFIncidence
        (ThreeOccurrenceVariable Variable) × Nat}
    (taggedMember :
      tagged ∈
        (PeriodicCNF.incidencesWithMetadata
          (formula source sourcePlacement
            occurrencePorts).erase).zipIdx) :
    (cycleSplicedIncidenceRoutes
        source sourcePlacement occurrencePorts
        tagged.1.clauseIndex
        tagged.1.literalIndex).head? =
        some
          (PositionedPeriodicCNF.incidenceVertexPositionAt
            (formula source sourcePlacement occurrencePorts)
            (placement sourcePlacement)
            (.clause tagged.1.clauseIndex)) ∧
      (cycleSplicedIncidenceRoutes
        source sourcePlacement occurrencePorts
        tagged.1.clauseIndex
        tagged.1.literalIndex).getLast? =
        some
          (Cell.add
            ((placement sourcePlacement).position
              tagged.1.literal.atom)
            ((placement sourcePlacement).translation
              tagged.1.edge.offset)) := by
  rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
      (formula source sourcePlacement occurrencePorts)
      taggedMember with
    ⟨clause, literal, clauseMember,
      literalMember, taggedEqual⟩
  have clauseIndexLt :
      tagged.1.clauseIndex <
        (formula source sourcePlacement
          occurrencePorts).clauses.length :=
    List.snd_lt_of_mem_zipIdx clauseMember
  have clauseLookup :
      (formula source sourcePlacement occurrencePorts).clauses[
        tagged.1.clauseIndex] = clause :=
    (List.mem_zipIdx' clauseMember).2.symm
  have endpoints :=
    cycleSplicedIncidenceRoutes_endpoints
      source sourcePlacement occurrencePorts
      clauseMember literalMember
  rw [taggedEqual]
  constructor
  · simpa [PositionedPeriodicCNF.incidenceVertexPositionAt,
      List.getElem?_eq_getElem clauseIndexLt,
      clauseLookup] using endpoints.1
  · simpa [PositionedPeriodicCNF.canonicalLiteralPosition,
      CNFIncidence.edge,
      PeriodicCNF.incidenceEdge] using endpoints.2

/-- Replacing the cycle suffix by certified local routes preserves the
complete periodic incidence-graph endpoint condition. -/
theorem cycleSplicedIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (occurrencePorts :
      PeriodicEightOccurrenceSplit.OccurrencePorts)
    (sourcePeriodPositive :
      0 < sourcePlacement.period) :
    (PositionedPeriodicCNF.incidenceDrawing
      (formula source sourcePlacement occurrencePorts)
      (placement sourcePlacement)
      (cycleSplicedIncidenceRoutes
        source sourcePlacement occurrencePorts)).RoutesMatch
      (formula source sourcePlacement
        occurrencePorts).erase.incidenceGraph := by
  intro taggedEdge taggedEdgeMember
  have metadataEdgeMember := taggedEdgeMember
  rw [← PeriodicCNF.incidencesWithMetadata_edges
      (formula source sourcePlacement occurrencePorts).erase,
    List.zipIdx_map] at metadataEdgeMember
  rcases List.mem_map.mp metadataEdgeMember with
    ⟨taggedIncidence, taggedIncidenceMember,
      taggedIncidenceEqual⟩
  have endpoints :=
    cycleSplicedIncidenceRoutes_endpoints_of_tagged
      source sourcePlacement occurrencePorts
      taggedIncidenceMember
  have graphWellFormed :=
    PeriodicCNF.incidenceGraph_isWellFormed
      (formula source sourcePlacement occurrencePorts).erase
  have edgeMember :
      taggedIncidence.1.edge ∈
        (formula source sourcePlacement
          occurrencePorts).erase.incidenceGraph.edges :=
    List.fst_mem_of_mem_zipIdx
      (PeriodicCNF.tagged_incidence_edge_mem
        (formula source sourcePlacement occurrencePorts).erase
        taggedIncidenceMember)
  have endpointMembers :=
    graphWellFormed.2 taggedIncidence.1.edge edgeMember
  have sourcePosition :=
    PositionedPeriodicCNF.incidenceDrawing_vertexPosition_of_mem
      (formula source sourcePlacement occurrencePorts)
      (placement sourcePlacement)
      (cycleSplicedIncidenceRoutes
        source sourcePlacement occurrencePorts)
      endpointMembers.1
  have targetPosition :=
    PositionedPeriodicCNF.incidenceDrawing_vertexPosition_of_mem
      (formula source sourcePlacement occurrencePorts)
      (placement sourcePlacement)
      (cycleSplicedIncidenceRoutes
        source sourcePlacement occurrencePorts)
      endpointMembers.2
  have routeLookup :=
    PositionedPeriodicCNF.incidenceDrawing_edgeRoute_of_tagged
      (formula source sourcePlacement occurrencePorts)
      (placement sourcePlacement)
      (cycleSplicedIncidenceRoutes
        source sourcePlacement occurrencePorts)
      taggedIncidenceMember
  rw [← taggedIncidenceEqual]
  simp only [Prod.map, id_eq]
  rw [routeLookup]
  constructor
  · rw [sourcePosition, CNFIncidence.edge_source]
    exact endpoints.1
  · rw [targetPosition, CNFIncidence.edge_target]
    simp only [PositionedPeriodicCNF.incidenceVertexPositionAt,
      PeriodicGridDrawing.periodTranslation]
    rw [PositionedPeriodicCNF.incidenceDrawing_gridSize
      (formula source sourcePlacement occurrencePorts)
      (placement sourcePlacement)
      (cycleSplicedIncidenceRoutes
        source sourcePlacement occurrencePorts)
      (placement_period_pos
        sourcePlacement sourcePeriodPositive)]
    simpa [PeriodicVariablePlacement.translation] using
      endpoints.2

/-- Replacing the cycle suffix by certified local routes preserves
orthogonality of the complete periodic incidence drawing. -/
theorem cycleSplicedIncidenceDrawing_isOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (occurrencePorts :
      PeriodicEightOccurrenceSplit.OccurrencePorts) :
    (PositionedPeriodicCNF.incidenceDrawing
      (formula source sourcePlacement occurrencePorts)
      (placement sourcePlacement)
      (cycleSplicedIncidenceRoutes
        source sourcePlacement occurrencePorts)).IsOrthogonal := by
  rw [PeriodicGridDrawing.isOrthogonal_iff_routes]
  intro route routeMember
  change route ∈
    PositionedPeriodicCNF.incidenceEdgeRoutes
      (formula source sourcePlacement occurrencePorts)
      (cycleSplicedIncidenceRoutes
        source sourcePlacement occurrencePorts)
    at routeMember
  rw [PositionedPeriodicCNF.incidenceEdgeRoutes_eq_metadata_map]
    at routeMember
  rcases List.mem_map.mp routeMember with
    ⟨incidence, incidenceMember, routeEqual⟩
  subst route
  rcases List.mem_iff_getElem.mp incidenceMember with
    ⟨incidenceIndex, incidenceIndexLt, incidenceAt⟩
  have taggedMember :
      (incidence, incidenceIndex) ∈
        (PeriodicCNF.incidencesWithMetadata
          (formula source sourcePlacement
            occurrencePorts).erase).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff]
    exact ⟨incidenceIndexLt, incidenceAt⟩
  rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
      (formula source sourcePlacement occurrencePorts)
      taggedMember with
    ⟨clause, literal, clauseMember,
      literalMember, _taggedEqual⟩
  exact cycleSplicedIncidenceRoutes_orthogonal
    source sourcePlacement occurrencePorts
    clauseMember literalMember

end PeriodicEightOccurrenceSplitPositioned

namespace PeriodicOrthocrossing

def drawingEightOccurrenceSplitIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PositionedPeriodicCNF.orthogonalIncidenceRoutes
    (drawingEightOccurrenceSplitPositionedFormula formula)
    (drawingEightOccurrenceSplitPlacement formula)

/-- The route family that has begun the geometric splice: source incidences
still use canonical detours, while all implication rings use the certified
translated Figure 7 routes. -/
def drawingEightOccurrenceSplitCycleSplicedIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PeriodicEightOccurrenceSplitPositioned.cycleSplicedIncidenceRoutes
    (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula)
    (wrappedDrawingPeriodicPlanarSATPlacement formula)
    (PeriodicEightOccurrenceSplit.occurrencePortsOfAngularOrder
      (deduplicatedWrappedDrawingPeriodicPlanarSATFormula formula)
      (drawingSemanticAngularOccurrenceOrder formula))

/-- The cycle-spliced drawing retains exact incidence-graph endpoints. -/
theorem
    drawingEightOccurrenceSplitCycleSplicedIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (PositionedPeriodicCNF.incidenceDrawing
      (drawingEightOccurrenceSplitPositionedFormula formula)
      (drawingEightOccurrenceSplitPlacement formula)
      (drawingEightOccurrenceSplitCycleSplicedIncidenceRoutes
        formula)).RoutesMatch
      (drawingEightOccurrenceSplitPositionedFormula
        formula).erase.incidenceGraph := by
  exact
    PeriodicEightOccurrenceSplitPositioned.cycleSplicedIncidenceDrawing_routesMatch
        (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula)
        (wrappedDrawingPeriodicPlanarSATPlacement formula)
        (PeriodicEightOccurrenceSplit.occurrencePortsOfAngularOrder
          (deduplicatedWrappedDrawingPeriodicPlanarSATFormula formula)
          (drawingSemanticAngularOccurrenceOrder formula))
        (drawingPeriodicPlanarSATPlacement_period_pos formula)

/-- The cycle-spliced drawing is still completely orthogonal. -/
theorem
    drawingEightOccurrenceSplitCycleSplicedIncidenceDrawing_isOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (PositionedPeriodicCNF.incidenceDrawing
      (drawingEightOccurrenceSplitPositionedFormula formula)
      (drawingEightOccurrenceSplitPlacement formula)
      (drawingEightOccurrenceSplitCycleSplicedIncidenceRoutes
        formula)).IsOrthogonal := by
  exact
    PeriodicEightOccurrenceSplitPositioned.cycleSplicedIncidenceDrawing_isOrthogonal
      (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      (wrappedDrawingPeriodicPlanarSATPlacement formula)
      (PeriodicEightOccurrenceSplit.occurrencePortsOfAngularOrder
        (deduplicatedWrappedDrawingPeriodicPlanarSATFormula formula)
        (drawingSemanticAngularOccurrenceOrder formula))

theorem drawingEightOccurrenceSplitPlacement_period_pos
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    0 < (drawingEightOccurrenceSplitPlacement formula).period := by
  unfold drawingEightOccurrenceSplitPlacement
  apply PeriodicEightOccurrenceSplitPositioned.placement_period_pos
  exact drawingPeriodicPlanarSATPlacement_period_pos formula

theorem drawingEightOccurrenceSplitIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (PositionedPeriodicCNF.incidenceDrawing
      (drawingEightOccurrenceSplitPositionedFormula formula)
      (drawingEightOccurrenceSplitPlacement formula)
      (drawingEightOccurrenceSplitIncidenceRoutes
        formula)).RoutesMatch
      (drawingEightOccurrenceSplitPositionedFormula
        formula).erase.incidenceGraph := by
  exact
    PositionedPeriodicCNF.orthogonalIncidenceDrawing_routesMatch
      (drawingEightOccurrenceSplitPositionedFormula formula)
      (drawingEightOccurrenceSplitPlacement formula)
      (drawingEightOccurrenceSplitPlacement_period_pos formula)

theorem drawingEightOccurrenceSplitIncidenceDrawing_isOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (PositionedPeriodicCNF.incidenceDrawing
      (drawingEightOccurrenceSplitPositionedFormula formula)
      (drawingEightOccurrenceSplitPlacement formula)
      (drawingEightOccurrenceSplitIncidenceRoutes
        formula)).IsOrthogonal := by
  exact
    PositionedPeriodicCNF.orthogonalIncidenceDrawing_isOrthogonal
      (drawingEightOccurrenceSplitPositionedFormula formula)
      (drawingEightOccurrenceSplitPlacement formula)

end PeriodicOrthocrossing
end LeanTrominoes
