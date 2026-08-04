import LeanTrominoes.PeriodicEightOccurrenceSplitCycleMacrocellSeparation
import LeanTrominoes.PeriodicEightOccurrenceSplitPositionedOccurrenceIndex
import LeanTrominoes.PeriodicEightOccurrenceSplitPositionedCycleIndex
import LeanTrominoes.RetainedAngularFanCompleteRouteCertificates
import LeanTrominoes.PositionedPeriodicCNFIncidenceRouteLookup

/-!
# Clause-position injectivity for positioned fixed-eight splitting

Every copied source clause lies at the center of a factor-36 source
clause macrocell.  Every appended Figure 7 implication clause lies within
six cells of a factor-36 source-variable macrocell.  Those small offsets
cannot cross macrocell boundaries, while a compatible source incidence
presentation distinguishes the underlying clause and variable vertices.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplitPositioned

open OccurrenceSplitRing
open PeriodicThreeSATThree
open PositionedPeriodicCNF

/-- Equality of two points in radius-six neighborhoods of the factor-36
lattice identifies both their lattice points and their local offsets. -/
private theorem tightMacrocell_eq
    (firstBase secondBase firstOffset secondOffset : Cell)
    (firstBounds :
      -6 ≤ firstOffset.1 ∧ firstOffset.1 ≤ 6 ∧
        -6 ≤ firstOffset.2 ∧ firstOffset.2 ≤ 6)
    (secondBounds :
      -6 ≤ secondOffset.1 ∧ secondOffset.1 ≤ 6 ∧
        -6 ≤ secondOffset.2 ∧ secondOffset.2 ≤ 6)
    (equal :
      Cell.add (Cell.scale refinementScale firstBase) firstOffset =
        Cell.add (Cell.scale refinementScale secondBase) secondOffset) :
    firstBase = secondBase ∧ firstOffset = secondOffset := by
  rcases firstBase with ⟨firstX, firstY⟩
  rcases secondBase with ⟨secondX, secondY⟩
  rcases firstOffset with ⟨firstOffsetX, firstOffsetY⟩
  rcases secondOffset with ⟨secondOffsetX, secondOffsetY⟩
  simp only [Cell.add, Cell.scale, refinementScale,
    Prod.mk.injEq] at equal ⊢
  constructor
  · constructor <;> omega
  · constructor <;> omega

/-- Subtracting a fixed cell is injective. -/
private theorem cellSub_right_injective
    (base : Cell) : Function.Injective (fun point => Cell.sub point base) := by
  intro first second equal
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases base with ⟨baseX, baseY⟩
  simp [Cell.sub, Prod.mk.injEq] at equal ⊢
  omega

/-- A genuine source clause supplies its listed clause vertex. -/
private theorem clauseVertex_mem_incidenceGraph
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx) :
    CNFVertex.clause clauseIndex ∈
      source.erase.incidenceGraph.vertices := by
  have indexLt : clauseIndex < source.clauses.length :=
    (List.mem_zipIdx' clauseMember).1
  apply List.mem_append.mpr
  apply Or.inr
  exact List.mem_map.mpr
    ⟨clauseIndex, by simpa [PositionedPeriodicCNF.erase] using indexLt, rfl⟩

/-- An atom owning a Figure 7 cycle supplies its listed source-variable
vertex. -/
private theorem variableVertex_mem_incidenceGraph
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    {atom : Variable}
    (atomMember : atom ∈ sourceVariables source.erase) :
    CNFVertex.variable atom ∈
      source.erase.incidenceGraph.vertices := by
  have atomOccurrence : atom ∈ source.erase.variableOccurrences := by
    rw [sourceVariables, List.mem_dedup,
      List.mem_map] at atomMember
    rcases atomMember with
      ⟨taggedLiteral, taggedLiteralMember, atomEqual⟩
    rw [taggedLiterals, List.mem_flatMap]
      at taggedLiteralMember
    rcases taggedLiteralMember with
      ⟨taggedClause, taggedClauseMember,
        taggedLiteralMember⟩
    rcases List.mem_map.mp taggedLiteralMember with
      ⟨taggedClauseLiteral, taggedClauseLiteralMember,
        taggedLiteralEqual⟩
    unfold PeriodicCNF.variableOccurrences
    apply List.mem_flatMap.mpr
    refine
      ⟨taggedClause.1,
        List.fst_mem_of_mem_zipIdx taggedClauseMember, ?_⟩
    apply List.mem_map.mpr
    refine
      ⟨taggedClauseLiteral.1,
        List.fst_mem_of_mem_zipIdx taggedClauseLiteralMember, ?_⟩
    rw [← atomEqual]
    exact congrArg (fun tagged => tagged.1.atom)
      taggedLiteralEqual
  apply List.mem_append.mpr
  apply Or.inl
  exact List.mem_map.mpr
    ⟨atom, List.mem_dedup.mpr atomOccurrence, rfl⟩

/-- Clause positions in one translated Figure 7 cycle do not repeat. -/
private theorem cycleClausesFor_positions_nodup
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) :
    ((cycleClausesFor sourcePlacement atom).map
      PositionedPeriodicClause.position).Nodup := by
  have localPositionsNodup :
      (cycleFormula.map
        PlanarThreeSAT.EmbeddedClause.position).Nodup := by
    have allPositionsNodup :=
      cycleDrawing_isValid.2.2.2.2.2
    exact
      (List.nodup_append.mp
        (by simpa [cycleDrawing,
            PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.vertexPositions]
          using allPositionsNodup)).2.1
  have translatedNodup :=
    localPositionsNodup.map
      (PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.cell_add_left_injective
        (macroOrigin sourcePlacement atom))
  simpa [cycleClausesFor_eq_cycleFormula,
    positionedLocalCycleClause, List.map_map,
    Function.comp_def] using translatedNodup

/-- Equal positions of two genuine clauses in one source atom's Figure 7
cycle force their local presentation indices to agree. -/
private theorem cycleClausesFor_position_injective
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable)
    {firstClause secondClause :
      PositionedPeriodicClause (ThreeOccurrenceVariable Variable)}
    {firstIndex secondIndex : Nat}
    (firstMember :
      (firstClause, firstIndex) ∈
        (cycleClausesFor sourcePlacement atom).zipIdx)
    (secondMember :
      (secondClause, secondIndex) ∈
        (cycleClausesFor sourcePlacement atom).zipIdx)
    (positionsEqual :
      firstClause.position = secondClause.position) :
    firstIndex = secondIndex := by
  have firstLookup :=
    (List.mem_zipIdx_iff_getElem?).mp firstMember
  have secondLookup :=
    (List.mem_zipIdx_iff_getElem?).mp secondMember
  rcases List.getElem?_eq_some_iff.mp firstLookup with
    ⟨firstIndexLt, firstAt⟩
  rcases List.getElem?_eq_some_iff.mp secondLookup with
    ⟨secondIndexLt, secondAt⟩
  have firstMapIndexLt :
      firstIndex <
        ((cycleClausesFor sourcePlacement atom).map
          PositionedPeriodicClause.position).length := by
    simpa using firstIndexLt
  have secondMapIndexLt :
      secondIndex <
        ((cycleClausesFor sourcePlacement atom).map
          PositionedPeriodicClause.position).length := by
    simpa using secondIndexLt
  apply
    ((cycleClausesFor_positions_nodup
      sourcePlacement atom).getElem_inj_iff
        (hi := firstMapIndexLt)
        (hj := secondMapIndexLt)).mp
  simp only [List.getElem_map]
  exact
    (congrArg PositionedPeriodicClause.position firstAt).trans
      (positionsEqual.trans
        (congrArg PositionedPeriodicClause.position secondAt).symm)

/-- A complete-formula clause before the append boundary belongs to the
copied source prefix at the same index. -/
private theorem occurrenceClauseMemberGeneric_of_formula_member
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (occurrencePorts :
      PeriodicEightOccurrenceSplit.OccurrencePorts)
    {clause :
      PositionedPeriodicClause (ThreeOccurrenceVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (formula source sourcePlacement occurrencePorts).clauses.zipIdx)
    (occurrenceIndex :
      clauseIndex < (occurrenceClauses source occurrencePorts).length) :
    (clause, clauseIndex) ∈
      (occurrenceClauses source occurrencePorts).zipIdx := by
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp clauseMember
  change
    (occurrenceClauses source occurrencePorts ++
      allCycleClauses source sourcePlacement)[clauseIndex]? =
        some clause at clauseLookup
  rw [List.getElem?_append_left occurrenceIndex] at clauseLookup
  exact List.mem_zipIdx_iff_getElem?.mpr clauseLookup

/-- The local displacement of one positioned implication clause from its
factor-36 source-variable macrocell center. -/
private def cycleClauseOffset
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (metadata : CycleClauseMetadata Variable) : Cell :=
  Cell.sub metadata.clause.position
    (Cell.scale refinementScale
      (sourcePlacement.position metadata.atom))

/-- Every genuine implication clause has a radius-six local displacement,
and its canonical position is its macrocell center plus that displacement. -/
private theorem cycleClauseOffset_data
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {metadata : CycleClauseMetadata Variable}
    (clauseMember :
      (metadata.clause, metadata.localClauseIndex) ∈
        (cycleClausesFor
          sourcePlacement metadata.atom).zipIdx) :
    (-6 ≤ (cycleClauseOffset sourcePlacement metadata).1 ∧
        (cycleClauseOffset sourcePlacement metadata).1 ≤ 6 ∧
      -6 ≤ (cycleClauseOffset sourcePlacement metadata).2 ∧
        (cycleClauseOffset sourcePlacement metadata).2 ≤ 6) ∧
      PositionedPeriodicCNF.canonicalClausePosition
          (placement sourcePlacement) metadata.clause =
        Cell.add
          (Cell.scale refinementScale
            (sourcePlacement.position metadata.atom))
          (cycleClauseOffset sourcePlacement metadata) := by
  have anchorZero :=
    cycleClausesFor_clauseAnchor_eq_zero
      sourcePlacement metadata.atom clauseMember
  rw [cycleClausesFor_eq_cycleFormula,
    List.zipIdx_map] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedClause, taggedClauseMember,
      taggedClauseEqual⟩
  have clauseEqual :
      metadata.clause =
        positionedLocalCycleClause
          sourcePlacement metadata.atom taggedClause.1 :=
    (congrArg Prod.fst taggedClauseEqual).symm
  have localClauseMember : taggedClause.1 ∈ cycleFormula :=
    List.fst_mem_of_mem_zipIdx taggedClauseMember
  have localBounds :=
    cycleFormula_clausePosition_inClosedGridRectangle
      localClauseMember
  rw [clauseEqual] at anchorZero
  have localAnchorZero :
      PeriodicCNF.clauseAnchor
        (periodicCycleClause metadata.atom taggedClause.1) =
          (0, 0) := by
    simpa [positionedLocalCycleClause] using anchorZero
  constructor
  · simp [cycleClauseOffset, clauseEqual,
      positionedLocalCycleClause,
      macroOrigin, Cell.add,
      Cell.sub, Cell.scale, refinementScale]
    simp only [InClosedGridRectangle] at localBounds
    omega
  · apply Prod.ext <;>
      simp [PositionedPeriodicCNF.canonicalClausePosition,
        cycleClauseOffset, clauseEqual,
        positionedLocalCycleClause,
        macroOrigin, localAnchorZero, placement,
        PeriodicVariablePlacement.translation,
        Cell.add, Cell.sub, Cell.scale,
        refinementScale]

/-- Equality of canonical split-clause positions reduces to equality of
their source macrocells and their radius-six local offsets. -/
private theorem translatedMacrocell_eq
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (firstBase secondBase firstOffset secondOffset : Cell)
    (firstBounds :
      -6 ≤ firstOffset.1 ∧ firstOffset.1 ≤ 6 ∧
        -6 ≤ firstOffset.2 ∧ firstOffset.2 ≤ 6)
    (secondBounds :
      -6 ≤ secondOffset.1 ∧ secondOffset.1 ≤ 6 ∧
        -6 ≤ secondOffset.2 ∧ secondOffset.2 ≤ 6)
    (firstPosition secondPosition : Cell)
    (firstPositionEq :
      firstPosition =
        Cell.add (Cell.scale refinementScale firstBase) firstOffset)
    (secondPositionEq :
      secondPosition =
        Cell.add (Cell.scale refinementScale secondBase) secondOffset)
    (relativeTranslate : Cell)
    (positionsEqual :
      firstPosition =
        Cell.add ((placement sourcePlacement).translation relativeTranslate)
          secondPosition) :
    firstBase =
        Cell.add (sourcePlacement.translation relativeTranslate) secondBase ∧
      firstOffset = secondOffset := by
  apply tightMacrocell_eq
    firstBase
    (Cell.add (sourcePlacement.translation relativeTranslate) secondBase)
    firstOffset secondOffset firstBounds secondBounds
  calc
    Cell.add (Cell.scale refinementScale firstBase) firstOffset =
        firstPosition := firstPositionEq.symm
    _ = Cell.add
          ((placement sourcePlacement).translation relativeTranslate)
          secondPosition := positionsEqual
    _ = Cell.add
          (Cell.scale refinementScale
            (Cell.add
              (sourcePlacement.translation relativeTranslate)
              secondBase))
          secondOffset := by
      rw [secondPositionEq]
      apply Prod.ext <;>
        simp [placement, refinementScale,
          PeriodicVariablePlacement.translation,
          Cell.add, Cell.scale] <;>
        ring

/-- A copied source clause sits at the center of its factor-36 source
clause macrocell. -/
private theorem occurrenceClauseMacrocell_data
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (occurrencePorts :
      PeriodicEightOccurrenceSplit.OccurrencePorts)
    (metadata : OccurrenceClauseMetadata Variable)
    (sourceMember :
      (metadata.sourceClause, metadata.clauseIndex) ∈
        source.clauses.zipIdx)
    (clauseEqual :
      metadata.clause =
        occurrenceClause occurrencePorts
          metadata.clauseIndex metadata.sourceClause) :
    PositionedPeriodicCNF.canonicalClausePosition
        (placement sourcePlacement) metadata.clause =
      Cell.add
        (Cell.scale refinementScale
          (incidenceVertexPositionAt source sourcePlacement
            (.clause metadata.clauseIndex)))
        (0, 0) := by
  have sourceIndexLt :
      metadata.clauseIndex < source.clauses.length :=
    (List.mem_zipIdx' sourceMember).1
  have sourceLookup :=
    (List.mem_zipIdx_iff_getElem?).mp sourceMember
  have sourceAt :
      source.clauses[metadata.clauseIndex] =
        metadata.sourceClause := by
    exact (List.getElem?_eq_some_iff.mp sourceLookup).2
  rw [clauseEqual,
    PeriodicEightOccurrenceSplit.canonicalClausePosition_occurrenceClause,
    incidenceVertexPositionAt_clause source sourcePlacement
      metadata.clauseIndex sourceIndexLt,
    sourceAt]
  simp [Cell.add]

/-- Canonical clause position is injective modulo period translations for
the complete positioned fixed-eight split.  Thus a translated equality
cannot confuse copied source clauses with each other, copied clauses with
Figure 7 clauses, or two distinct Figure 7 clauses. -/
theorem canonicalClausePosition_eq_translated_imp_clauseIndex_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (occurrencePorts :
      PeriodicEightOccurrenceSplit.OccurrencePorts)
    (presentation :
      PlanarIncidencePresentation source sourcePlacement)
    {firstClause secondClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstMember :
      (firstClause, firstClauseIndex) ∈
        (formula source sourcePlacement
          occurrencePorts).clauses.zipIdx)
    (secondMember :
      (secondClause, secondClauseIndex) ∈
        (formula source sourcePlacement
          occurrencePorts).clauses.zipIdx)
    (relativeTranslate : Cell)
    (positionsEqual :
      PositionedPeriodicCNF.canonicalClausePosition
          (placement sourcePlacement) firstClause =
        Cell.add
          ((placement sourcePlacement).translation relativeTranslate)
          (PositionedPeriodicCNF.canonicalClausePosition
            (placement sourcePlacement) secondClause)) :
    firstClauseIndex = secondClauseIndex := by
  let boundary :=
    (occurrenceClauses source occurrencePorts).length
  by_cases firstOccurrence : firstClauseIndex < boundary
  · have firstOccurrenceMember :=
      occurrenceClauseMemberGeneric_of_formula_member
        source sourcePlacement occurrencePorts firstMember
        firstOccurrence
    rcases occurrenceClauseMetadata_lookup
        source occurrencePorts firstOccurrenceMember with
      ⟨firstMetadata, firstLookup, firstClauseEqual,
        firstSourceMember, firstIndexEqual,
        firstOccurrenceEqual⟩
    have firstVertexMember :=
      clauseVertex_mem_incidenceGraph source firstSourceMember
    have firstPosition :=
      occurrenceClauseMacrocell_data source sourcePlacement
        occurrencePorts firstMetadata firstSourceMember
        firstOccurrenceEqual
    by_cases secondOccurrence : secondClauseIndex < boundary
    · have secondOccurrenceMember :=
        occurrenceClauseMemberGeneric_of_formula_member
          source sourcePlacement occurrencePorts secondMember
          secondOccurrence
      rcases occurrenceClauseMetadata_lookup
          source occurrencePorts secondOccurrenceMember with
        ⟨secondMetadata, secondLookup, secondClauseEqual,
          secondSourceMember, secondIndexEqual,
          secondOccurrenceEqual⟩
      have secondVertexMember :=
        clauseVertex_mem_incidenceGraph source secondSourceMember
      have secondPosition :=
        occurrenceClauseMacrocell_data source sourcePlacement
          occurrencePorts secondMetadata secondSourceMember
          secondOccurrenceEqual
      have macrocellEqual :=
        translatedMacrocell_eq sourcePlacement
          (incidenceVertexPositionAt source sourcePlacement
            (.clause firstMetadata.clauseIndex))
          (incidenceVertexPositionAt source sourcePlacement
            (.clause secondMetadata.clauseIndex))
          (0, 0) (0, 0)
          (by norm_num) (by norm_num)
          (PositionedPeriodicCNF.canonicalClausePosition
            (placement sourcePlacement) firstMetadata.clause)
          (PositionedPeriodicCNF.canonicalClausePosition
            (placement sourcePlacement) secondMetadata.clause)
          firstPosition secondPosition relativeTranslate
          (by simpa [firstClauseEqual, secondClauseEqual]
            using positionsEqual)
      have verticesEqual :=
        presentation.incidenceVertexPositionAt_eq_translated_imp_eq
          firstVertexMember secondVertexMember relativeTranslate
          macrocellEqual.1
      exact firstIndexEqual.symm.trans
        ((CNFVertex.clause.inj verticesEqual).trans secondIndexEqual)
    · have secondCycleMember :=
        cycleClauseMember_of_formula_member
          source sourcePlacement occurrencePorts secondMember
          secondOccurrence
      rcases allCycleClauseMetadata_lookup_valid
          source sourcePlacement secondCycleMember with
        ⟨secondMetadata, secondLookup, secondClauseEqual,
          secondLocalMember⟩
      have secondAtomMember :=
        allCycleClauseMetadata_lookup_atom_mem
          source sourcePlacement secondLookup
      have secondVertexMember :=
        variableVertex_mem_incidenceGraph source secondAtomMember
      have secondPosition :=
        cycleClauseOffset_data sourcePlacement secondLocalMember
      have macrocellEqual :=
        translatedMacrocell_eq sourcePlacement
          (incidenceVertexPositionAt source sourcePlacement
            (.clause firstMetadata.clauseIndex))
          (sourcePlacement.position secondMetadata.atom)
          (0, 0)
          (cycleClauseOffset sourcePlacement secondMetadata)
          (by norm_num) secondPosition.1
          (PositionedPeriodicCNF.canonicalClausePosition
            (placement sourcePlacement) firstMetadata.clause)
          (PositionedPeriodicCNF.canonicalClausePosition
            (placement sourcePlacement) secondMetadata.clause)
          firstPosition secondPosition.2 relativeTranslate
          (by simpa [firstClauseEqual, secondClauseEqual]
            using positionsEqual)
      have verticesEqual :=
        presentation.incidenceVertexPositionAt_eq_translated_imp_eq
          firstVertexMember secondVertexMember relativeTranslate
          (by simpa [incidenceVertexPositionAt]
            using macrocellEqual.1)
      cases verticesEqual
  · have firstCycleMember :=
      cycleClauseMember_of_formula_member
        source sourcePlacement occurrencePorts firstMember
        firstOccurrence
    rcases allCycleClauseMetadata_lookup_valid
        source sourcePlacement firstCycleMember with
      ⟨firstMetadata, firstLookup, firstClauseEqual,
        firstLocalMember⟩
    have firstAtomMember :=
      allCycleClauseMetadata_lookup_atom_mem
        source sourcePlacement firstLookup
    have firstVertexMember :=
      variableVertex_mem_incidenceGraph source firstAtomMember
    have firstPosition :=
      cycleClauseOffset_data sourcePlacement firstLocalMember
    by_cases secondOccurrence : secondClauseIndex < boundary
    · have secondOccurrenceMember :=
        occurrenceClauseMemberGeneric_of_formula_member
          source sourcePlacement occurrencePorts secondMember
          secondOccurrence
      rcases occurrenceClauseMetadata_lookup
          source occurrencePorts secondOccurrenceMember with
        ⟨secondMetadata, secondLookup, secondClauseEqual,
          secondSourceMember, secondIndexEqual,
          secondOccurrenceEqual⟩
      have secondVertexMember :=
        clauseVertex_mem_incidenceGraph source secondSourceMember
      have secondPosition :=
        occurrenceClauseMacrocell_data source sourcePlacement
          occurrencePorts secondMetadata secondSourceMember
          secondOccurrenceEqual
      have macrocellEqual :=
        translatedMacrocell_eq sourcePlacement
          (sourcePlacement.position firstMetadata.atom)
          (incidenceVertexPositionAt source sourcePlacement
            (.clause secondMetadata.clauseIndex))
          (cycleClauseOffset sourcePlacement firstMetadata)
          (0, 0) firstPosition.1 (by norm_num)
          (PositionedPeriodicCNF.canonicalClausePosition
            (placement sourcePlacement) firstMetadata.clause)
          (PositionedPeriodicCNF.canonicalClausePosition
            (placement sourcePlacement) secondMetadata.clause)
          firstPosition.2 secondPosition relativeTranslate
          (by simpa [firstClauseEqual, secondClauseEqual]
            using positionsEqual)
      have verticesEqual :=
        presentation.incidenceVertexPositionAt_eq_translated_imp_eq
          firstVertexMember secondVertexMember relativeTranslate
          (by simpa [incidenceVertexPositionAt]
            using macrocellEqual.1)
      cases verticesEqual
    · have secondCycleMember :=
        cycleClauseMember_of_formula_member
          source sourcePlacement occurrencePorts secondMember
          secondOccurrence
      rcases allCycleClauseMetadata_lookup_valid
          source sourcePlacement secondCycleMember with
        ⟨secondMetadata, secondLookup, secondClauseEqual,
          secondLocalMember⟩
      have secondAtomMember :=
        allCycleClauseMetadata_lookup_atom_mem
          source sourcePlacement secondLookup
      have secondVertexMember :=
        variableVertex_mem_incidenceGraph source secondAtomMember
      have secondPosition :=
        cycleClauseOffset_data sourcePlacement secondLocalMember
      have macrocellEqual :=
        translatedMacrocell_eq sourcePlacement
          (sourcePlacement.position firstMetadata.atom)
          (sourcePlacement.position secondMetadata.atom)
          (cycleClauseOffset sourcePlacement firstMetadata)
          (cycleClauseOffset sourcePlacement secondMetadata)
          firstPosition.1 secondPosition.1
          (PositionedPeriodicCNF.canonicalClausePosition
            (placement sourcePlacement) firstMetadata.clause)
          (PositionedPeriodicCNF.canonicalClausePosition
            (placement sourcePlacement) secondMetadata.clause)
          firstPosition.2 secondPosition.2 relativeTranslate
          (by simpa [firstClauseEqual, secondClauseEqual]
            using positionsEqual)
      have verticesEqual :=
        presentation.incidenceVertexPositionAt_eq_translated_imp_eq
          firstVertexMember secondVertexMember relativeTranslate
          (by simpa [incidenceVertexPositionAt]
            using macrocellEqual.1)
      have atomsEqual :
          firstMetadata.atom = secondMetadata.atom :=
        CNFVertex.variable.inj verticesEqual
      have clausePositionsEqual :
          firstMetadata.clause.position =
            secondMetadata.clause.position := by
        have offsetsEqual := macrocellEqual.2
        simp only [cycleClauseOffset] at offsetsEqual
        rw [atomsEqual] at offsetsEqual
        exact cellSub_right_injective
          (Cell.scale refinementScale
            (sourcePlacement.position secondMetadata.atom))
          offsetsEqual
      have secondLocalMember' :
          (secondMetadata.clause,
              secondMetadata.localClauseIndex) ∈
            (cycleClausesFor sourcePlacement
              firstMetadata.atom).zipIdx := by
        simpa [atomsEqual] using secondLocalMember
      have localIndicesEqual :=
        cycleClausesFor_position_injective sourcePlacement
          firstMetadata.atom firstLocalMember
          secondLocalMember' clausePositionsEqual
      have keysEqual :
          firstMetadata.key = secondMetadata.key := by
        apply Prod.ext
        · exact atomsEqual
        · exact localIndicesEqual
      have cycleIndicesEqual :=
        allCycleClauseMetadata_lookup_key_injective
          source sourcePlacement firstLookup secondLookup keysEqual
      dsimp [boundary] at firstOccurrence secondOccurrence
      omega

end PeriodicEightOccurrenceSplitPositioned
end LeanTrominoes
