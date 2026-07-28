import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedClausePositions
import LeanTrominoes.PeriodicCNFPlanarAtomNormalizationDegree
import LeanTrominoes.PeriodicCNFPlanarCrossoverNormalizationDegree
import LeanTrominoes.PeriodicCNFPlanarNormalizationComponents

/-!
# Non-carrier clause orbits in the gauged periodic planar-SAT drawing

This module proves that two valid non-carrier drawing clauses with the same
fundamental-domain residue become the same anchor-normalized periodic clause.
It classifies crossover, bend, routed-clause, and routed-variable gadgets by
their local clause offsets, rules out collisions between incompatible gadget
kinds, and transfers the result through opaque variable wrapping and the
canonical variable gauge.
-/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

theorem variableGauge_anchorNormalize_anchorNormalize
    {Variable : Type*}
    (gauge : Variable → Cell)
    (clause : PeriodicClause Variable) :
    ((clause.anchorNormalize).variableGauge gauge).anchorNormalize =
      (clause.variableGauge gauge).anchorNormalize := by
  cases clause with
  | nil =>
      rfl
  | cons first rest =>
      rcases first with ⟨firstAtom, ⟨anchorX, anchorY⟩, firstValue⟩
      rcases gauge firstAtom with ⟨gaugeX, gaugeY⟩
      simp [PeriodicClause.anchorNormalize,
        PeriodicClause.variableGauge,
        PeriodicLiteral.anchorNormalize,
        PeriodicLiteral.variableGauge,
        PeriodicCNF.clauseAnchor,
        List.map_map, Function.comp_def,
        Cell.add, Cell.sub]
      intro literal literalMember
      constructor <;> ring

theorem variableGauge_anchorNormalize_eq_of_anchorNormalize_eq
    {Variable : Type*}
    (gauge : Variable → Cell)
    {first second : PeriodicClause Variable}
    (normalizedEq :
      first.anchorNormalize = second.anchorNormalize) :
    (first.variableGauge gauge).anchorNormalize =
      (second.variableGauge gauge).anchorNormalize := by
  calc
    (first.variableGauge gauge).anchorNormalize =
        ((first.anchorNormalize).variableGauge gauge).anchorNormalize :=
      (variableGauge_anchorNormalize_anchorNormalize
        gauge first).symm
    _ =
        ((second.anchorNormalize).variableGauge gauge).anchorNormalize :=
      congrArg
        (fun clause =>
          (clause.variableGauge gauge).anchorNormalize)
        normalizedEq
    _ = (second.variableGauge gauge).anchorNormalize :=
      variableGauge_anchorNormalize_anchorNormalize gauge second

theorem clauseAnchor_eq_zero_of_mem_deduplicate_anchorNormalize
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (clause : PositionedPeriodicClause Variable)
    (clauseMember :
      clause ∈
        (source.anchorNormalize placement).deduplicateByLiterals.clauses) :
    PeriodicCNF.clauseAnchor clause.literals = (0, 0) := by
  have literalsMember :
      clause.literals ∈
        (source.anchorNormalize
          placement).deduplicateByLiterals.erase.clauses := by
    exact List.mem_map.mpr ⟨clause, clauseMember, rfl⟩
  rw [PositionedPeriodicCNF.erase_deduplicateByLiterals,
    PositionedPeriodicCNF.erase_anchorNormalize] at literalsMember
  have normalizedMember :
      clause.literals ∈ source.erase.anchorNormalize.clauses := by
    simpa using literalsMember
  rcases List.mem_map.mp normalizedMember with
    ⟨sourceClause, sourceClauseMember, literalsEq⟩
  rw [← literalsEq]
  exact PeriodicClause.clauseAnchor_anchorNormalize sourceClause

theorem deduplicated_canonicalClausePosition_eq_position
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable))
    (clauseMember :
      clause ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses) :
    PositionedPeriodicCNF.canonicalClausePosition
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
        clause =
      clause.position := by
  have anchorZero :=
    clauseAnchor_eq_zero_of_mem_deduplicate_anchorNormalize
      (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
      clause
      (by
        simpa only [
          retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula,
          retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula]
          using clauseMember)
  simp [PositionedPeriodicCNF.canonicalClausePosition,
    anchorZero, PeriodicVariablePlacement.translation,
    Cell.sub, Cell.scale]

theorem deduplicated_canonicalClausePositions_eq_stored
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).clauses.map
        (PositionedPeriodicCNF.canonicalClausePosition
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)) =
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).clauses.map PositionedPeriodicClause.position := by
  apply List.map_congr_left
  intro clause clauseMember
  exact deduplicated_canonicalClausePosition_eq_position
    formula clause clauseMember

def metadataGaugedNormalizedClause
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (metadata : DrawingPlanarSATClauseMetadata Variable) :
    PeriodicClause (WrappedPeriodicPlanarSATVariable Variable) :=
  ((wrapPeriodicPlanarSATClause
    (periodicizePlanarSATClause formula metadata.clause)).variableGauge
      (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
        formula)).anchorNormalize

theorem anchorNormalized_clauses_eq_metadata
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).clauses =
      (retainedDrawingPlanarSATClauseMetadata formula).map
        (fun metadata =>
          (⟨clauseResidue formula metadata.clause,
            metadataGaugedNormalizedClause formula metadata⟩ :
            PositionedPeriodicClause
              (WrappedPeriodicPlanarSATVariable Variable))) := by
  unfold
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
    retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
    retainedWrappedDrawingPositionedPeriodicPlanarSATFormula
    retainedDrawingPositionedPeriodicPlanarSATFormula
    positionPeriodicizedPlanarSATFormula
    PositionedPeriodicCNF.anchorNormalize
    PositionedPeriodicCNF.variableGauge
    PositionedPeriodicCNF.rename
  rw [← retainedDrawingPlanarSATClauseMetadata_clauses]
  simp only [List.map_map]
  apply List.map_congr_left
  intro metadata metadataMember
  rw [PositionedPeriodicClause.mk.injEq]
  constructor
  · change
      PositionedPeriodicCNF.canonicalClausePosition
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
          ⟨metadata.clause.position,
            (wrapPeriodicPlanarSATClause
              (periodicizePlanarSATClause formula
                metadata.clause)).variableGauge
                  (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
                    formula)⟩ =
        clauseResidue formula metadata.clause
    apply metadata_canonicalClausePosition_eq_residue
      wellFormed degree isLocal metadata
    · exact retainedDrawingPlanarSATClauseMetadata_valid
        formula metadataMember
    · exact clausesNonempty metadata.clause
        (by
          rw [← retainedDrawingPlanarSATClauseMetadata_clauses]
          exact List.mem_map.mpr
            ⟨metadata, metadataMember, rfl⟩)
  · rfl

theorem cell_eq_add_scale_of_emod_eq
    (period : Int) {first second : Cell}
    (horizontal :
      first.1 % period = second.1 % period)
    (vertical :
      first.2 % period = second.2 % period) :
    first =
      Cell.add second
        (Cell.scale period
          (first.1 / period - second.1 / period,
            first.2 / period - second.2 / period)) := by
  have firstHorizontal :=
    Int.emod_add_mul_ediv first.1 period
  have secondHorizontal :=
    Int.emod_add_mul_ediv second.1 period
  have firstVertical :=
    Int.emod_add_mul_ediv first.2 period
  have secondVertical :=
    Int.emod_add_mul_ediv second.2 period
  apply Prod.ext
  · simp only [Cell.add, Cell.scale]
    calc
      first.1 =
          first.1 % period +
            period * (first.1 / period) :=
        firstHorizontal.symm
      _ =
          second.1 % period +
            period * (first.1 / period) := by
        rw [horizontal]
      _ =
          second.1 +
            period *
              (first.1 / period - second.1 / period) := by
        linear_combination secondHorizontal
  · simp only [Cell.add, Cell.scale]
    calc
      first.2 =
          first.2 % period +
            period * (first.2 / period) :=
        firstVertical.symm
      _ =
          second.2 % period +
            period * (first.2 / period) := by
        rw [vertical]
      _ =
          second.2 +
            period *
              (first.2 / period - second.2 / period) := by
        linear_combination secondVertical

theorem clausePosition_eq_translate_of_residue_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {first second : EmbeddedClause (PlanarSATVariable Variable)}
    (residueEq :
      clauseResidue formula first =
        clauseResidue formula second) :
    ∃ shift,
      first.position =
        Cell.add second.position
          (Cell.scale
            (drawingPeriodicPlanarSATPlacement formula).period
            shift) := by
  let period : Int :=
    (drawingPeriodicPlanarSATPlacement formula).period
  let shift : Cell :=
    (first.position.1 / period - second.position.1 / period,
      first.position.2 / period - second.position.2 / period)
  refine ⟨shift, ?_⟩
  have horizontal :
      first.position.1 % period =
        second.position.1 % period :=
    congrArg Prod.fst residueEq
  have vertical :
      first.position.2 % period =
        second.position.2 % period :=
    congrArg Prod.snd residueEq
  have equal :=
    cell_eq_add_scale_of_emod_eq
      period horizontal vertical
  simpa [period, shift] using equal

theorem inPlanarSATMacrocell_translate
    {center point shift : Cell} (factor : Int)
    (bounded : InPlanarSATMacrocell center point) :
    InPlanarSATMacrocell
      (Cell.add center (Cell.scale factor shift))
      (Cell.add point
        (Cell.scale (planarMacroScale * factor) shift)) := by
  rcases center with ⟨centerX, centerY⟩
  rcases point with ⟨pointX, pointY⟩
  rcases shift with ⟨shiftX, shiftY⟩
  norm_num [InPlanarSATMacrocell,
    planarSATMacrocellRouteLower,
    planarSATMacrocellRouteUpper,
    InClosedGridRectangle, Cell.add, Cell.scale,
    planarMacroScale] at bounded ⊢
  ring_nf at ⊢
  omega

theorem noncarrier_macrocellCenter_eq_translate_of_residue_eq
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
    (firstCenter secondCenter : Cell)
    (firstCenterEq :
      first.source.component.macrocellCenter formula =
        some firstCenter)
    (secondCenterEq :
      second.source.component.macrocellCenter formula =
        some secondCenter)
    (firstNonempty : first.clause.literals ≠ [])
    (secondNonempty : second.clause.literals ≠ [])
    (residueEq :
      clauseResidue formula first.clause =
        clauseResidue formula second.clause) :
    ∃ shift,
      firstCenter =
        Cell.add secondCenter
          (Cell.scale
            (drawingGridSize
              (PeriodicCNF.incidenceGraph formula))
            shift) := by
  rcases clausePosition_eq_translate_of_residue_eq
      formula residueEq with
    ⟨shift, positionEq⟩
  refine ⟨shift, ?_⟩
  have firstBounded :=
    first.retainedClausePosition_in_macrocell
      wellFormed degree isLocal firstValid
      firstCenter firstCenterEq firstNonempty
  have secondBounded :=
    second.retainedClausePosition_in_macrocell
      wellFormed degree isLocal secondValid
      secondCenter secondCenterEq secondNonempty
  have translatedSecondBounded :=
    inPlanarSATMacrocell_translate
      (drawingGridSize
        (PeriodicCNF.incidenceGraph formula))
      (shift := shift) secondBounded
  apply planarSATMacrocellCenter_eq_of_common_point
    firstBounded
  rw [positionEq]
  simpa [drawingPeriodicPlanarSATPlacement,
    planarMacroScale] using translatedSecondBounded

theorem periodNormalize_point_eq_emod
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (record : CrossingRecord) :
    (record.periodNormalize graph).point =
      (record.point.1 % drawingGridSize graph,
        record.point.2 % drawingGridSize graph) := by
  have horizontal :=
    Int.emod_add_mul_ediv record.point.1
      (drawingGridSize graph : Int)
  have vertical :=
    Int.emod_add_mul_ediv record.point.2
      (drawingGridSize graph : Int)
  apply Prod.ext <;>
    simp only [CrossingRecord.periodNormalize,
      PeriodicGridDrawing.normalizePoint,
      PeriodicGridDrawing.periodTranslation,
      crossingPeriodShift, drawing_gridSize,
      Cell.sub, Cell.scale] <;>
    omega

theorem periodNormalize_eq_of_point_eq_translate
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : CrossingRecord}
    (firstMem : first ∈ orientedCrossingHalo graph)
    (secondMem : second ∈ orientedCrossingHalo graph)
    (shift : Cell)
    (pointEq :
      first.point =
        Cell.add second.point
          ((drawing graph).periodTranslation shift)) :
    first.periodNormalize graph =
      second.periodNormalize graph := by
  have normalizedPointEq :
      (first.periodNormalize graph).point =
        (second.periodNormalize graph).point := by
    rw [periodNormalize_point_eq_emod,
      periodNormalize_point_eq_emod]
    apply Prod.ext
    · have coordinateEq := congrArg Prod.fst pointEq
      simp only [Cell.add,
        PeriodicGridDrawing.periodTranslation,
        Cell.scale, drawing_gridSize] at coordinateEq
      rw [coordinateEq, Int.add_mul_emod_self_left]
    · have coordinateEq := congrArg Prod.snd pointEq
      simp only [Cell.add,
        PeriodicGridDrawing.periodTranslation,
        Cell.scale, drawing_gridSize] at coordinateEq
      rw [coordinateEq, Int.add_mul_emod_self_left]
  apply orientedCrossing_eq_of_point_eq
    wellFormed degree isLocal
  · exact orientedCrossings_subset_orientedCrossingHalo graph
      (periodNormalize_mem_orientedCrossings
        wellFormed degree isLocal firstMem)
  · exact orientedCrossings_subset_orientedCrossingHalo graph
      (periodNormalize_mem_orientedCrossings
        wellFormed degree isLocal secondMem)
  · exact normalizedPointEq

theorem liftedIncidenceVertex_eq_of_position_eq_translate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {firstVertex secondVertex : CNFVertex Variable}
    (firstVertexMem :
      firstVertex ∈
        (PeriodicCNF.incidenceGraph formula).vertices)
    (secondVertexMem :
      secondVertex ∈
        (PeriodicCNF.incidenceGraph formula).vertices)
    (firstTranslate secondTranslate shift : Cell)
    (positionEq :
      liftedIncidenceVertexPosition formula
          firstVertex firstTranslate =
        Cell.add
          (liftedIncidenceVertexPosition formula
            secondVertex secondTranslate)
          ((drawing
            (PeriodicCNF.incidenceGraph formula)).periodTranslation
              shift)) :
    firstVertex = secondVertex := by
  let graph := PeriodicCNF.incidenceGraph formula
  have translatedEq :
      Cell.add
          ((drawing graph).vertexPosition graph firstVertex)
          ((drawing graph).periodTranslation firstTranslate) =
        Cell.add
          ((drawing graph).vertexPosition graph secondVertex)
          ((drawing graph).periodTranslation
            (Cell.add secondTranslate shift)) := by
    rw [show
      Cell.add
          ((drawing graph).vertexPosition graph firstVertex)
          ((drawing graph).periodTranslation firstTranslate) =
        liftedIncidenceVertexPosition formula
          firstVertex firstTranslate by
      rfl]
    rw [positionEq]
    simp [liftedIncidenceVertexPosition, graph,
      PeriodicGridDrawing.periodTranslation,
      Cell.add, Cell.scale]
    constructor <;> ring
  exact
    (liftedDrawingVertexPosition_eq
      graph firstVertexMem secondVertexMem translatedEq).1

theorem normalizedDrawingRouteBendLink_eq_of_drawingPoint_eq_translate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : RouteBend}
    (firstMem : first ∈ drawingRouteBends graph)
    (secondMem : second ∈ drawingRouteBends graph)
    (shift : Cell)
    (pointEq :
      first.drawingPoint graph =
        Cell.add
          (second.drawingPoint graph)
          ((drawing graph).periodTranslation shift)) :
    PeriodicEquality.normalizeLink (normalizeCarrierNode graph)
        (first.equalityLink graph) =
      PeriodicEquality.normalizeLink (normalizeCarrierNode graph)
        (second.equalityLink graph) := by
  rcases drawingRouteBend_centerPlacement
      graph isLocal firstMem with
    ⟨firstEdge, firstEdgeIndex,
      firstPlacement, firstPlacementIndex,
      firstEdgeMem, firstPlacementMem,
      firstRouteEq, firstIndexEq, firstPointEq⟩
  rcases drawingRouteBend_centerPlacement
      graph isLocal secondMem with
    ⟨secondEdge, secondEdgeIndex,
      secondPlacement, secondPlacementIndex,
      secondEdgeMem, secondPlacementMem,
      secondRouteEq, secondIndexEq, secondPointEq⟩
  have firstPlacementListMem :
      firstPlacement ∈
        routeBendCenterPlacements
          graph firstEdge firstEdgeIndex :=
    List.fst_mem_of_mem_zipIdx firstPlacementMem
  have secondPlacementListMem :
      secondPlacement ∈
        routeBendCenterPlacements
          graph secondEdge secondEdgeIndex :=
    List.fst_mem_of_mem_zipIdx secondPlacementMem
  have firstValid :=
    routeBendCenterPlacements_kind_valid
      firstEdgeMem firstPlacementListMem
  have secondValid :=
    routeBendCenterPlacements_kind_valid
      secondEdgeMem secondPlacementListMem
  have normalizedPointEq :
      Cell.add
          (firstPlacement.kind.position graph)
          ((drawing graph).periodTranslation
            (Cell.add first.translate firstPlacement.offset)) =
        Cell.add
          (secondPlacement.kind.position graph)
          ((drawing graph).periodTranslation
            (Cell.add
              (Cell.add second.translate secondPlacement.offset)
              shift)) := by
    rw [← firstPointEq, pointEq, secondPointEq]
    simp [PeriodicGridDrawing.periodTranslation,
      Cell.add, Cell.scale]
    constructor <;> ring
  have normalizedUnique :=
    PeriodicGridDrawing.translatedHalfOpenPositions_eq
      (drawing graph)
      (RouteBendCenterKind.position_in_fundamental
        wellFormed degree firstValid)
      (RouteBendCenterKind.position_in_fundamental
        wellFormed degree secondValid)
      normalizedPointEq
  have kindEq :
      firstPlacement.kind = secondPlacement.kind :=
    RouteBendCenterKind.eq_of_position_eq
      wellFormed degree firstValid secondValid
        normalizedUnique.1
  have firstKindIndex :=
    routeBendCenterPlacements_kind_edgeIndex
      graph firstEdge firstEdgeIndex firstPlacementListMem
  have secondKindIndex :=
    routeBendCenterPlacements_kind_edgeIndex
      graph secondEdge secondEdgeIndex secondPlacementListMem
  have edgeIndexEq :
      firstEdgeIndex = secondEdgeIndex :=
    firstKindIndex.symm.trans
      ((congrArg RouteBendCenterKind.edgeIndex kindEq).trans
        secondKindIndex)
  have taggedEdgeEq :
      (firstEdge, firstEdgeIndex) =
        (secondEdge, secondEdgeIndex) :=
    tagged_eq_of_mem_zipIdx_of_snd_eq
      firstEdgeMem secondEdgeMem edgeIndexEq
  have edgeEq : firstEdge = secondEdge :=
    congrArg Prod.fst taggedEdgeEq
  subst secondEdge
  rw [← edgeIndexEq] at secondPlacementMem
  have taggedPlacementEq :
      (firstPlacement, firstPlacementIndex) =
        (secondPlacement, secondPlacementIndex) :=
    routeBendCenterPlacements_tagged_eq_of_kind_eq
      graph firstEdge firstEdgeIndex
        firstPlacementMem secondPlacementMem kindEq
  have placementIndexEq :
      firstPlacementIndex = secondPlacementIndex :=
    congrArg Prod.snd taggedPlacementEq
  have eraseEq :=
    drawingRouteBends_eraseTranslation_eq_of_identity_eq
      graph firstMem secondMem
      (firstRouteEq.trans (edgeIndexEq.trans secondRouteEq.symm))
      (firstIndexEq.trans
        (placementIndexEq.trans secondIndexEq.symm))
  rw [first.normalize_equalityLink_eq_eraseTranslation,
    second.normalize_equalityLink_eq_eraseTranslation,
    eraseEq]

theorem anchorNormalized_periodicizedEqualityClause_eq
    {Source Target : Type*}
    (normalize : Source → Target × Cell)
    {firstLink secondLink : EqualityLink Source}
    {firstClause secondClause : EmbeddedClause Source}
    {firstIndex secondIndex : Nat}
    (firstMember :
      (firstClause, firstIndex) ∈
        (equalityInstance firstLink.first firstLink.second
          firstLink.positions).zipIdx)
    (secondMember :
      (secondClause, secondIndex) ∈
        (equalityInstance secondLink.first secondLink.second
          secondLink.positions).zipIdx)
    (linkEq :
      PeriodicEquality.normalizeLink normalize firstLink =
        PeriodicEquality.normalizeLink normalize secondLink)
    (indexEq : firstIndex = secondIndex) :
    (PeriodicEquality.periodicizeClause
        normalize firstClause).anchorNormalize =
      (PeriodicEquality.periodicizeClause
        normalize secondClause).anchorNormalize := by
  have firstLookup :
      (((equalityInstance
        firstLink.first firstLink.second
        firstLink.positions).map
          (PeriodicEquality.periodicizeClause normalize)).map
            PeriodicClause.anchorNormalize)[firstIndex]? =
        some
          ((PeriodicEquality.periodicizeClause
            normalize firstClause).anchorNormalize) := by
    rw [List.getElem?_map, List.getElem?_map,
      (List.mk_mem_zipIdx_iff_getElem?).mp firstMember]
    rfl
  have secondLookup :
      (((equalityInstance
        secondLink.first secondLink.second
        secondLink.positions).map
          (PeriodicEquality.periodicizeClause normalize)).map
            PeriodicClause.anchorNormalize)[secondIndex]? =
        some
          ((PeriodicEquality.periodicizeClause
            normalize secondClause).anchorNormalize) := by
    rw [List.getElem?_map, List.getElem?_map,
      (List.mk_mem_zipIdx_iff_getElem?).mp secondMember]
    rfl
  rw [PeriodicEquality.equalityInstance_normalized] at firstLookup
  rw [PeriodicEquality.equalityInstance_normalized] at secondLookup
  rw [linkEq, indexEq] at firstLookup
  exact Option.some.inj (firstLookup.symm.trans secondLookup)

theorem normalizedRoutedVariableLink_eq_of_atom_eq_of_arm_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (firstSite secondSite : VariableRouteSite Variable)
    {firstLink secondLink :
      EqualityLink (PlanarSATNode Variable)}
    (firstMem :
      firstLink ∈ routedVariableLinksAt formula firstSite)
    (secondMem :
      secondLink ∈ routedVariableLinksAt formula secondSite)
    (atomEq : firstSite.1 = secondSite.1)
    (armEq :
      firstLink.first.duplicatorArm =
        secondLink.first.duplicatorArm) :
    PeriodicEquality.normalizeLink
        (normalizePlanarSATNode
          (PeriodicCNF.incidenceGraph formula)) firstLink =
      PeriodicEquality.normalizeLink
        (normalizePlanarSATNode
          (PeriodicCNF.incidenceGraph formula)) secondLink := by
  have firstNodeMem :
      firstLink.first ∈ routedVariableNodes formula firstSite := by
    rcases List.mem_map.mp firstMem with
      ⟨taggedNode, taggedNodeMem, linkEq⟩
    subst firstLink
    exact List.mem_of_mem_take
      (List.fst_mem_of_mem_zipIdx taggedNodeMem)
  have secondNodeMem :
      secondLink.first ∈ routedVariableNodes formula secondSite := by
    rcases List.mem_map.mp secondMem with
      ⟨taggedNode, taggedNodeMem, linkEq⟩
    subst secondLink
    exact List.mem_of_mem_take
      (List.fst_mem_of_mem_zipIdx taggedNodeMem)
  have firstSecondEq :
      firstLink.second = .atom firstSite := by
    rcases List.mem_map.mp firstMem with
      ⟨taggedNode, taggedNodeMem, linkEq⟩
    subst firstLink
    rfl
  have secondSecondEq :
      secondLink.second = .atom secondSite := by
    rcases List.mem_map.mp secondMem with
      ⟨taggedNode, taggedNodeMem, linkEq⟩
    subst secondLink
    rfl
  rcases (mem_routedVariableNodes_iff
      formula firstSite firstLink.first).mp firstNodeMem with
    ⟨firstOccurrence, firstOccurrenceAtMem, firstFirstEq⟩
  rcases (mem_routedVariableNodes_iff
      formula secondSite secondLink.first).mp secondNodeMem with
    ⟨secondOccurrence, secondOccurrenceAtMem, secondFirstEq⟩
  have firstData :=
    variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula firstSite firstOccurrenceAtMem
  have secondData :=
    variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula secondSite secondOccurrenceAtMem
  have firstEdgeMem :=
    firstOccurrence.edge_mem_of_mem_drawing formula firstData.1
  have secondEdgeMem :=
    secondOccurrence.edge_mem_of_mem_drawing formula secondData.1
  let graph := PeriodicCNF.incidenceGraph formula
  let firstPort :=
    targetPort firstOccurrence.edge firstOccurrence.edgeIndex
  let secondPort :=
    targetPort secondOccurrence.edge secondOccurrence.edgeIndex
  have firstPortMem : firstPort ∈ allPorts graph :=
    targetPort_mem_allPorts graph firstEdgeMem
  have secondPortMem : secondPort ∈ allPorts graph :=
    targetPort_mem_allPorts graph secondEdgeMem
  rw [firstFirstEq, secondFirstEq] at armEq
  change
    (firstOccurrence.targetTerminal formula).duplicatorArm =
      (secondOccurrence.targetTerminal formula).duplicatorArm
    at armEq
  rw [firstOccurrence.targetTerminal_duplicatorArm formula,
    secondOccurrence.targetTerminal_duplicatorArm formula] at armEq
  have rankEq :
      portRank graph firstPort =
        portRank graph secondPort := by
    apply targetDuplicatorArm_injective_below_three
    · exact portRank_lt_three degree firstPortMem
    · exact portRank_lt_three degree secondPortMem
    · exact armEq
  have targetVertexEq :
      firstPort.vertex = secondPort.vertex := by
    have occurrenceAtomEq :
        firstOccurrence.incidence.literal.atom =
          secondOccurrence.incidence.literal.atom :=
      (congrArg Prod.fst firstData.2).trans
        (atomEq.trans (congrArg Prod.fst secondData.2).symm)
    dsimp [firstPort, secondPort]
    change
      CNFVertex.variable
          firstOccurrence.incidence.literal.atom =
        CNFVertex.variable
          secondOccurrence.incidence.literal.atom
    exact congrArg CNFVertex.variable occurrenceAtomEq
  have portXEq :
      portX graph firstPort = portX graph secondPort := by
    unfold portX
    rw [targetVertexEq, rankEq]
  have portEq : firstPort = secondPort :=
    portX_injective_on_allPorts
      wellFormed degree firstPortMem secondPortMem portXEq
  have edgeIndexEq :
      firstOccurrence.edgeIndex =
        secondOccurrence.edgeIndex :=
    congrArg GraphPort.edgeIndex portEq
  have incidenceEq :=
    CNFRouteOccurrence.incidence_eq_of_edgeIndex_eq
      formula firstData.1 secondData.1 edgeIndexEq
  have targetIndexedEq :=
    CNFRouteOccurrence.targetTerminal_indexed_eq_of_data_eq
      formula incidenceEq edgeIndexEq
  have edgeEq :
      firstOccurrence.edge = secondOccurrence.edge :=
    congrArg CNFIncidence.edge incidenceEq
  rw [
    normalizeRoutedVariableLink_eq_of_witness
      formula firstData.2 firstFirstEq firstSecondEq,
    normalizeRoutedVariableLink_eq_of_witness
      formula secondData.2 secondFirstEq secondSecondEq,
    targetIndexedEq, incidenceEq, edgeEq]

theorem localOffset_eq_of_position_eq_translate
    {firstPosition secondPosition firstCenter secondCenter
      firstOffset secondOffset shift : Cell}
    (periodFactor : Int)
    (firstPositionEq :
      firstPosition =
        Cell.add
          (Cell.scale planarMacroScale firstCenter)
          firstOffset)
    (secondPositionEq :
      secondPosition =
        Cell.add
          (Cell.scale planarMacroScale secondCenter)
          secondOffset)
    (centerEq :
      firstCenter =
        Cell.add secondCenter
          (Cell.scale periodFactor shift))
    (positionEq :
      firstPosition =
        Cell.add secondPosition
          (Cell.scale
            (planarMacroScale * periodFactor) shift)) :
    firstOffset = secondOffset := by
  rcases firstPosition with ⟨firstPositionX, firstPositionY⟩
  rcases secondPosition with ⟨secondPositionX, secondPositionY⟩
  rcases firstCenter with ⟨firstCenterX, firstCenterY⟩
  rcases secondCenter with ⟨secondCenterX, secondCenterY⟩
  rcases firstOffset with ⟨firstOffsetX, firstOffsetY⟩
  rcases secondOffset with ⟨secondOffsetX, secondOffsetY⟩
  rcases shift with ⟨shiftX, shiftY⟩
  apply Prod.ext
  · have firstPositionXEq := congrArg Prod.fst firstPositionEq
    have secondPositionXEq := congrArg Prod.fst secondPositionEq
    have centerXEq := congrArg Prod.fst centerEq
    have positionXEq := congrArg Prod.fst positionEq
    simp [Cell.add, Cell.scale, planarMacroScale] at firstPositionXEq secondPositionXEq centerXEq positionXEq ⊢
    ring_nf at firstPositionXEq secondPositionXEq centerXEq positionXEq
    omega
  · have firstPositionYEq := congrArg Prod.snd firstPositionEq
    have secondPositionYEq := congrArg Prod.snd secondPositionEq
    have centerYEq := congrArg Prod.snd centerEq
    have positionYEq := congrArg Prod.snd positionEq
    simp [Cell.add, Cell.scale, planarMacroScale] at firstPositionYEq secondPositionYEq centerYEq positionYEq ⊢
    ring_nf at firstPositionYEq secondPositionYEq centerYEq positionYEq
    omega

def crossoverClauseLocalPositions : List Cell :=
  crossoverFormula.map EmbeddedClause.position

theorem crossoverClauseLocalPositions_nodup :
    crossoverClauseLocalPositions.Nodup := by
  native_decide

theorem crossoverClause_localOffset_eq
    {Variable : Type*}
    {firstCrossing secondCrossing : CrossingRecord}
    {firstClause secondClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {firstIndex secondIndex : Nat}
    (firstMember :
      (firstClause, firstIndex) ∈
        (drawingPlanarSATCrossoverFormulaAt
          (Variable := Variable) firstCrossing).zipIdx)
    (secondMember :
      (secondClause, secondIndex) ∈
        (drawingPlanarSATCrossoverFormulaAt
          (Variable := Variable) secondCrossing).zipIdx)
    {firstOffset secondOffset : Cell}
    (firstPositionEq :
      firstClause.position =
        Cell.add (crossingMacroOrigin firstCrossing) firstOffset)
    (secondPositionEq :
      secondClause.position =
        Cell.add (crossingMacroOrigin secondCrossing) secondOffset) :
    firstOffset = secondOffset ↔ firstIndex = secondIndex := by
  have firstSource :
      (firstOffset, firstIndex) ∈
        crossoverClauseLocalPositions.zipIdx := by
    unfold drawingPlanarSATCrossoverFormulaAt
      scopedCrossoverInstance instantiateFormula at firstMember
    rw [List.zipIdx_map, List.zipIdx_map] at firstMember
    rcases List.mem_map.mp firstMember with
      ⟨firstTagged, firstTaggedMember, firstTaggedEq⟩
    rcases List.mem_map.mp firstTaggedMember with
      ⟨firstSource, firstSourceMember, firstSourceEq⟩
    have firstOffsetEq :
        firstOffset = firstSource.1.position := by
      have outerPositionEq :=
        congrArg
          (fun tagged =>
            (tagged.1.position : Cell))
          firstTaggedEq
      have innerPositionEq :=
        congrArg
          (fun tagged =>
            (tagged.1.position : Cell))
          firstSourceEq
      simp [EmbeddedClause.rename, EmbeddedClause.place,
        EmbeddedClause.map] at outerPositionEq innerPositionEq
      rw [← outerPositionEq, ← innerPositionEq] at firstPositionEq
      apply Prod.ext
      · have coordinateEq := congrArg Prod.fst firstPositionEq
        simp [Cell.add, Cell.scale] at coordinateEq ⊢
        omega
      · have coordinateEq := congrArg Prod.snd firstPositionEq
        simp [Cell.add, Cell.scale] at coordinateEq ⊢
        omega
    have firstIndexEq :
        firstIndex = firstSource.2 :=
      (congrArg Prod.snd firstTaggedEq).symm.trans
        (congrArg Prod.snd firstSourceEq).symm
    subst firstOffset
    subst firstIndex
    rw [crossoverClauseLocalPositions,
      List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨firstSource, firstSourceMember, rfl⟩
  have secondSource :
      (secondOffset, secondIndex) ∈
        crossoverClauseLocalPositions.zipIdx := by
    unfold drawingPlanarSATCrossoverFormulaAt
      scopedCrossoverInstance instantiateFormula at secondMember
    rw [List.zipIdx_map, List.zipIdx_map] at secondMember
    rcases List.mem_map.mp secondMember with
      ⟨secondTagged, secondTaggedMember, secondTaggedEq⟩
    rcases List.mem_map.mp secondTaggedMember with
      ⟨secondSource, secondSourceMember, secondSourceEq⟩
    have secondOffsetEq :
        secondOffset = secondSource.1.position := by
      have outerPositionEq :=
        congrArg
          (fun tagged =>
            (tagged.1.position : Cell))
          secondTaggedEq
      have innerPositionEq :=
        congrArg
          (fun tagged =>
            (tagged.1.position : Cell))
          secondSourceEq
      simp [EmbeddedClause.rename, EmbeddedClause.place,
        EmbeddedClause.map] at outerPositionEq innerPositionEq
      rw [← outerPositionEq, ← innerPositionEq] at secondPositionEq
      apply Prod.ext
      · have coordinateEq := congrArg Prod.fst secondPositionEq
        simp [Cell.add, Cell.scale] at coordinateEq ⊢
        omega
      · have coordinateEq := congrArg Prod.snd secondPositionEq
        simp [Cell.add, Cell.scale] at coordinateEq ⊢
        omega
    have secondIndexEq :
        secondIndex = secondSource.2 :=
      (congrArg Prod.snd secondTaggedEq).symm.trans
        (congrArg Prod.snd secondSourceEq).symm
    subst secondOffset
    subst secondIndex
    rw [crossoverClauseLocalPositions,
      List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨secondSource, secondSourceMember, rfl⟩
  constructor
  · intro offsetEq
    subst secondOffset
    exact List.Nodup.index_eq_of_getElem?_eq_some
      crossoverClauseLocalPositions_nodup
      ((List.mk_mem_zipIdx_iff_getElem?).mp firstSource)
      ((List.mk_mem_zipIdx_iff_getElem?).mp secondSource)
  · intro indexEq
    exact congrArg Prod.fst
      (tagged_eq_of_mem_zipIdx_of_snd_eq
        firstSource secondSource indexEq)

theorem bendClause_localOffset_eq
    {Variable Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {firstBend secondBend : RouteBend}
    {firstClause secondClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {firstIndex secondIndex : Nat}
    (firstMember :
      (firstClause, firstIndex) ∈
        (drawingPlanarSATBendFormulaAt
          (Variable := Variable) graph firstBend).zipIdx)
    (secondMember :
      (secondClause, secondIndex) ∈
        (drawingPlanarSATBendFormulaAt
          (Variable := Variable) graph secondBend).zipIdx)
    {firstOffset secondOffset : Cell}
    (firstPositionEq :
      firstClause.position =
        Cell.add
          (Cell.scale planarMacroScale
            (firstBend.drawingPoint graph))
          firstOffset)
    (secondPositionEq :
      secondClause.position =
        Cell.add
          (Cell.scale planarMacroScale
            (secondBend.drawingPoint graph))
          secondOffset) :
    firstOffset = secondOffset ↔ firstIndex = secondIndex := by
  rcases firstOffset with ⟨firstOffsetX, firstOffsetY⟩
  rcases secondOffset with ⟨secondOffsetX, secondOffsetY⟩
  have firstIndexLt := List.snd_lt_of_mem_zipIdx firstMember
  have secondIndexLt := List.snd_lt_of_mem_zipIdx secondMember
  simp [drawingPlanarSATBendFormulaAt,
    drawingPlanarSATCarrierFormulaAt, equalityInstance] at firstIndexLt secondIndexLt
  interval_cases firstIndex <;>
    interval_cases secondIndex <;>
    simp_all [drawingPlanarSATBendFormulaAt,
      drawingPlanarSATCarrierFormulaAt, equalityInstance,
      RouteBend.equalityLink, routeBendEqualityPositions,
      EmbeddedClause.rename, EmbeddedClause.map,
      Cell.add, Cell.scale, planarMacroScale] <;>
    omega

def routedVariableClauseLocalOffset
    (input : DuplicatorArm × Fin 2) : Cell :=
  if input.2.1 = 0 then
    (duplicatorArmEqualityPositions input.1).forward
  else
    (duplicatorArmEqualityPositions input.1).backward

theorem routedVariableClauseLocalOffset_injective :
    Function.Injective routedVariableClauseLocalOffset := by
  native_decide

theorem equalityInstance_clausePosition_and_index
    {Variable : Type*}
    {link : EqualityLink Variable}
    {clause : EmbeddedClause Variable}
    {index : Nat}
    (member :
      (clause, index) ∈
        (equalityInstance
          link.first link.second link.positions).zipIdx) :
    (index = 0 ∧ clause.position = link.positions.forward) ∨
      (index = 1 ∧
        clause.position = link.positions.backward) := by
  simp [equalityInstance] at member
  rcases member with ⟨clauseEq, indexEq⟩ |
      ⟨clauseEq, indexEq⟩
  · exact Or.inl
      ⟨indexEq, congrArg EmbeddedClause.position clauseEq⟩
  · exact Or.inr
      ⟨indexEq, congrArg EmbeddedClause.position clauseEq⟩

theorem offset_eq_of_add_eq
    {origin first second point : Cell}
    (firstEq : point = Cell.add origin first)
    (secondEq : point = Cell.add origin second) :
    first = second := by
  rcases origin with ⟨originX, originY⟩
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases point with ⟨pointX, pointY⟩
  apply Prod.ext
  · have firstXEq := congrArg Prod.fst firstEq
    have secondXEq := congrArg Prod.fst secondEq
    simp [Cell.add] at firstXEq secondXEq ⊢
    omega
  · have firstYEq := congrArg Prod.snd firstEq
    have secondYEq := congrArg Prod.snd secondEq
    simp [Cell.add] at firstYEq secondYEq ⊢
    omega

theorem routedVariableClause_localOffset_eq
    {Variable : Type*}
    {firstOrigin secondOrigin : Cell}
    {firstArm secondArm : DuplicatorArm}
    {firstLink secondLink :
      EqualityLink (PlanarSATNode Variable)}
    (firstPositionsEq :
      firstLink.positions =
        ⟨Cell.add firstOrigin
            (duplicatorArmEqualityPositions firstArm).forward,
          Cell.add firstOrigin
            (duplicatorArmEqualityPositions firstArm).backward⟩)
    (secondPositionsEq :
      secondLink.positions =
        ⟨Cell.add secondOrigin
            (duplicatorArmEqualityPositions secondArm).forward,
          Cell.add secondOrigin
            (duplicatorArmEqualityPositions secondArm).backward⟩)
    {firstClause secondClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {firstIndex secondIndex : Nat}
    (firstMember :
      (firstClause, firstIndex) ∈
        (drawingPlanarSATRoutedVariableFormulaAt
          firstLink).zipIdx)
    (secondMember :
      (secondClause, secondIndex) ∈
        (drawingPlanarSATRoutedVariableFormulaAt
          secondLink).zipIdx)
    {firstOffset secondOffset : Cell}
    (firstPositionEq :
      firstClause.position =
        Cell.add firstOrigin firstOffset)
    (secondPositionEq :
      secondClause.position =
        Cell.add secondOrigin secondOffset) :
    firstOffset = secondOffset ↔
      firstArm = secondArm ∧ firstIndex = secondIndex := by
  have firstIndexLt := List.snd_lt_of_mem_zipIdx firstMember
  have secondIndexLt := List.snd_lt_of_mem_zipIdx secondMember
  simp [drawingPlanarSATRoutedVariableFormulaAt,
    equalityInstance] at firstIndexLt secondIndexLt
  let firstFiniteIndex : Fin 2 :=
    ⟨firstIndex, by omega⟩
  let secondFiniteIndex : Fin 2 :=
    ⟨secondIndex, by omega⟩
  have firstOffsetEq :
      firstOffset =
        routedVariableClauseLocalOffset
          (firstArm, firstFiniteIndex) := by
    have sourceMember := firstMember
    unfold drawingPlanarSATRoutedVariableFormulaAt at sourceMember
    rw [List.zipIdx_map] at sourceMember
    rcases List.mem_map.mp sourceMember with
      ⟨sourceTagged, sourceTaggedMember, sourceTaggedEq⟩
    have sourceData :=
      equalityInstance_clausePosition_and_index
        sourceTaggedMember
    rcases sourceData with
        ⟨indexEq, positionEq⟩ |
        ⟨indexEq, positionEq⟩
    · have clausePositionEq :
          firstClause.position =
            Cell.add firstOrigin
              (duplicatorArmEqualityPositions
                firstArm).forward := by
        have mappedPositionEq :=
          congrArg
            (fun tagged => tagged.1.position)
            sourceTaggedEq
        simp [EmbeddedClause.rename,
          EmbeddedClause.map] at mappedPositionEq
        rw [← mappedPositionEq, positionEq, firstPositionsEq]
      have offsetEq :=
        offset_eq_of_add_eq
          firstPositionEq clausePositionEq
      have sourceIndexEq :
          sourceTagged.2 = firstIndex :=
        congrArg Prod.snd sourceTaggedEq
      have firstIndexEq : firstIndex = 0 :=
        sourceIndexEq.symm.trans indexEq
      simpa [routedVariableClauseLocalOffset,
        firstFiniteIndex, firstIndexEq] using offsetEq
    · have clausePositionEq :
          firstClause.position =
            Cell.add firstOrigin
              (duplicatorArmEqualityPositions
                firstArm).backward := by
        have mappedPositionEq :=
          congrArg
            (fun tagged => tagged.1.position)
            sourceTaggedEq
        simp [EmbeddedClause.rename,
          EmbeddedClause.map] at mappedPositionEq
        rw [← mappedPositionEq, positionEq, firstPositionsEq]
      have offsetEq :=
        offset_eq_of_add_eq
          firstPositionEq clausePositionEq
      have sourceIndexEq :
          sourceTagged.2 = firstIndex :=
        congrArg Prod.snd sourceTaggedEq
      have firstIndexEq : firstIndex = 1 :=
        sourceIndexEq.symm.trans indexEq
      simpa [routedVariableClauseLocalOffset,
        firstFiniteIndex, firstIndexEq] using offsetEq
  have secondOffsetEq :
      secondOffset =
        routedVariableClauseLocalOffset
          (secondArm, secondFiniteIndex) := by
    have sourceMember := secondMember
    unfold drawingPlanarSATRoutedVariableFormulaAt at sourceMember
    rw [List.zipIdx_map] at sourceMember
    rcases List.mem_map.mp sourceMember with
      ⟨sourceTagged, sourceTaggedMember, sourceTaggedEq⟩
    have sourceData :=
      equalityInstance_clausePosition_and_index
        sourceTaggedMember
    rcases sourceData with
        ⟨indexEq, positionEq⟩ |
        ⟨indexEq, positionEq⟩
    · have clausePositionEq :
          secondClause.position =
            Cell.add secondOrigin
              (duplicatorArmEqualityPositions
                secondArm).forward := by
        have mappedPositionEq :=
          congrArg
            (fun tagged => tagged.1.position)
            sourceTaggedEq
        simp [EmbeddedClause.rename,
          EmbeddedClause.map] at mappedPositionEq
        rw [← mappedPositionEq, positionEq, secondPositionsEq]
      have offsetEq :=
        offset_eq_of_add_eq
          secondPositionEq clausePositionEq
      have sourceIndexEq :
          sourceTagged.2 = secondIndex :=
        congrArg Prod.snd sourceTaggedEq
      have secondIndexEq : secondIndex = 0 :=
        sourceIndexEq.symm.trans indexEq
      simpa [routedVariableClauseLocalOffset,
        secondFiniteIndex, secondIndexEq] using offsetEq
    · have clausePositionEq :
          secondClause.position =
            Cell.add secondOrigin
              (duplicatorArmEqualityPositions
                secondArm).backward := by
        have mappedPositionEq :=
          congrArg
            (fun tagged => tagged.1.position)
            sourceTaggedEq
        simp [EmbeddedClause.rename,
          EmbeddedClause.map] at mappedPositionEq
        rw [← mappedPositionEq, positionEq, secondPositionsEq]
      have offsetEq :=
        offset_eq_of_add_eq
          secondPositionEq clausePositionEq
      have sourceIndexEq :
          sourceTagged.2 = secondIndex :=
        congrArg Prod.snd sourceTaggedEq
      have secondIndexEq : secondIndex = 1 :=
        sourceIndexEq.symm.trans indexEq
      simpa [routedVariableClauseLocalOffset,
        secondFiniteIndex, secondIndexEq] using offsetEq
  constructor
  · intro offsetEq
    have pairEq :
        (firstArm, firstFiniteIndex) =
          (secondArm, secondFiniteIndex) :=
      routedVariableClauseLocalOffset_injective
        (firstOffsetEq.symm.trans
          (offsetEq.trans secondOffsetEq))
    exact
      ⟨congrArg Prod.fst pairEq,
        congrArg (fun pair => pair.2.1) pairEq⟩
  · rintro ⟨armEq, indexEq⟩
    subst secondArm
    subst secondIndex
    exact firstOffsetEq.trans secondOffsetEq.symm

theorem anchorNormalized_periodicizedCrossoverClause_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {firstCrossing secondCrossing : CrossingRecord}
    {firstClause secondClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {firstIndex secondIndex : Nat}
    (firstMember :
      (firstClause, firstIndex) ∈
        (drawingPlanarSATCrossoverFormulaAt
          (Variable := Variable) firstCrossing).zipIdx)
    (secondMember :
      (secondClause, secondIndex) ∈
        (drawingPlanarSATCrossoverFormulaAt
          (Variable := Variable) secondCrossing).zipIdx)
    (crossingEq :
      firstCrossing.periodNormalize
          (PeriodicCNF.incidenceGraph formula) =
        secondCrossing.periodNormalize
          (PeriodicCNF.incidenceGraph formula))
    (indexEq : firstIndex = secondIndex) :
    (periodicizePlanarSATClause
        formula firstClause).anchorNormalize =
      (periodicizePlanarSATClause
        formula secondClause).anchorNormalize := by
  unfold drawingPlanarSATCrossoverFormulaAt
    scopedCrossoverInstance instantiateFormula at firstMember secondMember
  rw [List.zipIdx_map, List.zipIdx_map] at firstMember secondMember
  rcases List.mem_map.mp firstMember with
    ⟨firstTagged, firstTaggedMember, firstTaggedEq⟩
  rcases List.mem_map.mp firstTaggedMember with
    ⟨firstSource, firstSourceMember, firstSourceEq⟩
  rcases List.mem_map.mp secondMember with
    ⟨secondTagged, secondTaggedMember, secondTaggedEq⟩
  rcases List.mem_map.mp secondTaggedMember with
    ⟨secondSource, secondSourceMember, secondSourceEq⟩
  subst firstTagged
  subst secondTagged
  simp only [Prod.map, id_eq, Prod.mk.injEq] at firstTaggedEq secondTaggedEq
  have sourceIndexEq :
      firstSource.2 = secondSource.2 :=
    firstTaggedEq.2.trans
      (indexEq.trans secondTaggedEq.2.symm)
  have sourceEq :
      firstSource = secondSource :=
    tagged_eq_of_mem_zipIdx_of_snd_eq
      firstSourceMember secondSourceMember sourceIndexEq
  subst secondSource
  rw [← firstTaggedEq.1, ← secondTaggedEq.1,
    normalizedCrossoverClauseAt_eq,
    normalizedCrossoverClauseAt_eq,
    crossingEq]

theorem anchorNormalized_periodicizedCarrierClause_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {firstLink secondLink : EqualityLink CarrierNode}
    {firstClause secondClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {firstIndex secondIndex : Nat}
    (firstMember :
      (firstClause, firstIndex) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) firstLink).zipIdx)
    (secondMember :
      (secondClause, secondIndex) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) secondLink).zipIdx)
    (linkEq :
      PeriodicEquality.normalizeLink
          (normalizeCarrierNode
            (PeriodicCNF.incidenceGraph formula)) firstLink =
        PeriodicEquality.normalizeLink
          (normalizeCarrierNode
            (PeriodicCNF.incidenceGraph formula)) secondLink)
    (indexEq : firstIndex = secondIndex) :
    (periodicizePlanarSATClause
        formula firstClause).anchorNormalize =
      (periodicizePlanarSATClause
        formula secondClause).anchorNormalize := by
  unfold drawingPlanarSATCarrierFormulaAt at firstMember secondMember
  rw [List.zipIdx_map] at firstMember secondMember
  rcases List.mem_map.mp firstMember with
    ⟨firstSource, firstSourceMember, firstSourceEq⟩
  rcases List.mem_map.mp secondMember with
    ⟨secondSource, secondSourceMember, secondSourceEq⟩
  simp only [Prod.map, id_eq, Prod.mk.injEq] at firstSourceEq secondSourceEq
  rw [← firstSourceEq.1, ← secondSourceEq.1,
    periodicizePlanarSATClause_carrier_core_rename,
    periodicizePlanarSATClause_carrier_core_rename,
    ← embedPeriodicCarrierClause_anchorNormalize,
    ← embedPeriodicCarrierClause_anchorNormalize]
  apply congrArg (@embedPeriodicCarrierClause Variable)
  exact anchorNormalized_periodicizedEqualityClause_eq
    (normalizeCarrierNode
      (PeriodicCNF.incidenceGraph formula))
    firstSourceMember secondSourceMember linkEq
    (firstSourceEq.2.trans
      (indexEq.trans secondSourceEq.2.symm))

theorem anchorNormalized_periodicizedRoutedVariableClause_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {firstLink secondLink :
      EqualityLink (PlanarSATNode Variable)}
    {firstClause secondClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {firstIndex secondIndex : Nat}
    (firstMember :
      (firstClause, firstIndex) ∈
        (drawingPlanarSATRoutedVariableFormulaAt
          firstLink).zipIdx)
    (secondMember :
      (secondClause, secondIndex) ∈
        (drawingPlanarSATRoutedVariableFormulaAt
          secondLink).zipIdx)
    (linkEq :
      PeriodicEquality.normalizeLink
          (normalizePlanarSATNode
            (PeriodicCNF.incidenceGraph formula)) firstLink =
        PeriodicEquality.normalizeLink
          (normalizePlanarSATNode
            (PeriodicCNF.incidenceGraph formula)) secondLink)
    (indexEq : firstIndex = secondIndex) :
    (periodicizePlanarSATClause
        formula firstClause).anchorNormalize =
      (periodicizePlanarSATClause
        formula secondClause).anchorNormalize := by
  unfold drawingPlanarSATRoutedVariableFormulaAt at firstMember secondMember
  rw [List.zipIdx_map] at firstMember secondMember
  rcases List.mem_map.mp firstMember with
    ⟨firstSource, firstSourceMember, firstSourceEq⟩
  rcases List.mem_map.mp secondMember with
    ⟨secondSource, secondSourceMember, secondSourceEq⟩
  simp only [Prod.map, id_eq, Prod.mk.injEq] at firstSourceEq secondSourceEq
  rw [← firstSourceEq.1, ← secondSourceEq.1,
    periodicizePlanarSATClause_external_rename,
    periodicizePlanarSATClause_external_rename]
  exact anchorNormalized_periodicizedEqualityClause_eq
    (normalizePlanarSATNode
      (PeriodicCNF.incidenceGraph formula))
    firstSourceMember secondSourceMember linkEq
    (firstSourceEq.2.trans
      (indexEq.trans secondSourceEq.2.symm))

theorem anchorNormalized_periodicizedRoutedClause_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (firstSite secondSite : ClauseRouteSite)
    (siteEq : firstSite.1 = secondSite.1) :
    (periodicizePlanarSATClause formula
      ((routedClauseAt formula firstSite).rename
        planarSATExternalVariableMap)).anchorNormalize =
    (periodicizePlanarSATClause formula
      ((routedClauseAt formula secondSite).rename
        planarSATExternalVariableMap)).anchorNormalize := by
  rw [periodicizePlanarSATClause_external_rename,
    periodicizePlanarSATClause_external_rename,
    anchorNormalized_routedClauseAt,
    anchorNormalized_routedClauseAt,
    siteEq]

theorem crossoverClause_localOffset_mem
    {Variable : Type*}
    {crossing : CrossingRecord}
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {index : Nat}
    (member :
      (clause, index) ∈
        (drawingPlanarSATCrossoverFormulaAt
          (Variable := Variable) crossing).zipIdx)
    {offset : Cell}
    (positionEq :
      clause.position =
        Cell.add (crossingMacroOrigin crossing) offset) :
    offset ∈ crossoverClauseLocalPositions := by
  unfold drawingPlanarSATCrossoverFormulaAt
    scopedCrossoverInstance instantiateFormula at member
  rw [List.zipIdx_map, List.zipIdx_map] at member
  rcases List.mem_map.mp member with
    ⟨tagged, taggedMember, taggedEq⟩
  rcases List.mem_map.mp taggedMember with
    ⟨source, sourceMember, sourceEq⟩
  have outerPositionEq :=
    congrArg (fun tagged => tagged.1.position) taggedEq
  have innerPositionEq :=
    congrArg (fun tagged => tagged.1.position) sourceEq
  simp [EmbeddedClause.rename, EmbeddedClause.place,
    EmbeddedClause.map] at outerPositionEq innerPositionEq
  have offsetEq :
      offset = source.1.position := by
    rw [← outerPositionEq, ← innerPositionEq] at positionEq
    exact offset_eq_of_add_eq rfl
      (by simpa [Cell.scale] using positionEq.symm)
  rw [offsetEq, crossoverClauseLocalPositions]
  exact List.mem_map.mpr
    ⟨source.1, List.fst_mem_of_mem_zipIdx sourceMember, rfl⟩

def bendClauseLocalPositions : List Cell :=
  [(5, 5), (8, 8)]

theorem bendClause_localOffset_mem
    {Variable Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {bend : RouteBend}
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {index : Nat}
    (member :
      (clause, index) ∈
        (drawingPlanarSATBendFormulaAt
          (Variable := Variable) graph bend).zipIdx)
    {offset : Cell}
    (positionEq :
      clause.position =
        Cell.add
          (Cell.scale planarMacroScale
            (bend.drawingPoint graph))
          offset) :
    offset ∈ bendClauseLocalPositions := by
  have indexLt := List.snd_lt_of_mem_zipIdx member
  simp [drawingPlanarSATBendFormulaAt,
    drawingPlanarSATCarrierFormulaAt, equalityInstance] at indexLt
  rcases offset with ⟨offsetX, offsetY⟩
  interval_cases index <;>
    simp_all [drawingPlanarSATBendFormulaAt,
      drawingPlanarSATCarrierFormulaAt, equalityInstance,
      RouteBend.equalityLink, routeBendEqualityPositions,
      EmbeddedClause.rename, EmbeddedClause.map,
      bendClauseLocalPositions,
      Cell.add, Cell.scale, planarMacroScale] <;>
    omega

theorem crossover_bend_localPositions_disjoint :
    List.Disjoint crossoverClauseLocalPositions
      bendClauseLocalPositions := by
  simp [List.disjoint_left,
    crossoverClauseLocalPositions,
    bendClauseLocalPositions,
    crossoverFormula, crossoverClause]

theorem pointEq_translate_symm
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {first second : Cell} (shift : Cell)
    (equal :
      first =
        Cell.add second
          ((drawing graph).periodTranslation shift)) :
    second =
      Cell.add first
        ((drawing graph).periodTranslation (Cell.neg shift)) := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases shift with ⟨shiftX, shiftY⟩
  apply Prod.ext
  · have coordinateEq := congrArg Prod.fst equal
    simp [PeriodicGridDrawing.periodTranslation,
      Cell.add, Cell.scale, Cell.neg, Cell.sub] at coordinateEq ⊢
    omega
  · have coordinateEq := congrArg Prod.snd equal
    simp [PeriodicGridDrawing.periodTranslation,
      Cell.add, Cell.scale, Cell.neg, Cell.sub] at coordinateEq ⊢
    omega

theorem noncarrierClause_exists_localOffset
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (notCarrier :
      ¬∃ link, metadata.source.component = .carrier link)
    (center : Cell)
    (centerEq :
      metadata.source.component.macrocellCenter formula =
        some center) :
    ∃ offset,
      metadata.clause.position =
        Cell.add (Cell.scale planarMacroScale center) offset := by
  rcases metadata with ⟨clause, source⟩
  cases source with
  | crossover crossing localClauseIndex =>
      simp only [DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.macrocellCenter,
        Option.some.injEq] at centerEq
      subst center
      rcases crossoverClause_localPosition_strict valid.2 with
        ⟨offset, positionEq, _bounds⟩
      exact ⟨offset, by
        simpa [crossingMacroOrigin] using positionEq⟩
  | carrier link localClauseIndex =>
      exact False.elim (notCarrier ⟨link, rfl⟩)
  | bend bend localClauseIndex =>
      simp only [DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.macrocellCenter,
        Option.some.injEq] at centerEq
      subst center
      rcases bendClause_localPosition_strict
          (PeriodicCNF.incidenceGraph formula)
          bend valid.2 with
        ⟨offset, positionEq, _bounds⟩
      exact ⟨offset, positionEq⟩
  | routedClause site =>
      simp only [DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.macrocellCenter,
        Option.some.injEq] at centerEq
      subst center
      rcases routedClause_localPosition_strict
          formula site valid.2 with
        ⟨offset, positionEq, _bounds⟩
      exact ⟨offset, by
        simpa [routedClauseOrigin,
          liftedIncidenceVertexMacroOrigin] using positionEq⟩
  | routedVariable site armIndex arm link localClauseIndex =>
      simp only [DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.macrocellCenter,
        Option.some.injEq] at centerEq
      subst center
      have linkMem :
          link ∈ routedVariableLinksAt formula site :=
        List.fst_mem_of_mem_zipIdx valid.2.1
      have positionsEq :
          link.positions =
            ⟨Cell.add (routedVariableOrigin formula site)
                (duplicatorArmEqualityPositions arm).forward,
              Cell.add (routedVariableOrigin formula site)
                (duplicatorArmEqualityPositions arm).backward⟩ := by
        rw [routedVariableLink_positions formula site linkMem,
          valid.2.2.1]
        rfl
      rcases routedVariableClause_localPosition_strict
          (routedVariableOrigin formula site)
          arm link positionsEq valid.2.2.2 with
        ⟨offset, positionEq, _bounds⟩
      exact ⟨offset, by
        simpa [routedVariableOrigin,
          liftedIncidenceVertexMacroOrigin] using positionEq⟩

theorem add_periodTranslations
    (drawing : PeriodicGridDrawing)
    (base : Cell)
    (firstShift secondShift : Cell) :
    Cell.add
        (Cell.add base (drawing.periodTranslation firstShift))
        (drawing.periodTranslation secondShift) =
      Cell.add
        base
        (drawing.periodTranslation
          (Cell.add firstShift secondShift)) := by
  rcases base with ⟨positionX, positionY⟩
  rcases firstShift with ⟨firstX, firstY⟩
  rcases secondShift with ⟨secondX, secondY⟩
  apply Prod.ext <;>
    simp [PeriodicGridDrawing.periodTranslation,
      Cell.add, Cell.scale] <;>
    ring

theorem liftedIncidenceVertexPosition_add_periodTranslation
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (vertex : CNFVertex Variable)
    (firstShift secondShift : Cell) :
    Cell.add
        (liftedIncidenceVertexPosition formula vertex firstShift)
        ((drawing
          (PeriodicCNF.incidenceGraph formula)).periodTranslation
            secondShift) =
      Cell.add
        ((drawing
          (PeriodicCNF.incidenceGraph formula)).vertexPosition
            (PeriodicCNF.incidenceGraph formula) vertex)
        ((drawing
          (PeriodicCNF.incidenceGraph formula)).periodTranslation
            (Cell.add firstShift secondShift)) := by
  simpa [liftedIncidenceVertexPosition] using
    add_periodTranslations
      (drawing (PeriodicCNF.incidenceGraph formula))
      ((drawing
        (PeriodicCNF.incidenceGraph formula)).vertexPosition
          (PeriodicCNF.incidenceGraph formula) vertex)
      firstShift secondShift

set_option maxHeartbeats 1200000 in
theorem noncarrier_metadata_anchorNormalized_eq_of_residue_eq
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
    (firstNotCarrier :
      ¬∃ link, first.source.component = .carrier link)
    (secondNotCarrier :
      ¬∃ link, second.source.component = .carrier link)
    (firstNonempty : first.clause.literals ≠ [])
    (secondNonempty : second.clause.literals ≠ [])
    (residueEq :
      clauseResidue formula first.clause =
        clauseResidue formula second.clause) :
    (periodicizePlanarSATClause
        formula first.clause).anchorNormalize =
      (periodicizePlanarSATClause
        formula second.clause).anchorNormalize := by
  rcases
      first.source.component.exists_macrocellCenter_of_not_carrier
        formula firstNotCarrier with
    ⟨firstCenter, firstCenterEq⟩
  rcases
      second.source.component.exists_macrocellCenter_of_not_carrier
        formula secondNotCarrier with
    ⟨secondCenter, secondCenterEq⟩
  rcases clausePosition_eq_translate_of_residue_eq
      formula residueEq with
    ⟨shift, positionEq⟩
  rcases
      noncarrier_macrocellCenter_eq_translate_of_residue_eq
        wellFormed degree isLocal first second
        firstValid secondValid firstCenter secondCenter
        firstCenterEq secondCenterEq
        firstNonempty secondNonempty residueEq with
    ⟨centerShift, centerEq⟩
  have shiftEq : centerShift = shift := by
    have firstBounded :=
      first.retainedClausePosition_in_macrocell
        wellFormed degree isLocal firstValid
        firstCenter firstCenterEq firstNonempty
    have secondBounded :=
      second.retainedClausePosition_in_macrocell
        wellFormed degree isLocal secondValid
        secondCenter secondCenterEq secondNonempty
    have firstCenterFromPosition :
        firstCenter =
          Cell.add secondCenter
            (Cell.scale
              (drawingGridSize
                (PeriodicCNF.incidenceGraph formula))
              shift) := by
      have translatedSecondBounded :=
        inPlanarSATMacrocell_translate
          (drawingGridSize
            (PeriodicCNF.incidenceGraph formula))
          (shift := shift) secondBounded
      apply planarSATMacrocellCenter_eq_of_common_point firstBounded
      rw [positionEq]
      simpa [drawingPeriodicPlanarSATPlacement,
        planarMacroScale] using translatedSecondBounded
    have scaledEq :
        Cell.scale
            (drawingGridSize
              (PeriodicCNF.incidenceGraph formula) : Int)
            centerShift =
          Cell.scale
            (drawingGridSize
              (PeriodicCNF.incidenceGraph formula) : Int)
            shift := by
      exact offset_eq_of_add_eq
        centerEq firstCenterFromPosition
    have gridPositive :
        (0 : Int) <
          drawingGridSize
            (PeriodicCNF.incidenceGraph formula) := by
      exact_mod_cast drawingGridSize_pos
        (PeriodicCNF.incidenceGraph formula)
    rcases centerShift with ⟨centerShiftX, centerShiftY⟩
    rcases shift with ⟨shiftX, shiftY⟩
    apply Prod.ext
    · have coordinateEq := congrArg Prod.fst scaledEq
      simp [Cell.scale] at coordinateEq ⊢
      omega
    · have coordinateEq := congrArg Prod.snd scaledEq
      simp [Cell.scale] at coordinateEq ⊢
      omega
  subst centerShift
  rcases noncarrierClause_exists_localOffset
      first firstValid firstNotCarrier firstCenter firstCenterEq with
    ⟨firstOffset, firstPositionEq⟩
  rcases noncarrierClause_exists_localOffset
      second secondValid secondNotCarrier secondCenter secondCenterEq with
    ⟨secondOffset, secondPositionEq⟩
  have localOffsetEq :
      firstOffset = secondOffset := by
    apply localOffset_eq_of_position_eq_translate
      (drawingGridSize
        (PeriodicCNF.incidenceGraph formula) : Int)
      firstPositionEq secondPositionEq centerEq
    simpa [drawingPeriodicPlanarSATPlacement,
      planarMacroScale] using positionEq
  rcases first with ⟨firstClause, firstSource⟩
  rcases second with ⟨secondClause, secondSource⟩
  cases firstSource with
  | carrier link localClauseIndex =>
      exact False.elim (firstNotCarrier ⟨link, rfl⟩)
  | crossover firstCrossing firstIndex =>
      cases secondSource with
      | carrier link localClauseIndex =>
          exact False.elim (secondNotCarrier ⟨link, rfl⟩)
      | crossover secondCrossing secondIndex =>
          simp only [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter,
            Option.some.injEq] at firstCenterEq secondCenterEq
          rw [← firstCenterEq] at centerEq firstPositionEq
          rw [← secondCenterEq] at centerEq secondPositionEq
          have crossingEq :=
            periodNormalize_eq_of_point_eq_translate
              wellFormed degree isLocal
              firstValid.1 secondValid.1 shift
              (by
                simpa [PeriodicGridDrawing.periodTranslation,
                  drawing_gridSize] using centerEq)
          have indexEq :=
            (crossoverClause_localOffset_eq
              firstValid.2 secondValid.2
              (by simpa [crossingMacroOrigin] using firstPositionEq)
              (by simpa [crossingMacroOrigin] using secondPositionEq)).mp
                localOffsetEq
          exact anchorNormalized_periodicizedCrossoverClause_eq
            formula firstValid.2 secondValid.2 crossingEq indexEq
      | bend secondBend secondIndex =>
          simp only [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter,
            Option.some.injEq] at firstCenterEq secondCenterEq
          rw [← firstCenterEq] at centerEq firstPositionEq
          rw [← secondCenterEq] at centerEq secondPositionEq
          have firstOffsetMem :=
            crossoverClause_localOffset_mem
              firstValid.2
              (by simpa [crossingMacroOrigin] using firstPositionEq)
          have secondOffsetMem :=
            bendClause_localOffset_mem
              (PeriodicCNF.incidenceGraph formula)
              secondValid.2 secondPositionEq
          exact False.elim
            (crossover_bend_localPositions_disjoint
              firstOffsetMem
              (localOffsetEq ▸ secondOffsetMem))
      | routedClause secondSite =>
          simp only [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter,
            Option.some.injEq] at firstCenterEq secondCenterEq
          rw [← firstCenterEq] at centerEq firstPositionEq
          rw [← secondCenterEq] at centerEq secondPositionEq
          exact False.elim
            ((orientedCrossing_point_ne_liftedVertexPosition
              wellFormed degree firstValid.1
              (drawingClauseRouteSite_vertex_mem
                formula secondValid.1)
              (Cell.add secondSite.2 shift))
              (by
                calc
                  firstCrossing.point =
                      Cell.add
                        (liftedIncidenceVertexPosition formula
                          (.clause secondSite.1) secondSite.2)
                        ((drawing
                          (PeriodicCNF.incidenceGraph formula)).periodTranslation
                            shift) := by
                    simpa [PeriodicGridDrawing.periodTranslation,
                      drawing_gridSize] using centerEq
                  _ = _ :=
                    liftedIncidenceVertexPosition_add_periodTranslation
                      formula (.clause secondSite.1) secondSite.2 shift))
      | routedVariable secondSite secondArmIndex secondArm
          secondLink secondIndex =>
          simp only [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter,
            Option.some.injEq] at firstCenterEq secondCenterEq
          rw [← firstCenterEq] at centerEq firstPositionEq
          rw [← secondCenterEq] at centerEq secondPositionEq
          exact False.elim
            ((orientedCrossing_point_ne_liftedVertexPosition
              wellFormed degree firstValid.1
              (drawingVariableRouteSite_vertex_mem
                formula secondValid.1)
              (Cell.add secondSite.2 shift))
              (by
                calc
                  firstCrossing.point =
                      Cell.add
                        (liftedIncidenceVertexPosition formula
                          (.variable secondSite.1) secondSite.2)
                        ((drawing
                          (PeriodicCNF.incidenceGraph formula)).periodTranslation
                            shift) := by
                    simpa [PeriodicGridDrawing.periodTranslation,
                      drawing_gridSize] using centerEq
                  _ = _ :=
                    liftedIncidenceVertexPosition_add_periodTranslation
                      formula (.variable secondSite.1) secondSite.2 shift))
  | bend firstBend firstIndex =>
      cases secondSource with
      | carrier link localClauseIndex =>
          exact False.elim (secondNotCarrier ⟨link, rfl⟩)
      | crossover secondCrossing secondIndex =>
          simp only [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter,
            Option.some.injEq] at firstCenterEq secondCenterEq
          rw [← firstCenterEq] at centerEq firstPositionEq
          rw [← secondCenterEq] at centerEq secondPositionEq
          have firstOffsetMem :=
            bendClause_localOffset_mem
              (PeriodicCNF.incidenceGraph formula)
              firstValid.2 firstPositionEq
          have secondOffsetMem :=
            crossoverClause_localOffset_mem
              secondValid.2
              (by simpa [crossingMacroOrigin] using secondPositionEq)
          exact False.elim
            (crossover_bend_localPositions_disjoint
              secondOffsetMem
              (localOffsetEq.symm ▸ firstOffsetMem))
      | bend secondBend secondIndex =>
          simp only [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter,
            Option.some.injEq] at firstCenterEq secondCenterEq
          rw [← firstCenterEq] at centerEq firstPositionEq
          rw [← secondCenterEq] at centerEq secondPositionEq
          have linkEq :=
            normalizedDrawingRouteBendLink_eq_of_drawingPoint_eq_translate
              (PeriodicCNF.incidenceGraph formula)
              wellFormed degree isLocal
              (List.mem_dedup.mp firstValid.1)
              (List.mem_dedup.mp secondValid.1)
              shift
              (by
                simpa [PeriodicGridDrawing.periodTranslation,
                  drawing_gridSize] using centerEq)
          have indexEq :=
            (bendClause_localOffset_eq
              (PeriodicCNF.incidenceGraph formula)
              firstValid.2 secondValid.2
              firstPositionEq secondPositionEq).mp
                localOffsetEq
          exact anchorNormalized_periodicizedCarrierClause_eq
            formula
            (by simpa [drawingPlanarSATBendFormulaAt] using firstValid.2)
            (by simpa [drawingPlanarSATBendFormulaAt] using secondValid.2)
            linkEq indexEq
      | routedClause secondSite =>
          simp only [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter,
            Option.some.injEq] at firstCenterEq secondCenterEq
          rw [← firstCenterEq] at centerEq firstPositionEq
          rw [← secondCenterEq] at centerEq secondPositionEq
          exact False.elim
            ((drawingRouteBend_drawingPoint_ne_liftedVertexPosition
              wellFormed degree isLocal
              (drawingClauseRouteSite_vertex_mem
                formula secondValid.1)
              (Cell.add secondSite.2 shift)
              (List.mem_dedup.mp firstValid.1))
              (by
                calc
                  firstBend.drawingPoint
                      (PeriodicCNF.incidenceGraph formula) =
                      Cell.add
                        (liftedIncidenceVertexPosition formula
                          (.clause secondSite.1) secondSite.2)
                        ((drawing
                          (PeriodicCNF.incidenceGraph formula)).periodTranslation
                            shift) := by
                    simpa [PeriodicGridDrawing.periodTranslation,
                      drawing_gridSize] using centerEq
                  _ = _ :=
                    liftedIncidenceVertexPosition_add_periodTranslation
                      formula (.clause secondSite.1) secondSite.2 shift))
      | routedVariable secondSite secondArmIndex secondArm
          secondLink secondIndex =>
          simp only [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter,
            Option.some.injEq] at firstCenterEq secondCenterEq
          rw [← firstCenterEq] at centerEq firstPositionEq
          rw [← secondCenterEq] at centerEq secondPositionEq
          exact False.elim
            ((drawingRouteBend_drawingPoint_ne_liftedVertexPosition
              wellFormed degree isLocal
              (drawingVariableRouteSite_vertex_mem
                formula secondValid.1)
              (Cell.add secondSite.2 shift)
              (List.mem_dedup.mp firstValid.1))
              (by
                calc
                  firstBend.drawingPoint
                      (PeriodicCNF.incidenceGraph formula) =
                      Cell.add
                        (liftedIncidenceVertexPosition formula
                          (.variable secondSite.1) secondSite.2)
                        ((drawing
                          (PeriodicCNF.incidenceGraph formula)).periodTranslation
                            shift) := by
                    simpa [PeriodicGridDrawing.periodTranslation,
                      drawing_gridSize] using centerEq
                  _ = _ :=
                    liftedIncidenceVertexPosition_add_periodTranslation
                      formula (.variable secondSite.1) secondSite.2 shift))
  | routedClause firstSite =>
      cases secondSource with
      | carrier link localClauseIndex =>
          exact False.elim (secondNotCarrier ⟨link, rfl⟩)
      | crossover secondCrossing secondIndex =>
          simp only [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter,
            Option.some.injEq] at firstCenterEq secondCenterEq
          rw [← firstCenterEq] at centerEq firstPositionEq
          rw [← secondCenterEq] at centerEq secondPositionEq
          have reverseEq :=
            pointEq_translate_symm
              (PeriodicCNF.incidenceGraph formula)
              shift
              (by
                simpa [PeriodicGridDrawing.periodTranslation,
                  drawing_gridSize] using centerEq)
          exact False.elim
            ((orientedCrossing_point_ne_liftedVertexPosition
              wellFormed degree secondValid.1
              (drawingClauseRouteSite_vertex_mem
                formula firstValid.1)
              (Cell.add firstSite.2 (Cell.neg shift)))
              (by
                calc
                  secondCrossing.point =
                      Cell.add
                        (liftedIncidenceVertexPosition formula
                          (.clause firstSite.1) firstSite.2)
                        ((drawing
                          (PeriodicCNF.incidenceGraph formula)).periodTranslation
                            (Cell.neg shift)) := by
                    simpa [PeriodicGridDrawing.periodTranslation,
                      drawing_gridSize] using reverseEq
                  _ = _ :=
                    liftedIncidenceVertexPosition_add_periodTranslation
                      formula (.clause firstSite.1) firstSite.2
                        (Cell.neg shift)))
      | bend secondBend secondIndex =>
          simp only [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter,
            Option.some.injEq] at firstCenterEq secondCenterEq
          rw [← firstCenterEq] at centerEq firstPositionEq
          rw [← secondCenterEq] at centerEq secondPositionEq
          have reverseEq :=
            pointEq_translate_symm
              (PeriodicCNF.incidenceGraph formula)
              shift
              (by
                simpa [PeriodicGridDrawing.periodTranslation,
                  drawing_gridSize] using centerEq)
          exact False.elim
            ((drawingRouteBend_drawingPoint_ne_liftedVertexPosition
              wellFormed degree isLocal
              (drawingClauseRouteSite_vertex_mem
                formula firstValid.1)
              (Cell.add firstSite.2 (Cell.neg shift))
              (List.mem_dedup.mp secondValid.1))
              (by
                calc
                  secondBend.drawingPoint
                      (PeriodicCNF.incidenceGraph formula) =
                      Cell.add
                        (liftedIncidenceVertexPosition formula
                          (.clause firstSite.1) firstSite.2)
                        ((drawing
                          (PeriodicCNF.incidenceGraph formula)).periodTranslation
                            (Cell.neg shift)) := by
                    simpa [PeriodicGridDrawing.periodTranslation,
                      drawing_gridSize] using reverseEq
                  _ = _ :=
                    liftedIncidenceVertexPosition_add_periodTranslation
                      formula (.clause firstSite.1) firstSite.2
                        (Cell.neg shift)))
      | routedClause secondSite =>
          simp only [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter,
            Option.some.injEq] at firstCenterEq secondCenterEq
          rw [← firstCenterEq] at centerEq firstPositionEq
          rw [← secondCenterEq] at centerEq secondPositionEq
          have vertexEq :=
            liftedIncidenceVertex_eq_of_position_eq_translate
              formula
              (drawingClauseRouteSite_vertex_mem
                formula firstValid.1)
              (drawingClauseRouteSite_vertex_mem
                formula secondValid.1)
              firstSite.2 secondSite.2 shift
              (by
                simpa [PeriodicGridDrawing.periodTranslation,
                  drawing_gridSize] using centerEq)
          have siteEq : firstSite.1 = secondSite.1 :=
            CNFVertex.clause.inj vertexEq
          rw [firstValid.2, secondValid.2]
          exact
            anchorNormalized_periodicizedRoutedClause_eq
              formula firstSite secondSite siteEq
      | routedVariable secondSite secondArmIndex secondArm
          secondLink secondIndex =>
          simp only [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter,
            Option.some.injEq] at firstCenterEq secondCenterEq
          rw [← firstCenterEq] at centerEq firstPositionEq
          rw [← secondCenterEq] at centerEq secondPositionEq
          have vertexEq :=
            liftedIncidenceVertex_eq_of_position_eq_translate
              formula
              (drawingClauseRouteSite_vertex_mem
                formula firstValid.1)
              (drawingVariableRouteSite_vertex_mem
                formula secondValid.1)
              firstSite.2 secondSite.2 shift
              (by
                simpa [PeriodicGridDrawing.periodTranslation,
                  drawing_gridSize] using centerEq)
          cases vertexEq
  | routedVariable firstSite firstArmIndex firstArm
      firstLink firstIndex =>
      cases secondSource with
      | carrier link localClauseIndex =>
          exact False.elim (secondNotCarrier ⟨link, rfl⟩)
      | crossover secondCrossing secondIndex =>
          simp only [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter,
            Option.some.injEq] at firstCenterEq secondCenterEq
          rw [← firstCenterEq] at centerEq firstPositionEq
          rw [← secondCenterEq] at centerEq secondPositionEq
          have reverseEq :=
            pointEq_translate_symm
              (PeriodicCNF.incidenceGraph formula)
              shift
              (by
                simpa [PeriodicGridDrawing.periodTranslation,
                  drawing_gridSize] using centerEq)
          exact False.elim
            ((orientedCrossing_point_ne_liftedVertexPosition
              wellFormed degree secondValid.1
              (drawingVariableRouteSite_vertex_mem
                formula firstValid.1)
              (Cell.add firstSite.2 (Cell.neg shift)))
              (by
                calc
                  secondCrossing.point =
                      Cell.add
                        (liftedIncidenceVertexPosition formula
                          (.variable firstSite.1) firstSite.2)
                        ((drawing
                          (PeriodicCNF.incidenceGraph formula)).periodTranslation
                            (Cell.neg shift)) := by
                    simpa [PeriodicGridDrawing.periodTranslation,
                      drawing_gridSize] using reverseEq
                  _ = _ :=
                    liftedIncidenceVertexPosition_add_periodTranslation
                      formula (.variable firstSite.1) firstSite.2
                        (Cell.neg shift)))
      | bend secondBend secondIndex =>
          simp only [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter,
            Option.some.injEq] at firstCenterEq secondCenterEq
          rw [← firstCenterEq] at centerEq firstPositionEq
          rw [← secondCenterEq] at centerEq secondPositionEq
          have reverseEq :=
            pointEq_translate_symm
              (PeriodicCNF.incidenceGraph formula)
              shift
              (by
                simpa [PeriodicGridDrawing.periodTranslation,
                  drawing_gridSize] using centerEq)
          exact False.elim
            ((drawingRouteBend_drawingPoint_ne_liftedVertexPosition
              wellFormed degree isLocal
              (drawingVariableRouteSite_vertex_mem
                formula firstValid.1)
              (Cell.add firstSite.2 (Cell.neg shift))
              (List.mem_dedup.mp secondValid.1))
              (by
                calc
                  secondBend.drawingPoint
                      (PeriodicCNF.incidenceGraph formula) =
                      Cell.add
                        (liftedIncidenceVertexPosition formula
                          (.variable firstSite.1) firstSite.2)
                        ((drawing
                          (PeriodicCNF.incidenceGraph formula)).periodTranslation
                            (Cell.neg shift)) := by
                    simpa [PeriodicGridDrawing.periodTranslation,
                      drawing_gridSize] using reverseEq
                  _ = _ :=
                    liftedIncidenceVertexPosition_add_periodTranslation
                      formula (.variable firstSite.1) firstSite.2
                        (Cell.neg shift)))
      | routedClause secondSite =>
          simp only [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter,
            Option.some.injEq] at firstCenterEq secondCenterEq
          rw [← firstCenterEq] at centerEq firstPositionEq
          rw [← secondCenterEq] at centerEq secondPositionEq
          have vertexEq :=
            liftedIncidenceVertex_eq_of_position_eq_translate
              formula
              (drawingVariableRouteSite_vertex_mem
                formula firstValid.1)
              (drawingClauseRouteSite_vertex_mem
                formula secondValid.1)
              firstSite.2 secondSite.2 shift
              (by
                simpa [PeriodicGridDrawing.periodTranslation,
                  drawing_gridSize] using centerEq)
          cases vertexEq
      | routedVariable secondSite secondArmIndex secondArm
          secondLink secondIndex =>
          simp only [DrawingPlanarSATClauseSource.component,
            DrawingPlanarSATComponent.macrocellCenter,
            Option.some.injEq] at firstCenterEq secondCenterEq
          rw [← firstCenterEq] at centerEq firstPositionEq
          rw [← secondCenterEq] at centerEq secondPositionEq
          have vertexEq :=
            liftedIncidenceVertex_eq_of_position_eq_translate
              formula
              (drawingVariableRouteSite_vertex_mem
                formula firstValid.1)
              (drawingVariableRouteSite_vertex_mem
                formula secondValid.1)
              firstSite.2 secondSite.2 shift
              (by
                simpa [PeriodicGridDrawing.periodTranslation,
                  drawing_gridSize] using centerEq)
          have atomEq : firstSite.1 = secondSite.1 :=
            CNFVertex.variable.inj vertexEq
          have firstLinkMem :
              firstLink ∈ routedVariableLinksAt formula firstSite :=
            List.fst_mem_of_mem_zipIdx firstValid.2.1
          have secondLinkMem :
              secondLink ∈ routedVariableLinksAt formula secondSite :=
            List.fst_mem_of_mem_zipIdx secondValid.2.1
          have firstPositionsEq :
              firstLink.positions =
                ⟨Cell.add (routedVariableOrigin formula firstSite)
                    (duplicatorArmEqualityPositions firstArm).forward,
                  Cell.add (routedVariableOrigin formula firstSite)
                    (duplicatorArmEqualityPositions firstArm).backward⟩ := by
            rw [routedVariableLink_positions
              formula firstSite firstLinkMem,
              firstValid.2.2.1]
            rfl
          have secondPositionsEq :
              secondLink.positions =
                ⟨Cell.add (routedVariableOrigin formula secondSite)
                    (duplicatorArmEqualityPositions secondArm).forward,
                  Cell.add (routedVariableOrigin formula secondSite)
                    (duplicatorArmEqualityPositions secondArm).backward⟩ := by
            rw [routedVariableLink_positions
              formula secondSite secondLinkMem,
              secondValid.2.2.1]
            rfl
          have armIndexEq :=
            (routedVariableClause_localOffset_eq
              firstPositionsEq secondPositionsEq
              firstValid.2.2.2 secondValid.2.2.2
              (by simpa [routedVariableOrigin,
                liftedIncidenceVertexMacroOrigin] using firstPositionEq)
              (by simpa [routedVariableOrigin,
                liftedIncidenceVertexMacroOrigin] using secondPositionEq)).mp
                  localOffsetEq
          have linkEq :=
            normalizedRoutedVariableLink_eq_of_atom_eq_of_arm_eq
              formula wellFormed degree firstSite secondSite
              firstLinkMem secondLinkMem atomEq
              (firstValid.2.2.1.symm.trans
                (armIndexEq.1.trans secondValid.2.2.1))
          exact
            anchorNormalized_periodicizedRoutedVariableClause_eq
              formula firstValid.2.2.2 secondValid.2.2.2
              linkEq armIndexEq.2

theorem noncarrier_metadataGaugedNormalizedClause_eq_of_residue_eq
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
    (firstNotCarrier :
      ¬∃ link, first.source.component = .carrier link)
    (secondNotCarrier :
      ¬∃ link, second.source.component = .carrier link)
    (firstNonempty : first.clause.literals ≠ [])
    (secondNonempty : second.clause.literals ≠ [])
    (residueEq :
      clauseResidue formula first.clause =
        clauseResidue formula second.clause) :
    metadataGaugedNormalizedClause formula first =
      metadataGaugedNormalizedClause formula second := by
  unfold metadataGaugedNormalizedClause
  apply variableGauge_anchorNormalize_eq_of_anchorNormalize_eq
  rw [← wrapPeriodicPlanarSATClause_anchorNormalize,
    ← wrapPeriodicPlanarSATClause_anchorNormalize]
  exact congrArg wrapPeriodicPlanarSATClause
    (noncarrier_metadata_anchorNormalized_eq_of_residue_eq
      wellFormed degree isLocal first second
      firstValid secondValid firstNotCarrier secondNotCarrier
      firstNonempty secondNonempty residueEq)

end LeanTrominoes.PeriodicOrthocrossing
