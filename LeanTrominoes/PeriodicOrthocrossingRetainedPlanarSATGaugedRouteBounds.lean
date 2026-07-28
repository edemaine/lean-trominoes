import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierRouteBounds

/-!
# Route bounds for the final gauged retained planar-SAT drawing

The local carrier and non-carrier coordinate bounds are combined into one
metadata-level statement.  This module then follows each route through
clause-anchor normalization and first-representative clause deduplication.
Every point of every route in the final gauged periodic incidence drawing
lies in the open neighboring-period square `(-P, 2P)²`.
-/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- Every retained metadata-selected route point satisfies the expanded
square bound after clause-anchor normalization. -/
theorem metadata_normalizedRoutePoint_inExpanded
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (nonempty : metadata.clause.literals ≠ [])
    {literal : PlanarSATVariable Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ metadata.clause.literals.zipIdx)
    {point : Cell}
    (pointMember :
      point ∈
        (metadata.source.incidenceDrawing formula).routes
          metadata.source.localClauseIndex literalIndex) :
    let normalized :=
      Cell.sub point
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).translation
          (PeriodicCNF.clauseAnchor
            ((wrapPeriodicPlanarSATClause
              (periodicizePlanarSATClause formula
                metadata.clause)).variableGauge
                  (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
                    formula))))
    let period : Int :=
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).period
    (-period < normalized.1) ∧ normalized.1 < 2 * period ∧
      -period < normalized.2 ∧ normalized.2 < 2 * period := by
  by_cases carrier :
      ∃ link, metadata.source.component = .carrier link
  · rcases carrier with ⟨link, componentEq⟩
    exact metadata_normalizedRoutePoint_inExpanded_of_carrier
      wellFormed degree isLocal metadata valid link componentEq
      nonempty literalMember pointMember
  · rcases
        metadata.source.component.exists_macrocellCenter_of_not_carrier
          formula carrier with
      ⟨center, centerEq⟩
    have fundamental :=
      metadata_normalizedRoutePoint_inFundamental_of_noncarrier
        wellFormed degree isLocal metadata valid center centerEq
        nonempty literalMember pointMember
    dsimp only at fundamental ⊢
    have periodPositive :
        (0 : Int) <
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula).period := by
      exact_mod_cast
        drawingPeriodicPlanarSATPlacement_period_pos formula
    omega

/-- Before anchor normalization, the gauged positioned clauses remain in
exact retained-metadata order. -/
theorem gauged_clauses_eq_metadata
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).clauses =
      (retainedDrawingPlanarSATClauseMetadata formula).map
        (fun metadata =>
          (⟨metadata.clause.position,
            (wrapPeriodicPlanarSATClause
              (periodicizePlanarSATClause formula
                metadata.clause)).variableGauge
                  (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
                    formula)⟩ :
            PositionedPeriodicClause
              (WrappedPeriodicPlanarSATVariable Variable))) := by
  unfold
    retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
    retainedWrappedDrawingPositionedPeriodicPlanarSATFormula
    retainedDrawingPositionedPeriodicPlanarSATFormula
    positionPeriodicizedPlanarSATFormula
    PositionedPeriodicCNF.variableGauge
    PositionedPeriodicCNF.rename
  rw [← retainedDrawingPlanarSATClauseMetadata_clauses]
  simp only [List.map_map]
  apply List.map_congr_left
  intro metadata metadataMember
  rfl

/-- The route at a retained metadata index inherits its local expanded-square
bound through the first anchor-normalization pass. -/
theorem metadata_anchorNormalizedRoutePoint_inExpanded
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    {clauseIndex : Nat}
    (metadataLookup :
      (retainedDrawingPlanarSATClauseMetadata
        formula)[clauseIndex]? = some metadata)
    (valid : metadata.RetainedValid formula)
    (nonempty : metadata.clause.literals ≠ [])
    {literal : PlanarSATVariable Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ metadata.clause.literals.zipIdx)
    {point : Cell}
    (pointMember :
      point ∈
        PositionedPeriodicCNF.anchorNormalizedIncidenceRoutes
          (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula)
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
          (retainedDrawingPlanarSATLocalIncidenceRoutes formula)
          clauseIndex literalIndex) :
    let period : Int :=
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).period
    (-period < point.1) ∧ point.1 < 2 * period ∧
      -period < point.2 ∧ point.2 < 2 * period := by
  let positionedClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable) :=
    ⟨metadata.clause.position,
      (wrapPeriodicPlanarSATClause
        (periodicizePlanarSATClause formula
          metadata.clause)).variableGauge
            (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
              formula)⟩
  have clauseLookup :
      (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).clauses[clauseIndex]? =
          some positionedClause := by
    rw [gauged_clauses_eq_metadata formula,
      List.getElem?_map, metadataLookup]
    rfl
  simp only [PositionedPeriodicCNF.anchorNormalizedIncidenceRoutes,
    clauseLookup] at pointMember
  unfold PositionedPeriodicCNF.normalizeIncidenceRoute at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨rawPoint, rawPointMember, pointEq⟩
  subst point
  have localPointMember :
      rawPoint ∈
        (metadata.source.incidenceDrawing formula).routes
          metadata.source.localClauseIndex literalIndex := by
    simpa [retainedDrawingPlanarSATLocalIncidenceRoutes,
      metadataLookup] using rawPointMember
  have bounded :=
    metadata_normalizedRoutePoint_inExpanded
      wellFormed degree isLocal metadata valid nonempty
      literalMember localPointMember
  simpa [positionedClause] using bounded

/-- Deduplication reuses the representative source route literally when the
retained clause already has anchor zero. -/
theorem mem_sourceRoute_of_mem_deduplicatedIncidenceRoute_of_anchor_zero
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex literalIndex : Nat}
    (clauseLookup :
      source.deduplicateByLiterals.clauses[clauseIndex]? =
        some clause)
    (anchorZero :
      PeriodicCNF.clauseAnchor clause.literals = (0, 0))
    {point : Cell}
    (pointMember :
      point ∈
        source.deduplicatedIncidenceRoutes
          placement routes clauseIndex literalIndex) :
    point ∈
      routes
        (source.representativeClauseIndex clause.literals)
        literalIndex := by
  simpa [PositionedPeriodicCNF.deduplicatedIncidenceRoutes,
    clauseLookup,
    PositionedPeriodicCNF.normalizeIncidenceRoute,
    anchorZero,
    PeriodicVariablePlacement.translation,
    Cell.sub, Cell.scale] using pointMember

/-- A positioned clause retained by literal-list deduplication has an
original positioned representative at the declared representative index. -/
theorem exists_representativeClause_of_mem_deduplicateByLiterals
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (clause : PositionedPeriodicClause Variable)
    (clauseMember :
      clause ∈ source.deduplicateByLiterals.clauses) :
    ∃ sourceClause : PositionedPeriodicClause Variable,
      source.clauses[
          source.representativeClauseIndex clause.literals]? =
        some sourceClause ∧
      sourceClause.literals = clause.literals := by
  have retainedLiteralsMem :
      clause.literals ∈ source.erase.clauses := by
    have deduplicatedMember :
        clause.literals ∈
          source.deduplicateByLiterals.erase.clauses := by
      exact List.mem_map.mpr ⟨clause, clauseMember, rfl⟩
    exact
      (PositionedPeriodicCNF.clause_mem_erase_deduplicateByLiterals_iff
        source clause.literals).mp deduplicatedMember
  rcases
      PositionedPeriodicCNF.exists_representativeClause
        source clause.literals retainedLiteralsMem with
    ⟨sourceClause, sourceClauseLookup,
      sourceClauseLiterals, sourceClausePosition⟩
  exact ⟨sourceClause, sourceClauseLookup, sourceClauseLiterals⟩

/-- Every flat incidence route recovers its positioned clause and literal
coordinates. -/
theorem exists_incidenceRoute_coordinates
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    {route : List Cell}
    (routeMember :
      route ∈
        (PositionedPeriodicCNF.incidenceDrawing
          source placement routes).edgeRoutes) :
    ∃ taggedClause ∈ source.clauses.zipIdx,
      ∃ taggedLiteral ∈ taggedClause.1.literals.zipIdx,
        route = routes taggedClause.2 taggedLiteral.2 := by
  change route ∈
    PositionedPeriodicCNF.incidenceEdgeRoutes source routes at routeMember
  unfold PositionedPeriodicCNF.incidenceEdgeRoutes at routeMember
  rcases List.mem_flatMap.mp routeMember with
    ⟨taggedClause, taggedClauseMember, routeMember⟩
  rcases List.mem_map.mp routeMember with
    ⟨taggedLiteral, taggedLiteralMember, routeEq⟩
  exact
    ⟨taggedClause, taggedClauseMember,
      taggedLiteral, taggedLiteralMember, routeEq.symm⟩

/-- Every point of one genuine final incidence route lies in the expanded
square. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutePoint_inExpandedSquare
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
        clause.literals ≠ [])
    (taggedClause :
      PositionedPeriodicClause
          (WrappedPeriodicPlanarSATVariable Variable) × Nat)
    (taggedClauseMember :
      taggedClause ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses.zipIdx)
    (taggedLiteral :
      PeriodicLiteral
          (WrappedPeriodicPlanarSATVariable Variable) × Nat)
    (taggedLiteralMember :
      taggedLiteral ∈ taggedClause.1.literals.zipIdx)
    {point : Cell}
    (pointMember :
      point ∈
        retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula taggedClause.2 taggedLiteral.2) :
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula).PositionInExpandedSquare point := by
  let retainedClause := taggedClause.1
  let clauseIndex := taggedClause.2
  let literalIndex := taggedLiteral.2
  have retainedClauseMember :
      retainedClause ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses :=
    List.fst_mem_of_mem_zipIdx taggedClauseMember
  have retainedClauseLookup :
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).clauses[clauseIndex]? =
          some retainedClause := by
    exact
      (List.mem_zipIdx_iff_getElem?).mp taggedClauseMember
  let source :=
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula
  have retainedClauseMember' :
      retainedClause ∈ source.deduplicateByLiterals.clauses := by
    simpa only [source,
      retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula]
      using retainedClauseMember
  rcases
      exists_representativeClause_of_mem_deduplicateByLiterals
        source retainedClause retainedClauseMember' with
    ⟨sourceClause, sourceClauseLookup,
      sourceClauseLiterals⟩
  have sourceClausesEq :
      source.clauses =
        (retainedDrawingPlanarSATClauseMetadata formula).map
          (fun metadata =>
            (⟨clauseResidue formula metadata.clause,
              metadataGaugedNormalizedClause formula metadata⟩ :
              PositionedPeriodicClause
                (WrappedPeriodicPlanarSATVariable Variable))) := by
    simpa [source] using
      anchorNormalized_clauses_eq_metadata
        formula wellFormed degree isLocal clausesNonempty
  rw [sourceClausesEq, List.getElem?_map] at sourceClauseLookup
  rcases Option.map_eq_some_iff.mp sourceClauseLookup with
    ⟨metadata, metadataLookup, sourceClauseEq⟩
  have metadataIndexLt :
      source.representativeClauseIndex retainedClause.literals <
        (retainedDrawingPlanarSATClauseMetadata formula).length :=
    (List.getElem?_eq_some_iff.mp metadataLookup).1
  have metadataMember :
      metadata ∈ retainedDrawingPlanarSATClauseMetadata formula := by
    have metadataAt :
        (retainedDrawingPlanarSATClauseMetadata formula)[
            source.representativeClauseIndex
              retainedClause.literals] = metadata :=
      (List.getElem?_eq_some_iff.mp metadataLookup).2
    rw [← metadataAt]
    exact List.getElem_mem metadataIndexLt
  have valid : metadata.RetainedValid formula :=
    retainedDrawingPlanarSATClauseMetadata_valid formula metadataMember
  have metadataClauseMember :
      metadata.clause ∈ retainedDrawingPlanarSATFormula formula := by
    rw [← retainedDrawingPlanarSATClauseMetadata_clauses]
    exact List.mem_map.mpr ⟨metadata, metadataMember, rfl⟩
  have nonempty : metadata.clause.literals ≠ [] :=
    clausesNonempty metadata.clause metadataClauseMember
  have literalIndexLt :
      literalIndex < metadata.clause.literals.length := by
    have retainedLiteralIndexLt :=
      List.snd_lt_of_mem_zipIdx taggedLiteralMember
    change
      taggedLiteral.2 < metadata.clause.literals.length
    change taggedLiteral.2 < retainedClause.literals.length at retainedLiteralIndexLt
    rw [← sourceClauseLiterals,
      ← sourceClauseEq] at retainedLiteralIndexLt
    simpa [metadataGaugedNormalizedClause,
      wrapPeriodicPlanarSATClause,
      periodicizePlanarSATClause] using retainedLiteralIndexLt
  let literal := metadata.clause.literals[literalIndex]
  have literalMember :
      (literal, literalIndex) ∈
        metadata.clause.literals.zipIdx := by
    exact (List.mem_zipIdx_iff_getElem?).mpr
      (by simp [literal, literalIndexLt])
  have anchorZero :
      PeriodicCNF.clauseAnchor retainedClause.literals = (0, 0) := by
    apply clauseAnchor_eq_zero_of_mem_deduplicate_anchorNormalize
      (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
      retainedClause
    simpa only [
      retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula,
      retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula]
      using retainedClauseMember
  have innerPointMember :
      point ∈
        PositionedPeriodicCNF.anchorNormalizedIncidenceRoutes
          (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula)
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
          (retainedDrawingPlanarSATLocalIncidenceRoutes formula)
          (source.representativeClauseIndex retainedClause.literals)
          literalIndex := by
    apply
      mem_sourceRoute_of_mem_deduplicatedIncidenceRoute_of_anchor_zero
        source
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
        (PositionedPeriodicCNF.anchorNormalizedIncidenceRoutes
          (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula)
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
          (retainedDrawingPlanarSATLocalIncidenceRoutes formula))
        retainedClauseLookup anchorZero
    simpa [source,
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes,
      retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula]
      using pointMember
  have bounded :=
    metadata_anchorNormalizedRoutePoint_inExpanded
      wellFormed degree isLocal metadata metadataLookup valid nonempty
      literalMember innerPointMember
  unfold PeriodicGridDrawing.PositionInExpandedSquare
  rw [
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing]
  rw [PositionedPeriodicCNF.incidenceDrawing_gridSize
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula)
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      formula)
    (by
      simpa [retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
        wrappedDrawingPeriodicPlanarSATPlacement] using
        drawingPeriodicPlanarSATPlacement_period_pos formula)]
  exact bounded

/-- The complete final gauged, anchor-normalized, deduplicated incidence
drawing satisfies the pointwise route bound required by expanded finite
periodic planarity. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_routePointsInExpandedSquare
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
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula).RoutePointsInExpandedSquare := by
  intro route routeMember point pointMember
  rcases exists_incidenceRoute_coordinates
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula)
      (by
        simpa only [
          retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing]
          using routeMember) with
    ⟨taggedClause, taggedClauseMember,
      taggedLiteral, taggedLiteralMember, routeEq⟩
  subst route
  exact
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutePoint_inExpandedSquare
    formula wellFormed degree isLocal clausesNonempty
    taggedClause taggedClauseMember taggedLiteral taggedLiteralMember
    pointMember

end LeanTrominoes.PeriodicOrthocrossing
