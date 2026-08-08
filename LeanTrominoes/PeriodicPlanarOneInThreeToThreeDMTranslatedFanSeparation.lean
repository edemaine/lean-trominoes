import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMTranslatedFanCorridorSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableClauseSeparation

/-!
# Separation of periodically translated endpoint fans

The finite fan classifiers depend only on the relative positions and endpoint
directions of their two macrocells.  Lifted continuous source planarity rules
out the classifiers' sole facing cases at arbitrary relative period shifts.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Translating both a ribbon center and a bounded physical point preserves
macrocell containment. -/
theorem InRibbonMacrocell.add_center
    {center point : Cell} (bounded : InRibbonMacrocell center point)
    (offset : Cell) :
    InRibbonMacrocell (Cell.add offset center)
      (Cell.add (ribbonMacrocellOrigin offset) point) := by
  rcases center with ⟨centerX, centerY⟩
  rcases point with ⟨pointX, pointY⟩
  rcases offset with ⟨offsetX, offsetY⟩
  simp only [InRibbonMacrocell, ribbonMacrocellOrigin,
    standardThreeStrandLayout, Cell.add, Cell.scale] at bounded ⊢
  omega

/-- A translated coordinated variable fan remains in the correspondingly
translated source macrocell. -/
theorem translatedOccurrenceCoordinatedRibbonVariableStub_points_bounded
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible presentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) (translate : Cell) {point : Cell}
    (member : point ∈
      translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (occurrenceCoordinatedRibbonVariableStub
          presentation entry color)) :
    InRibbonMacrocell
      (Cell.add (placement.translation translate)
        (placement.position entry.1.1)) point := by
  unfold translatePolyline at member
  rcases List.mem_map.mp member with
    ⟨sourcePoint, sourceMember, rfl⟩
  exact
    (occurrenceCoordinatedRibbonVariableStub_points_bounded
      presentation compatible entry color sourceMember).add_center
        (placement.translation translate)

/-- A translated coordinated clause fan remains in the correspondingly
translated lifted clause macrocell. -/
theorem translatedOccurrenceCoordinatedRibbonClauseStub_points_bounded
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible presentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) (translate : Cell) {point : Cell}
    (member : point ∈
      translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (occurrenceCoordinatedRibbonClauseStub
          presentation entry color)) :
    InRibbonMacrocell
      (Cell.add (placement.translation translate)
        (occurrenceSourceClauseTarget presentation entry)) point := by
  unfold translatePolyline at member
  rcases List.mem_map.mp member with
    ⟨sourcePoint, sourceMember, rfl⟩
  exact
    (occurrenceCoordinatedRibbonClauseStub_points_bounded
      presentation compatible entry color sourceMember).add_center
        (placement.translation translate)

/-- A nonzero period shift cannot identify two active variable vertices in
the positioned source drawing. -/
theorem activeOccurrenceVariablePosition_ne_translated_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (first second : ActiveOccurrenceEntry source.erase)
    (translate : Cell) (translateNonzero : translate ≠ (0, 0)) :
    placement.position first.1.1 ≠
      Cell.add (placement.translation translate)
        (placement.position second.1.1) := by
  let planar := presentation.toPlanarIncidencePresentation
  have firstAtomMember :
      first.1.1 ∈ source.erase.variableOccurrences.dedup := by
    simpa [occurringVariables,
      PeriodicOneInThreeToThreeDM.occurringVariables] using first.atom_mem
  have secondAtomMember :
      second.1.1 ∈ source.erase.variableOccurrences.dedup := by
    simpa [occurringVariables,
      PeriodicOneInThreeToThreeDM.occurringVariables] using second.atom_mem
  have firstVertexMember :
      CNFVertex.variable first.1.1 ∈ source.erase.incidenceGraph.vertices := by
    apply List.mem_append.mpr
    left
    exact List.mem_map.mpr ⟨first.1.1, firstAtomMember, rfl⟩
  have secondVertexMember :
      CNFVertex.variable second.1.1 ∈ source.erase.incidenceGraph.vertices := by
    apply List.mem_append.mpr
    left
    exact List.mem_map.mpr ⟨second.1.1, secondAtomMember, rfl⟩
  intro positionsEqual
  have atomsEqual : first.1.1 = second.1.1 :=
    CNFVertex.variable.inj
      (planar.incidenceVertexPositionAt_eq_translated_imp_eq
        firstVertexMember secondVertexMember translate positionsEqual)
  have translationZero : placement.translation translate = (0, 0) := by
    apply Cell.add_left_injective (placement.position first.1.1)
    simpa [atomsEqual, Cell.add, add_comm] using positionsEqual.symm
  have periodNonzero : (placement.period : Int) ≠ 0 := by
    exact_mod_cast presentation.periodPositive.ne'
  have translateZero : translate = (0, 0) := by
    apply Cell.scale_injective periodNonzero
    simpa [PeriodicVariablePlacement.translation, Cell.scale] using
      translationZero
  exact translateNonzero translateZero

/-- A source variable vertex cannot equal any period translate of a lifted
source-clause target. -/
theorem occurrenceSourceVariablePosition_ne_translatedClauseTarget
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (first second : ActiveOccurrenceEntry source.erase)
    (translate : Cell) :
    placement.position first.1.1 ≠
      Cell.add (placement.translation translate)
        (occurrenceSourceClauseTarget
          presentation.toPlanarIncidencePresentation second) := by
  let planar := presentation.toPlanarIncidencePresentation
  let secondData := occurrenceSpliceData planar second
  have firstAtomMember :
      first.1.1 ∈ source.erase.variableOccurrences.dedup := by
    simpa [occurringVariables,
      PeriodicOneInThreeToThreeDM.occurringVariables] using first.atom_mem
  have firstVertexMember :
      CNFVertex.variable first.1.1 ∈ source.erase.incidenceGraph.vertices := by
    apply List.mem_append.mpr
    left
    exact List.mem_map.mpr ⟨first.1.1, firstAtomMember, rfl⟩
  have secondEdgeMember :=
    PeriodicCNF.tagged_incidence_edge_mem
      source.erase secondData.indexedMember
  have secondEndpointMembers :=
    planar.compatible.1.2 secondData.indexed.1.edge
      (List.fst_mem_of_mem_zipIdx secondEdgeMember)
  have secondClauseVertexMember :
      CNFVertex.clause secondData.indexed.1.clauseIndex ∈
        source.erase.incidenceGraph.vertices := by
    simpa [CNFIncidence.edge, PeriodicCNF.incidenceEdge] using
      secondEndpointMembers.1
  have secondIndexLt :
      secondData.indexed.1.clauseIndex < source.clauses.length :=
    (List.mem_zipIdx' secondData.clauseMember).1
  have secondClauseLookup :
      source.clauses[secondData.indexed.1.clauseIndex] =
        secondData.positionedClause := by
    have lookup :=
      (List.mem_zipIdx_iff_getElem?).mp secondData.clauseMember
    rw [List.getElem?_eq_getElem secondIndexLt] at lookup
    exact Option.some.inj lookup
  let routeTranslate :=
    Cell.sub
      (PeriodicCNF.clauseAnchor secondData.positionedClause.literals)
      secondData.tagged.1.offset
  let combinedTranslate := Cell.add routeTranslate translate
  intro equal
  have liftedEqual :
      PositionedPeriodicCNF.incidenceVertexPositionAt source placement
          (.variable first.1.1) =
        Cell.add (placement.translation combinedTranslate)
          (PositionedPeriodicCNF.incidenceVertexPositionAt source placement
            (.clause secondData.indexed.1.clauseIndex)) := by
    rw [PositionedPeriodicCNF.incidenceVertexPositionAt_clause
      source placement secondData.indexed.1.clauseIndex secondIndexLt,
      secondClauseLookup]
    change placement.position first.1.1 = _
    rw [equal]
    rcases secondData.positionedClause.position with ⟨clauseX, clauseY⟩
    rcases PeriodicCNF.clauseAnchor
        secondData.positionedClause.literals with ⟨anchorX, anchorY⟩
    rcases secondData.tagged.1.offset with ⟨offsetX, offsetY⟩
    rcases translate with ⟨translateX, translateY⟩
    apply Prod.ext <;>
      simp [occurrenceSourceClauseTarget,
        PositionedPeriodicCNF.variableToClauseTarget,
        PositionedPeriodicCNF.canonicalClausePosition,
        PeriodicOneInThreeToThreeDM.reverseOffset,
        PeriodicVariablePlacement.translation,
        routeTranslate, combinedTranslate, planar, secondData,
        Cell.add, Cell.sub, Cell.scale] <;> ring
  have verticesEqual :=
    planar.incidenceVertexPositionAt_eq_translated_imp_eq
      firstVertexMember secondClauseVertexMember
      combinedTranslate liftedEqual
  cases verticesEqual

/-- Local copy of the incidence/positioned-clause lookup used to compare
periodically aligned clause targets. -/
private theorem indexedIncidence_clause_eq_positionedClause_literals_for_translated_fans
    {Variable : Type*}
    {source : PositionedPeriodicCNF Variable}
    {indexed : CNFIncidence Variable × Nat}
    (indexedMember :
      indexed ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx)
    {positionedClause : PositionedPeriodicClause Variable}
    (clauseMember :
      (positionedClause, indexed.1.clauseIndex) ∈ source.clauses.zipIdx) :
    indexed.1.clause = positionedClause.literals := by
  have incidenceMember :
      indexed.1 ∈ PeriodicCNF.incidencesWithMetadata source.erase :=
    List.fst_mem_of_mem_zipIdx indexedMember
  have indexedClauseMember :=
    (PeriodicCNF.mem_incidencesWithMetadata_iff
      source.erase indexed.1).mp incidenceMember |>.1
  have positionedClauseMember :
      (positionedClause.literals, indexed.1.clauseIndex) ∈
        source.erase.clauses.zipIdx := by
    change (positionedClause.literals, indexed.1.clauseIndex) ∈
      (source.clauses.map PositionedPeriodicClause.literals).zipIdx
    rw [List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(positionedClause, indexed.1.clauseIndex), clauseMember, rfl⟩
  exact (List.mem_zipIdx' indexedClauseMember).2.trans
    (List.mem_zipIdx' positionedClauseMember).2.symm

/-- Periodically aligned lifted clause targets come from the same prototype
clause vertex. -/
theorem occurrenceSourceClauseTarget_eq_translated_imp_clauseIndex_eq
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (first second : ActiveOccurrenceEntry source.erase)
    (translate : Cell)
    (equal :
      occurrenceSourceClauseTarget
          presentation.toPlanarIncidencePresentation first =
        Cell.add (placement.translation translate)
          (occurrenceSourceClauseTarget
            presentation.toPlanarIncidencePresentation second)) :
    occurrenceClauseIndex source.erase first.1.1 first.1.2 =
      occurrenceClauseIndex source.erase second.1.1 second.1.2 := by
  let planar := presentation.toPlanarIncidencePresentation
  let firstData := occurrenceSpliceData planar first
  let secondData := occurrenceSpliceData planar second
  have firstEdgeMember :=
    PeriodicCNF.tagged_incidence_edge_mem
      source.erase firstData.indexedMember
  have secondEdgeMember :=
    PeriodicCNF.tagged_incidence_edge_mem
      source.erase secondData.indexedMember
  have firstEndpointMembers :=
    planar.compatible.1.2 firstData.indexed.1.edge
      (List.fst_mem_of_mem_zipIdx firstEdgeMember)
  have secondEndpointMembers :=
    planar.compatible.1.2 secondData.indexed.1.edge
      (List.fst_mem_of_mem_zipIdx secondEdgeMember)
  have firstClauseVertexMember :
      CNFVertex.clause firstData.indexed.1.clauseIndex ∈
        source.erase.incidenceGraph.vertices := by
    simpa [CNFIncidence.edge, PeriodicCNF.incidenceEdge] using
      firstEndpointMembers.1
  have secondClauseVertexMember :
      CNFVertex.clause secondData.indexed.1.clauseIndex ∈
        source.erase.incidenceGraph.vertices := by
    simpa [CNFIncidence.edge, PeriodicCNF.incidenceEdge] using
      secondEndpointMembers.1
  have firstIndexLt :
      firstData.indexed.1.clauseIndex < source.clauses.length :=
    (List.mem_zipIdx' firstData.clauseMember).1
  have secondIndexLt :
      secondData.indexed.1.clauseIndex < source.clauses.length :=
    (List.mem_zipIdx' secondData.clauseMember).1
  have firstClauseLookup :
      source.clauses[firstData.indexed.1.clauseIndex] =
        firstData.positionedClause := by
    have lookup := (List.mem_zipIdx_iff_getElem?).mp firstData.clauseMember
    rw [List.getElem?_eq_getElem firstIndexLt] at lookup
    exact Option.some.inj lookup
  have secondClauseLookup :
      source.clauses[secondData.indexed.1.clauseIndex] =
        secondData.positionedClause := by
    have lookup := (List.mem_zipIdx_iff_getElem?).mp secondData.clauseMember
    rw [List.getElem?_eq_getElem secondIndexLt] at lookup
    exact Option.some.inj lookup
  have firstVertexPosition :
      PositionedPeriodicCNF.incidenceVertexPositionAt source placement
          (.clause firstData.indexed.1.clauseIndex) =
        PositionedPeriodicCNF.canonicalClausePosition
          placement firstData.positionedClause := by
    rw [PositionedPeriodicCNF.incidenceVertexPositionAt_clause
      source placement firstData.indexed.1.clauseIndex firstIndexLt,
      firstClauseLookup]
  have secondVertexPosition :
      PositionedPeriodicCNF.incidenceVertexPositionAt source placement
          (.clause secondData.indexed.1.clauseIndex) =
        PositionedPeriodicCNF.canonicalClausePosition
          placement secondData.positionedClause := by
    rw [PositionedPeriodicCNF.incidenceVertexPositionAt_clause
      source placement secondData.indexed.1.clauseIndex secondIndexLt,
      secondClauseLookup]
  have firstClauseEq :
      firstData.indexed.1.clause = firstData.positionedClause.literals :=
    indexedIncidence_clause_eq_positionedClause_literals_for_translated_fans
      firstData.indexedMember firstData.clauseMember
  have secondClauseEq :
      secondData.indexed.1.clause = secondData.positionedClause.literals :=
    indexedIncidence_clause_eq_positionedClause_literals_for_translated_fans
      secondData.indexedMember secondData.clauseMember
  have firstLiteralEq : firstData.indexed.1.literal = firstData.tagged.1 :=
    congrArg Prod.fst firstData.metadataEq
  have secondLiteralEq : secondData.indexed.1.literal = secondData.tagged.1 :=
    congrArg Prod.fst secondData.metadataEq
  let firstTranslate :=
    PositionedPeriodicCNF.variableToClauseTranslate firstData.indexed.1
  let secondTranslate :=
    PositionedPeriodicCNF.variableToClauseTranslate secondData.indexed.1
  let relativeTranslate :=
    Cell.add (Cell.sub secondTranslate firstTranslate) translate
  have liftedEqual :
      PositionedPeriodicCNF.incidenceVertexPositionAt source placement
          (.clause firstData.indexed.1.clauseIndex) =
        Cell.add (placement.translation relativeTranslate)
          (PositionedPeriodicCNF.incidenceVertexPositionAt source placement
            (.clause secondData.indexed.1.clauseIndex)) := by
    rw [firstVertexPosition, secondVertexPosition]
    rcases firstData.positionedClause.position with ⟨firstX, firstY⟩
    rcases secondData.positionedClause.position with ⟨secondX, secondY⟩
    rcases PeriodicCNF.clauseAnchor firstData.positionedClause.literals with
      ⟨firstAnchorX, firstAnchorY⟩
    rcases PeriodicCNF.clauseAnchor secondData.positionedClause.literals with
      ⟨secondAnchorX, secondAnchorY⟩
    rcases firstData.tagged.1.offset with ⟨firstOffsetX, firstOffsetY⟩
    rcases secondData.tagged.1.offset with ⟨secondOffsetX, secondOffsetY⟩
    rcases translate with ⟨translateX, translateY⟩
    simp only [occurrenceSourceClauseTarget,
      PositionedPeriodicCNF.variableToClauseTarget,
      PositionedPeriodicCNF.canonicalClausePosition,
      PositionedPeriodicCNF.variableToClauseTranslate,
      PeriodicOneInThreeToThreeDM.reverseOffset,
      PeriodicVariablePlacement.translation,
      Cell.add, Cell.sub, Cell.scale, Prod.mk.injEq,
      planar, firstData, secondData, firstTranslate, secondTranslate,
      relativeTranslate, firstClauseEq, secondClauseEq,
      firstLiteralEq, secondLiteralEq] at equal ⊢
    constructor
    · linear_combination equal.1
    · linear_combination equal.2
  have clauseVerticesEqual :=
    planar.incidenceVertexPositionAt_eq_translated_imp_eq
      firstClauseVertexMember secondClauseVertexMember
      relativeTranslate liftedEqual
  have indexedClauseIndicesEqual :
      firstData.indexed.1.clauseIndex = secondData.indexed.1.clauseIndex :=
    CNFVertex.clause.inj clauseVerticesEqual
  rw [occurrenceClauseIndex_eq_indexedClauseIndex planar first,
    occurrenceClauseIndex_eq_indexedClauseIndex planar second]
  exact indexedClauseIndicesEqual

/-- A translated clause endpoint cannot occupy the internal first neighbor
of a length-three unshifted occurrence route. -/
theorem translatedOccurrenceSourceClauseTarget_ne_firstVariableNeighbor
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (first second : ActiveOccurrenceEntry source.erase)
    (translate : Cell) (translateNonzero : translate ≠ (0, 0))
    (firstLength :
      3 ≤
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation first).length) :
    Cell.add (placement.translation translate)
        (occurrenceSourceClauseTarget
          presentation.toPlanarIncidencePresentation second) ≠
      Cell.add (placement.position first.1.1)
        (occurrenceSourceVariableDirection
          presentation.toPlanarIncidencePresentation first).step := by
  let planar := presentation.toPlanarIncidencePresentation
  let firstRoute := occurrenceUnitSourceRoute planar first
  let secondRoute := occurrenceUnitSourceRoute planar second
  let translatedSecondRoute :=
    translatePolyline (placement.translation translate) secondRoute
  let secondTarget := Cell.add (placement.translation translate)
    (occurrenceSourceClauseTarget planar second)
  have firstLength' : 3 ≤ firstRoute.length := by
    simpa [firstRoute, planar] using firstLength
  have firstNodup : firstRoute.Nodup := by
    simpa [firstRoute, planar] using
      occurrenceUnitSourceRoute_nodup presentation first
  have firstUnitSteps :
      firstRoute.IsChain AxisDirection.IsUnitAxisStep := by
    simpa [firstRoute] using occurrenceUnitSourceRoute_unitSteps planar first
  have firstHead :
      firstRoute.head? = some (placement.position first.1.1) := by
    simpa [firstRoute] using
      occurrenceUnitSourceRoute_variableEndpoint_head? planar first
  have secondTargetMember : secondTarget ∈ translatedSecondRoute := by
    unfold translatedSecondRoute translatePolyline
    apply List.mem_map.mpr
    exact ⟨occurrenceSourceClauseTarget planar second,
      occurrenceUnitSourceRoute_clauseEndpoint_mem planar second, rfl⟩
  have meetOnly :
      RoutesMeetOnlyAtEndpoints firstRoute translatedSecondRoute := by
    simpa [firstRoute, secondRoute, translatedSecondRoute, planar,
      PeriodicVariablePlacement.translation, Cell.scale] using
      translatedOccurrenceUnitSourceRoutes_meetOnlyAtEndpoints
        presentation first second (0, 0) translate
          (occurrenceSourceRouteKeyAt_zero_ne_of_translate_ne_zero
            planar first second translateNonzero)
  cases firstEquation : firstRoute with
  | nil => simp [firstEquation] at firstLength'
  | cons firstPoint firstTail =>
      cases firstTail with
      | nil => simp [firstEquation] at firstLength'
      | cons firstNext firstRest =>
          cases firstRest with
          | nil => simp [firstEquation] at firstLength'
          | cons firstThird firstRest =>
              have firstPointEq :
                  firstPoint = placement.position first.1.1 := by
                rw [firstEquation] at firstHead
                exact Option.some.inj firstHead
              have firstUnit :
                  AxisDirection.IsUnitAxisStep firstPoint firstNext := by
                rw [firstEquation] at firstUnitSteps
                exact (List.isChain_cons_cons.mp firstUnitSteps).1
              have firstNextEq :
                  firstNext =
                    Cell.add (placement.position first.1.1)
                      (occurrenceSourceVariableDirection planar first).step := by
                change firstNext = Cell.add (placement.position first.1.1)
                  (AxisDirection.polylineFirstDirection firstRoute).step
                rw [firstEquation]
                simp only [AxisDirection.polylineFirstDirection_cons_cons]
                rw [← firstPointEq]
                exact AxisDirection.add_between_step_eq_of_unitAxisStep firstUnit
              have firstNextMember : firstNext ∈ firstRoute := by
                rw [firstEquation]
                simp
              have firstNextInternal :
                  ¬RoutePointIsEndpoint firstRoute firstNext := by
                apply routeCenter_not_endpoint_of_nodup_of_eq_append_triple
                  (leading := []) (trailing := firstRest)
                  (previous := firstPoint) (next := firstThird)
                · simpa [firstEquation]
                · exact firstNodup
              intro targetEq
              have targetEqNext : secondTarget = firstNext :=
                targetEq.trans firstNextEq.symm
              have differentPoints : firstNext ≠ secondTarget :=
                routePoints_ne_of_routesMeetOnlyAtEndpoints
                  meetOnly firstNextMember secondTargetMember
                  (Or.inl firstNextInternal)
              exact differentPoints targetEqNext.symm

/-- Variable-side fans on distinct nonzero lifted copies are strictly
separated for arbitrary colors and occurrence entries. -/
theorem occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_translatedOccurrenceCoordinatedRibbonVariableStub_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (first second : ActiveOccurrenceEntry source.erase)
    (translate : Cell) (translateNonzero : translate ≠ (0, 0))
    (firstColor secondColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (occurrenceCoordinatedRibbonVariableStub
        presentation.toPlanarIncidencePresentation first firstColor)
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (occurrenceCoordinatedRibbonVariableStub
          presentation.toPlanarIncidencePresentation second secondColor)) := by
  let planar := presentation.toPlanarIncidencePresentation
  let firstCenter := placement.position first.1.1
  let secondCenter := Cell.add (placement.translation translate)
    (placement.position second.1.1)
  have centersNe : firstCenter ≠ secondCenter :=
    activeOccurrenceVariablePosition_ne_translated_of_nonzero
      presentation first second translate translateNonzero
  rcases ribbonMacrocellCenters_eq_or_far_or_adjacent
      firstCenter secondCenter with
    centersEqual | centersFar | centersAdjacent
  · exact (centersNe centersEqual).elim
  · exact routesStrictlyAvoidEachOther_of_inFarRibbonMacrocells
      (fun point member =>
        occurrenceCoordinatedRibbonVariableStub_points_bounded
          planar compatible first firstColor member)
      (fun point member =>
        translatedOccurrenceCoordinatedRibbonVariableStub_points_bounded
          planar compatible second secondColor translate member)
      centersFar
  · let firstData := sourceVariableRibbonFanData planar first
    let secondData := sourceVariableRibbonFanData planar second
    let firstSlot := occurrenceVariableSiteSlot first.1.2
    let secondSlot := occurrenceVariableSiteSlot second.1.2
    let offset := Cell.sub secondCenter firstCenter
    have firstActive : firstData.SlotActive firstSlot :=
      VariableRibbonFanData.sourceVariableRibbonFanData_slotActive planar first
    have secondActive : secondData.SlotActive secondSlot :=
      VariableRibbonFanData.sourceVariableRibbonFanData_slotActive planar second
    have notFacing : ∀ direction, direction.IsGenuine →
        offset ≠ direction.step ∨
          firstData.direction firstSlot ≠ direction ∨
          secondData.direction secondSlot ≠ direction.opposite := by
      let firstRoute := occurrenceSourceRoute planar first
      let secondRoute := occurrenceSourceRoute planar second
      let translatedSecondRoute :=
        translatePolyline (placement.translation translate) secondRoute
      let firstSplice := occurrenceSpliceData planar first
      let secondSplice := occurrenceSpliceData planar second
      have firstAtom : firstSplice.tagged.1.atom = first.1.1 :=
        (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
          source.erase first.1.1 first.1.2 firstSplice.tagged
          firstSplice.occurrenceLookup).2
      have secondAtom : secondSplice.tagged.1.atom = second.1.1 :=
        (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
          source.erase second.1.1 second.1.2 secondSplice.tagged
          secondSplice.occurrenceLookup).2
      have firstHead : firstRoute.head? = some firstCenter := by
        simpa [firstRoute, firstCenter, occurrenceSourceRoute,
          firstSplice, firstAtom] using firstSplice.routeHead
      have secondHead : translatedSecondRoute.head? = some secondCenter := by
        have originalHead : secondRoute.head? =
            some (placement.position second.1.1) := by
          simpa [secondRoute, occurrenceSourceRoute,
            secondSplice, secondAtom] using secondSplice.routeHead
        simpa [translatedSecondRoute, translatePolyline, secondCenter]
          using congrArg (Option.map (Cell.add (placement.translation translate)))
            originalHead
      intro direction genuine
      by_cases offsetDifferent : offset ≠ direction.step
      · exact Or.inl offsetDifferent
      · right
        have offsetEqual : offset = direction.step :=
          not_ne_iff.mp offsetDifferent
        change Cell.sub secondCenter firstCenter = direction.step at offsetEqual
        have adjacent : secondCenter =
            Cell.add firstCenter direction.step := by
          calc
            secondCenter = Cell.add firstCenter
                (Cell.sub secondCenter firstCenter) := by
              rcases firstCenter with ⟨firstX, firstY⟩
              rcases secondCenter with ⟨secondX, secondY⟩
              simp [Cell.add, Cell.sub]
            _ = Cell.add firstCenter direction.step := by rw [offsetEqual]
        have separated :=
          polylineFirstDirections_not_facing_of_routesAvoidEachOther
            (occurrenceSourceRoute_length planar first)
            (by simpa [translatedSecondRoute, translatePolyline, secondRoute]
              using occurrenceSourceRoute_length planar second)
            firstHead secondHead genuine adjacent
            (by
              simpa [firstRoute, secondRoute, translatedSecondRoute, planar,
                PeriodicVariablePlacement.translation, Cell.scale] using
                (translatedOccurrenceSourceRoutes_avoidEachOther
                  presentation first second (0, 0) translate
                    (occurrenceSourceRouteKeyAt_zero_ne_of_translate_ne_zero
                      planar first second translateNonzero)))
        simpa [firstData, secondData, firstSlot, secondSlot,
          planar,
          occurrenceSourceVariableDirection_eq_sourceRoute,
          firstRoute, secondRoute, translatedSecondRoute] using separated
    have localAvoid :=
      firstData.coordinatedRoutes_strictlyAvoidEachOther_of_adjacent_notFacing
        secondData (compatible.1 first) (compatible.1 second)
        firstSlot secondSlot firstActive secondActive
        firstColor secondColor offset centersAdjacent notFacing
    have translatedAvoid :=
      localAvoid.translatePolyline (ribbonMacrocellOrigin firstCenter)
    have originEq :
        Cell.add
            (Cell.scale standardThreeStrandLayout.factor offset)
            (ribbonMacrocellOrigin firstCenter) =
          ribbonMacrocellOrigin secondCenter := by
      rcases firstCenter with ⟨firstX, firstY⟩
      rcases secondCenter with ⟨secondX, secondY⟩
      apply Prod.ext <;>
        simp [offset, ribbonMacrocellOrigin,
          Cell.add, Cell.sub, Cell.scale] <;> ring
    rw [translatePolyline_add, originEq] at translatedAvoid
    have secondOriginEq :
        ribbonMacrocellOrigin secondCenter =
          Cell.add
            (ribbonMacrocellOrigin (placement.position second.1.1))
            (ribbonMacrocellOrigin (placement.translation translate)) := by
      rcases translate with ⟨translateX, translateY⟩
      rcases positionEq : placement.position second.1.1 with
        ⟨positionX, positionY⟩
      apply Prod.ext <;>
        simp [secondCenter, ribbonMacrocellOrigin,
          PeriodicVariablePlacement.translation,
          standardThreeStrandLayout, positionEq,
          Cell.add, Cell.scale] <;> ring
    rw [secondOriginEq] at translatedAvoid
    simpa [occurrenceCoordinatedRibbonVariableStub,
      translatePolyline_add, planar, firstData, secondData,
      firstSlot, secondSlot, firstCenter, secondCenter,
      add_comm, add_left_comm, add_assoc] using
        translatedAvoid

/-- A variable-side fan strictly avoids every nonzero translated clause-side
fan when the variable route contains an interior source point. -/
theorem occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_translatedOccurrenceCoordinatedRibbonClauseStub_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (first second : ActiveOccurrenceEntry source.erase)
    (translate : Cell) (translateNonzero : translate ≠ (0, 0))
    (firstLength :
      3 ≤
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation first).length)
    (firstColor secondColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (occurrenceCoordinatedRibbonVariableStub
        presentation.toPlanarIncidencePresentation first firstColor)
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (occurrenceCoordinatedRibbonClauseStub
          presentation.toPlanarIncidencePresentation second secondColor)) := by
  let planar := presentation.toPlanarIncidencePresentation
  let firstCenter := placement.position first.1.1
  let secondCenter := Cell.add (placement.translation translate)
    (occurrenceSourceClauseTarget planar second)
  have centersNe : firstCenter ≠ secondCenter :=
    occurrenceSourceVariablePosition_ne_translatedClauseTarget
      presentation first second translate
  rcases ribbonMacrocellCenters_eq_or_far_or_adjacent
      firstCenter secondCenter with
    centersEqual | centersFar | centersAdjacent
  · exact (centersNe centersEqual).elim
  · exact routesStrictlyAvoidEachOther_of_inFarRibbonMacrocells
      (fun point member =>
        occurrenceCoordinatedRibbonVariableStub_points_bounded
          planar compatible first firstColor member)
      (fun point member =>
        translatedOccurrenceCoordinatedRibbonClauseStub_points_bounded
          planar compatible second secondColor translate member)
      centersFar
  · let firstData := sourceVariableRibbonFanData planar first
    let secondClauseIndex :=
      occurrenceClauseIndex source.erase second.1.1 second.1.2
    let secondData := sourceClauseRibbonFanData planar secondClauseIndex
    let firstSlot := occurrenceVariableSiteSlot first.1.2
    let secondGroup := occurrenceClauseTerminalGroup source.erase second
    let secondLane := routedRibbonLane source.erase second secondColor
    let offset := Cell.sub secondCenter firstCenter
    have firstActive : firstData.SlotActive firstSlot :=
      VariableRibbonFanData.sourceVariableRibbonFanData_slotActive planar first
    have secondMember :
        second ∈ activeClauseOccurrenceEntries
          source.erase secondClauseIndex :=
      second.mem_activeClauseOccurrenceEntries
    have secondActive : secondData.GroupActive secondGroup :=
      ClauseRibbonFanData.sourceClauseRibbonFanData_groupActive
        planar secondClauseIndex second secondMember
    have notFirstNeighbor :
        offset ≠ (firstData.direction firstSlot).step := by
      intro offsetEqual
      have targetEqual : secondCenter =
          Cell.add firstCenter (firstData.direction firstSlot).step := by
        change Cell.sub secondCenter firstCenter =
          (firstData.direction firstSlot).step at offsetEqual
        calc
          secondCenter = Cell.add firstCenter
              (Cell.sub secondCenter firstCenter) := by
            rcases firstCenter with ⟨firstX, firstY⟩
            rcases secondCenter with ⟨secondX, secondY⟩
            simp [Cell.add, Cell.sub]
          _ = Cell.add firstCenter (firstData.direction firstSlot).step := by
            rw [offsetEqual]
      apply
        translatedOccurrenceSourceClauseTarget_ne_firstVariableNeighbor
          presentation first second translate translateNonzero firstLength
      rw [← VariableRibbonFanData.sourceVariableRibbonFanData_direction
        planar first]
      exact targetEqual
    have localAvoid :=
      firstData.coordinatedRoute_strictlyAvoids_clauseCoordinatedRoute_of_adjacent_notFirstNeighbor
        secondData (compatible.1 first) (compatible.2 second)
        firstSlot secondGroup firstActive secondActive
        firstColor secondLane offset centersAdjacent notFirstNeighbor
    have translatedAvoid :=
      localAvoid.translatePolyline (ribbonMacrocellOrigin firstCenter)
    have originEq :
        Cell.add
            (Cell.scale standardThreeStrandLayout.factor offset)
            (ribbonMacrocellOrigin firstCenter) =
          ribbonMacrocellOrigin secondCenter := by
      rcases firstCenter with ⟨firstX, firstY⟩
      rcases secondCenter with ⟨secondX, secondY⟩
      apply Prod.ext <;>
        simp [offset, ribbonMacrocellOrigin,
          Cell.add, Cell.sub, Cell.scale] <;> ring
    rw [translatePolyline_add, originEq] at translatedAvoid
    have secondOriginEq :
        ribbonMacrocellOrigin secondCenter =
          Cell.add
            (ribbonMacrocellOrigin
              (occurrenceSourceClauseTarget planar second))
            (ribbonMacrocellOrigin (placement.translation translate)) := by
      rcases translate with ⟨translateX, translateY⟩
      rcases targetEq : occurrenceSourceClauseTarget planar second with
        ⟨targetX, targetY⟩
      apply Prod.ext <;>
        simp [secondCenter, ribbonMacrocellOrigin,
          PeriodicVariablePlacement.translation,
          standardThreeStrandLayout, targetEq,
          Cell.add, Cell.scale] <;> ring
    rw [secondOriginEq] at translatedAvoid
    simpa [occurrenceCoordinatedRibbonVariableStub,
      occurrenceCoordinatedRibbonClauseStub, translatePolyline_add,
      planar, firstData, secondData, firstSlot, secondClauseIndex,
      secondGroup, secondLane, firstCenter, secondCenter,
      add_comm, add_left_comm, add_assoc] using translatedAvoid

/-- Clause-side fans on distinct nonzero lifted copies are strictly separated
for arbitrary colors and occurrence entries. -/
theorem occurrenceCoordinatedRibbonClauseStub_strictlyAvoids_translatedOccurrenceCoordinatedRibbonClauseStub_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (first second : ActiveOccurrenceEntry source.erase)
    (translate : Cell) (translateNonzero : translate ≠ (0, 0))
    (firstColor secondColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (occurrenceCoordinatedRibbonClauseStub
        presentation.toPlanarIncidencePresentation first firstColor)
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (occurrenceCoordinatedRibbonClauseStub
          presentation.toPlanarIncidencePresentation second secondColor)) := by
  let planar := presentation.toPlanarIncidencePresentation
  let firstCenter := occurrenceSourceClauseTarget planar first
  let secondCenter := Cell.add (placement.translation translate)
    (occurrenceSourceClauseTarget planar second)
  rcases ribbonMacrocellCenters_eq_or_far_or_adjacent
      firstCenter secondCenter with
    centersEqual | centersFar | centersAdjacent
  · have sameClauseIndex :=
      occurrenceSourceClauseTarget_eq_translated_imp_clauseIndex_eq
        presentation first second translate centersEqual
    let clauseIndex :=
      occurrenceClauseIndex source.erase first.1.1 first.1.2
    let data := sourceClauseRibbonFanData planar clauseIndex
    let firstGroup := occurrenceClauseTerminalGroup source.erase first
    let secondGroup := occurrenceClauseTerminalGroup source.erase second
    let firstLane := routedRibbonLane source.erase first firstColor
    let secondLane := routedRibbonLane source.erase second secondColor
    have firstMember :
        first ∈ activeClauseOccurrenceEntries source.erase clauseIndex :=
      first.mem_activeClauseOccurrenceEntries
    have secondMember :
        second ∈ activeClauseOccurrenceEntries source.erase clauseIndex := by
      rw [mem_activeClauseOccurrenceEntries_iff]
      exact sameClauseIndex.symm
    have firstActive : data.GroupActive firstGroup :=
      ClauseRibbonFanData.sourceClauseRibbonFanData_groupActive
        planar clauseIndex first firstMember
    have secondActive : data.GroupActive secondGroup :=
      ClauseRibbonFanData.sourceClauseRibbonFanData_groupActive
        planar clauseIndex second secondMember
    have strandsDifferent :
        RibbonStrandsDifferent first firstColor second secondColor := by
      intro strandsEqual
      have entriesEqual : first = second := congrArg Prod.fst strandsEqual
      subst second
      have targetEqual :
          occurrenceSourceClauseTarget planar first =
            Cell.add (placement.translation translate)
              (occurrenceSourceClauseTarget planar first) := by
        simpa [firstCenter, secondCenter] using centersEqual
      have translationZero : placement.translation translate = (0, 0) := by
        apply Cell.add_left_injective
          (occurrenceSourceClauseTarget planar first)
        simpa [Cell.add, add_comm] using targetEqual.symm
      have periodNonzero : (placement.period : Int) ≠ 0 := by
        exact_mod_cast presentation.periodPositive.ne'
      have translateZero : translate = (0, 0) := by
        apply Cell.scale_injective periodNonzero
        simpa [PeriodicVariablePlacement.translation, Cell.scale] using
          translationZero
      exact translateNonzero translateZero
    have localDifferent :
        (firstGroup, firstLane) ≠ (secondGroup, secondLane) := by
      intro equal
      have groupEqual : firstGroup = secondGroup := congrArg Prod.fst equal
      have occurrenceEqual : first = second :=
        sourceClauseTerminalGroupsUnique_of_widthAtMostThree
          planar width clauseIndex first second firstMember secondMember
          groupEqual
      subst second
      have colorEqual : firstColor = secondColor :=
        routedRibbonLane_injective source.erase first (congrArg Prod.snd equal)
      exact strandsDifferent (Prod.ext rfl colorEqual)
    have localAvoid :
        RoutesStrictlyAvoidEachOther
          (data.coordinatedRoute firstGroup firstLane)
          (data.coordinatedRoute secondGroup secondLane) :=
      ClauseRibbonFanData.coordinatedRoutes_strictlyAvoidEachOther
        data (compatible.2 first)
        firstGroup secondGroup firstActive secondActive
        firstLane secondLane localDifferent
    have translatedAvoid :=
      localAvoid.translatePolyline (ribbonMacrocellOrigin firstCenter)
    have secondOriginEq :
        ribbonMacrocellOrigin secondCenter =
          Cell.add
            (ribbonMacrocellOrigin
              (occurrenceSourceClauseTarget planar second))
            (ribbonMacrocellOrigin (placement.translation translate)) := by
      rcases translate with ⟨translateX, translateY⟩
      rcases targetEq : occurrenceSourceClauseTarget planar second with
        ⟨targetX, targetY⟩
      apply Prod.ext <;>
        simp [secondCenter, ribbonMacrocellOrigin,
          PeriodicVariablePlacement.translation,
          standardThreeStrandLayout, targetEq,
          Cell.add, Cell.scale] <;> ring
    have firstStubEq :
        occurrenceCoordinatedRibbonClauseStub planar first firstColor =
          translatePolyline (ribbonMacrocellOrigin firstCenter)
            (data.coordinatedRoute firstGroup firstLane) := by
      simp [occurrenceCoordinatedRibbonClauseStub,
        firstCenter, clauseIndex, data, firstGroup, firstLane]
    have secondStubEq :
        translatePolyline
            (ribbonMacrocellOrigin (placement.translation translate))
            (occurrenceCoordinatedRibbonClauseStub
              planar second secondColor) =
          translatePolyline (ribbonMacrocellOrigin firstCenter)
            (data.coordinatedRoute secondGroup secondLane) := by
      simp only [occurrenceCoordinatedRibbonClauseStub,
        translatePolyline_add]
      rw [← secondOriginEq, ← centersEqual]
      simp [clauseIndex, data, secondGroup, secondLane, sameClauseIndex]
    rw [firstStubEq, secondStubEq]
    exact translatedAvoid
  · exact routesStrictlyAvoidEachOther_of_inFarRibbonMacrocells
      (fun point member =>
        occurrenceCoordinatedRibbonClauseStub_points_bounded
          planar compatible first firstColor member)
      (fun point member =>
        translatedOccurrenceCoordinatedRibbonClauseStub_points_bounded
          planar compatible second secondColor translate member)
      centersFar
  · let firstClauseIndex :=
      occurrenceClauseIndex source.erase first.1.1 first.1.2
    let secondClauseIndex :=
      occurrenceClauseIndex source.erase second.1.1 second.1.2
    let firstData := sourceClauseRibbonFanData planar firstClauseIndex
    let secondData := sourceClauseRibbonFanData planar secondClauseIndex
    let firstGroup := occurrenceClauseTerminalGroup source.erase first
    let secondGroup := occurrenceClauseTerminalGroup source.erase second
    let firstLane := routedRibbonLane source.erase first firstColor
    let secondLane := routedRibbonLane source.erase second secondColor
    let offset := Cell.sub secondCenter firstCenter
    have firstMember :
        first ∈ activeClauseOccurrenceEntries
          source.erase firstClauseIndex :=
      first.mem_activeClauseOccurrenceEntries
    have secondMember :
        second ∈ activeClauseOccurrenceEntries
          source.erase secondClauseIndex :=
      second.mem_activeClauseOccurrenceEntries
    have firstActive : firstData.GroupActive firstGroup :=
      ClauseRibbonFanData.sourceClauseRibbonFanData_groupActive
        planar firstClauseIndex first firstMember
    have secondActive : secondData.GroupActive secondGroup :=
      ClauseRibbonFanData.sourceClauseRibbonFanData_groupActive
        planar secondClauseIndex second secondMember
    have notFacing : ∀ direction, direction.IsGenuine →
        offset ≠ direction.step ∨
          firstData.direction firstGroup ≠ direction.opposite ∨
          secondData.direction secondGroup ≠ direction := by
      let firstRoute := occurrenceSourceRoute planar first
      let secondRoute := occurrenceSourceRoute planar second
      let translatedSecondRoute :=
        translatePolyline (placement.translation translate) secondRoute
      let firstSplice := occurrenceSpliceData planar first
      let secondSplice := occurrenceSpliceData planar second
      have firstLast : firstRoute.getLast? = some firstCenter := by
        simpa [firstRoute, firstCenter, occurrenceSourceRoute,
          occurrenceSourceClauseTarget, firstSplice] using firstSplice.routeLast
      have secondLast : translatedSecondRoute.getLast? = some secondCenter := by
        have originalLast : secondRoute.getLast? =
            some (occurrenceSourceClauseTarget planar second) := by
          simpa [secondRoute, occurrenceSourceRoute,
            occurrenceSourceClauseTarget, secondSplice] using
              secondSplice.routeLast
        simpa [translatedSecondRoute, translatePolyline, secondCenter] using
          congrArg (Option.map (Cell.add (placement.translation translate)))
            originalLast
      intro direction genuine
      by_cases offsetDifferent : offset ≠ direction.step
      · exact Or.inl offsetDifferent
      · right
        have offsetEqual : offset = direction.step :=
          not_ne_iff.mp offsetDifferent
        change Cell.sub secondCenter firstCenter = direction.step at offsetEqual
        have adjacent : secondCenter =
            Cell.add firstCenter direction.step := by
          calc
            secondCenter = Cell.add firstCenter
                (Cell.sub secondCenter firstCenter) := by
              rcases firstCenter with ⟨firstX, firstY⟩
              rcases secondCenter with ⟨secondX, secondY⟩
              simp [Cell.add, Cell.sub]
            _ = Cell.add firstCenter direction.step := by rw [offsetEqual]
        have separated :=
          polylineLastDirections_not_facing_of_routesAvoidEachOther
            (occurrenceSourceRoute_length planar first)
            (by simpa [translatedSecondRoute, translatePolyline, secondRoute]
              using occurrenceSourceRoute_length planar second)
            firstLast secondLast genuine adjacent
            (by
              simpa [firstRoute, secondRoute, translatedSecondRoute, planar,
                PeriodicVariablePlacement.translation, Cell.scale] using
                (translatedOccurrenceSourceRoutes_avoidEachOther
                  presentation first second (0, 0) translate
                    (occurrenceSourceRouteKeyAt_zero_ne_of_translate_ne_zero
                      planar first second translateNonzero)))
        rw [ClauseRibbonFanData.sourceClauseRibbonFanData_direction_at_occurrence_of_widthAtMostThree
            planar width first,
          ClauseRibbonFanData.sourceClauseRibbonFanData_direction_at_occurrence_of_widthAtMostThree
            planar width second]
        simpa [occurrenceSourceClauseDirection_eq_sourceRoute,
          firstRoute, secondRoute, translatedSecondRoute] using separated
    have localAvoid :=
      firstData.coordinatedRoutes_strictlyAvoidEachOther_of_adjacent_notFacing
        secondData (compatible.2 first) (compatible.2 second)
        firstGroup secondGroup firstActive secondActive
        firstLane secondLane offset centersAdjacent notFacing
    have translatedAvoid :=
      localAvoid.translatePolyline (ribbonMacrocellOrigin firstCenter)
    have originEq :
        Cell.add
            (Cell.scale standardThreeStrandLayout.factor offset)
            (ribbonMacrocellOrigin firstCenter) =
          ribbonMacrocellOrigin secondCenter := by
      rcases firstCenter with ⟨firstX, firstY⟩
      rcases secondCenter with ⟨secondX, secondY⟩
      apply Prod.ext <;>
        simp [offset, ribbonMacrocellOrigin,
          Cell.add, Cell.sub, Cell.scale] <;> ring
    rw [translatePolyline_add, originEq] at translatedAvoid
    have secondOriginEq :
        ribbonMacrocellOrigin secondCenter =
          Cell.add
            (ribbonMacrocellOrigin
              (occurrenceSourceClauseTarget planar second))
            (ribbonMacrocellOrigin (placement.translation translate)) := by
      rcases translate with ⟨translateX, translateY⟩
      rcases targetEq : occurrenceSourceClauseTarget planar second with
        ⟨targetX, targetY⟩
      apply Prod.ext <;>
        simp [secondCenter, ribbonMacrocellOrigin,
          PeriodicVariablePlacement.translation,
          standardThreeStrandLayout, targetEq,
          Cell.add, Cell.scale] <;> ring
    rw [secondOriginEq] at translatedAvoid
    simpa [occurrenceCoordinatedRibbonClauseStub, translatePolyline_add,
      planar, firstData, secondData, firstClauseIndex, secondClauseIndex,
      firstGroup, secondGroup, firstLane, secondLane,
      firstCenter, secondCenter,
      add_comm, add_left_comm, add_assoc] using translatedAvoid

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
