import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedAnchorReindexing
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierClauseOrbits

/-!
# Retained membership witnesses for translated planar-SAT sources

The common-shift reindexing bridge reduces periodic planarity to finding a
retained source for a translated local component.  Four source families can
reuse their literal period translate once the translated geometric object is
known to be retained.  Routed-variable arms need one extra flexibility: the
same translated link can acquire a different index in the target site's
finite enumeration.

This module packages those constructor-level facts, leaving later geometric
orbit arguments to prove only the corresponding retained-object membership.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Period translation does not change the duplicator arm selected by an
external planar-SAT node. -/
@[simp]
theorem PlanarSATNode.duplicatorArm_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (node : PlanarSATNode Variable) (shift : Cell) :
    (node.periodTranslate
      (PeriodicCNF.incidenceGraph formula) shift).duplicatorArm =
      node.duplicatorArm := by
  cases node with
  | carrier node =>
      cases node with
      | boundary boundary =>
          rfl
      | terminal terminal =>
          rfl
  | atom site =>
      rfl

/-- Common period translation preserves inequality of the two segment
occurrence keys stored by a crossing record. -/
theorem CrossingRecord.occurrenceKeys_ne_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (record : CrossingRecord) (shift : Cell)
    (different :
      PeriodicGridDrawing.SegmentOccurrenceKey
          record.first record.firstTranslate ≠
        PeriodicGridDrawing.SegmentOccurrenceKey
          record.second record.secondTranslate) :
    PeriodicGridDrawing.SegmentOccurrenceKey
        (record.periodTranslate graph shift).first
        (record.periodTranslate graph shift).firstTranslate ≠
      PeriodicGridDrawing.SegmentOccurrenceKey
        (record.periodTranslate graph shift).second
        (record.periodTranslate graph shift).secondTranslate := by
  intro translatedEqual
  apply different
  simp only [CrossingRecord.periodTranslate,
    PeriodicGridDrawing.SegmentOccurrenceKey,
    Prod.mk.injEq] at translatedEqual ⊢
  exact
    ⟨translatedEqual.1, translatedEqual.2.1,
      Cell.add_right_injective shift translatedEqual.2.2⟩

/-- A crossing in the neighboring halo remains in that halo after a common
period translation whenever both translated segment occurrences are still
neighboring. -/
theorem CrossingRecord.periodTranslate_mem_orientedCrossingHalo_of_neighbors
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (record : CrossingRecord)
    (recordMember : record ∈ orientedCrossingHalo graph)
    (shift : Cell)
    (firstTranslatedNeighbor :
      IsNeighborTranslation
        (Cell.add record.firstTranslate shift))
    (secondTranslatedNeighbor :
      IsNeighborTranslation
        (Cell.add record.secondTranslate shift)) :
    record.periodTranslate graph shift ∈
      orientedCrossingHalo graph := by
  let target := record.periodTranslate graph shift
  let offset := (drawing graph).periodTranslation shift
  rcases orientedCrossingHalo_sound graph recordMember with
    ⟨sourceFirstMember, sourceSecondMember,
      _sourceFirstNeighbor, _sourceSecondNeighbor,
      sourceDifferent, sourceFirstHorizontal,
      sourceSecondVertical, sourceProper⟩
  have targetFirstMember :
      (target.first, target.firstTranslate) ∈
        neighborOccurrences graph :=
    (mem_neighborOccurrences_iff graph _).mpr
      ⟨by simpa only [target, CrossingRecord.periodTranslate] using
          sourceFirstMember,
        by simpa only [target, CrossingRecord.periodTranslate] using
          firstTranslatedNeighbor⟩
  have targetSecondMember :
      (target.second, target.secondTranslate) ∈
        neighborOccurrences graph :=
    (mem_neighborOccurrences_iff graph _).mpr
      ⟨by simpa only [target, CrossingRecord.periodTranslate] using
          sourceSecondMember,
        by simpa only [target, CrossingRecord.periodTranslate] using
          secondTranslatedNeighbor⟩
  have targetFirstContains :
      (target.firstSegment graph).InteriorContains target.point := by
    rw [show target.firstSegment graph =
        (record.firstSegment graph).translate offset by
      exact CrossingRecord.firstSegment_periodTranslate
        graph record shift]
    change
      (record.firstSegment graph).translate offset
          |>.InteriorContains (Cell.add record.point offset)
    exact
      (PeriodicGridDrawing.interiorContains_translate_iff
        (record.firstSegment graph) offset record.point).mpr
          sourceProper.1
  have targetSecondContains :
      (target.secondSegment graph).InteriorContains target.point := by
    rw [show target.secondSegment graph =
        (record.secondSegment graph).translate offset by
      exact CrossingRecord.secondSegment_periodTranslate
        graph record shift]
    change
      (record.secondSegment graph).translate offset
          |>.InteriorContains (Cell.add record.point offset)
    exact
      (PeriodicGridDrawing.interiorContains_translate_iff
        (record.secondSegment graph) offset record.point).mpr
          sourceProper.2.1
  have targetFirstHorizontal :
      (target.firstSegment graph).IsHorizontal := by
    rw [show target.firstSegment graph =
        (record.firstSegment graph).translate offset by
      exact CrossingRecord.firstSegment_periodTranslate
        graph record shift]
    exact (GridSegment.isHorizontal_translate _ _).mpr
      sourceFirstHorizontal
  have targetSecondVertical :
      (target.secondSegment graph).IsVertical := by
    rw [show target.secondSegment graph =
        (record.secondSegment graph).translate offset by
      exact CrossingRecord.secondSegment_periodTranslate
        graph record shift]
    exact (GridSegment.isVertical_translate _ _).mpr
      sourceSecondVertical
  have targetPointEq :
      target.point =
        orientedIntersectionPoint
          (target.firstSegment graph)
          (target.secondSegment graph) :=
    (orientedIntersectionPoint_eq
      targetFirstHorizontal targetSecondVertical
      targetFirstContains targetSecondContains).symm
  apply (mem_orientedCrossingHalo_iff graph target).mpr
  exact
    ⟨targetFirstMember, targetSecondMember, targetPointEq,
      record.occurrenceKeys_ne_periodTranslate shift
          sourceDifferent,
        targetFirstHorizontal, targetSecondVertical,
        targetFirstContains, targetSecondContains,
        Or.inl ⟨targetFirstHorizontal, targetSecondVertical⟩⟩

/-- A metadata-rich route occurrence remains in the represented drawing
block whenever its translated occurrence coordinate is still neighboring. -/
theorem CNFRouteOccurrence.periodTranslate_mem_drawing_of_neighbor
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (occurrence : CNFRouteOccurrence Variable)
    (occurrenceMember :
      occurrence ∈ drawingCNFRouteOccurrences formula)
    (shift : Cell)
    (translatedNeighbor :
      IsNeighborTranslation
        (Cell.add occurrence.translate shift)) :
    occurrence.periodTranslate shift ∈
      drawingCNFRouteOccurrences formula := by
  rcases List.mem_flatMap.mp occurrenceMember with
    ⟨taggedIncidence, taggedIncidenceMember, occurrenceMember⟩
  rcases List.mem_map.mp occurrenceMember with
    ⟨sourceTranslate, sourceTranslateMember, occurrenceEq⟩
  subst occurrence
  apply List.mem_flatMap.mpr
  refine ⟨taggedIncidence, taggedIncidenceMember, ?_⟩
  apply List.mem_map.mpr
  refine
    ⟨Cell.add sourceTranslate shift,
      (mem_neighborTranslations_iff _).mpr translatedNeighbor, rfl⟩

/-- Translating the occurrence coordinate in a bend enumeration translates
every bend record in place. -/
theorem routeBendsAux_periodTranslate
    (routeIndex incomingSegmentIndex : Nat)
    (translate shift : Cell) :
    ∀ points : List Cell,
      routeBendsAux routeIndex (Cell.add translate shift)
          incomingSegmentIndex points =
        (routeBendsAux routeIndex translate
          incomingSegmentIndex points).map
            (fun routeBend => routeBend.periodTranslate shift) := by
  intro points
  induction points generalizing incomingSegmentIndex with
  | nil =>
      rfl
  | cons first rest induction =>
      cases rest with
      | nil =>
          rfl
      | cons second rest =>
          cases rest with
          | nil =>
              rfl
          | cons third rest =>
              simp only [routeBendsAux, List.map_cons,
                RouteBend.periodTranslate]
              congr 1
              simpa only [RouteBend.periodTranslate] using
                induction (incomingSegmentIndex + 1)

/-- The corresponding covariance statement for the complete bend list of
one route occurrence. -/
theorem routeBends_periodTranslate
    (routeIndex : Nat) (translate shift : Cell)
    (route : List Cell) :
    routeBends routeIndex (Cell.add translate shift) route =
      (routeBends routeIndex translate route).map
        (fun routeBend => routeBend.periodTranslate shift) := by
  exact routeBendsAux_periodTranslate
    routeIndex 0 translate shift route

/-- A listed bend remains listed whenever its translated route occurrence is
still one of the nine neighboring occurrences. -/
theorem RouteBend.periodTranslate_mem_drawing_of_neighbor
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (routeBend : RouteBend)
    (routeBendMember : routeBend ∈ drawingRouteBends graph)
    (shift : Cell)
    (translatedNeighbor :
      IsNeighborTranslation
        (Cell.add routeBend.translate shift)) :
    routeBend.periodTranslate shift ∈ drawingRouteBends graph := by
  rcases List.mem_flatMap.mp routeBendMember with
    ⟨taggedRoute, taggedRouteMember, routeBendMember⟩
  rcases List.mem_flatMap.mp routeBendMember with
    ⟨sourceTranslate, sourceTranslateMember, routeBendMember⟩
  have sourceTranslateEq :
      routeBend.translate = sourceTranslate :=
    (routeBendsAux_member_data
      taggedRoute.2 sourceTranslate taggedRoute.1 0
      routeBendMember).2.1
  apply List.mem_flatMap.mpr
  refine ⟨taggedRoute, taggedRouteMember, ?_⟩
  apply List.mem_flatMap.mpr
  refine
    ⟨Cell.add sourceTranslate shift,
      (mem_neighborTranslations_iff _).mpr
        (by simpa only [sourceTranslateEq] using translatedNeighbor),
      ?_⟩
  rw [routeBends_periodTranslate]
  exact List.mem_map.mpr
    ⟨routeBend, routeBendMember, rfl⟩

/-- A represented routed-clause site remains represented whenever its
translated site coordinate is neighboring. -/
theorem clauseRouteSitePeriodTranslate_mem_drawing_of_neighbor
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (site : ClauseRouteSite)
    (siteMember : site ∈ drawingClauseRouteSites formula)
    (shift : Cell)
    (translatedNeighbor :
      IsNeighborTranslation (Cell.add site.2 shift)) :
    clauseRouteSitePeriodTranslate site shift ∈
      drawingClauseRouteSites formula := by
  rcases List.mem_flatMap.mp siteMember with
    ⟨taggedClause, taggedClauseMember, siteMember⟩
  rcases List.mem_map.mp siteMember with
    ⟨sourceTranslate, sourceTranslateMember, siteEq⟩
  subst site
  apply List.mem_flatMap.mpr
  refine ⟨taggedClause, taggedClauseMember, ?_⟩
  apply List.mem_map.mpr
  refine
    ⟨Cell.add sourceTranslate shift,
      (mem_neighborTranslations_iff _).mpr
        translatedNeighbor,
      rfl⟩

/-- A translated metadata-rich route occurrence witnesses membership of its
translated routed-variable site. -/
theorem variableRouteSitePeriodTranslate_mem_drawing_of_occurrence
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (site : VariableRouteSite Variable)
    (occurrence : CNFRouteOccurrence Variable)
    (occurrenceMember :
      occurrence ∈ drawingCNFRouteOccurrences formula)
    (siteEq : occurrence.variableOccurrence = site)
    (shift : Cell)
    (translatedNeighbor :
      IsNeighborTranslation
        (Cell.add occurrence.translate shift)) :
    variableRouteSitePeriodTranslate site shift ∈
      drawingVariableRouteSites formula := by
  rw [drawingVariableRouteSites, List.mem_dedup]
  apply List.mem_map.mpr
  refine
    ⟨occurrence.periodTranslate shift,
      occurrence.periodTranslate_mem_drawing_of_neighbor
        occurrenceMember shift translatedNeighbor, ?_⟩
  rw [← siteEq]
  rcases occurrence with ⟨incidence, edgeIndex, translate⟩
  rcases translate with ⟨translateX, translateY⟩
  rcases shift with ⟨shiftX, shiftY⟩
  simp [CNFRouteOccurrence.variableOccurrence,
    CNFRouteOccurrence.periodTranslate, CNFRouteOccurrence.edge,
    variableRouteSitePeriodTranslate, Cell.add]
  constructor <;> ring

/-- A translated crossover source is retained as soon as its translated
crossing record belongs to the retained crossing halo. -/
theorem crossoverSource_periodTranslate_retainedComponentMember
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (crossing : CrossingRecord)
    (localClauseIndex : Nat)
    (shift : Cell)
    (translatedCrossingMember :
      crossing.periodTranslate
          (PeriodicCNF.incidenceGraph formula) shift ∈
        orientedCrossingHalo
          (PeriodicCNF.incidenceGraph formula)) :
    ((DrawingPlanarSATClauseSource.crossover
        crossing localClauseIndex).periodTranslate
      formula shift).RetainedComponentMember formula := by
  exact translatedCrossingMember

/-- A translated selected carrier source is retained as soon as the exact
translated link remains one of the selected retained links. -/
theorem carrierSource_periodTranslate_retainedComponentMember
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode)
    (localClauseIndex : Nat)
    (shift : Cell)
    (translatedLinkMember :
      carrierLinkPeriodTranslate
          (PeriodicCNF.incidenceGraph formula) link shift ∈
        retainedDrawingCompleteCarrierLinks
          (PeriodicCNF.incidenceGraph formula)) :
    ((DrawingPlanarSATClauseSource.carrier
        link localClauseIndex).periodTranslate
      formula shift).RetainedComponentMember formula := by
  exact translatedLinkMember

/-- A translated bend source is retained as soon as the translated bend is
present in the deduplicated neighboring bend family. -/
theorem bendSource_periodTranslate_retainedComponentMember
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (routeBend : RouteBend)
    (localClauseIndex : Nat)
    (shift : Cell)
    (translatedBendMember :
      routeBend.periodTranslate shift ∈
        (drawingRouteBends
          (PeriodicCNF.incidenceGraph formula)).dedup) :
    ((DrawingPlanarSATClauseSource.bend
        routeBend localClauseIndex).periodTranslate
      formula shift).RetainedComponentMember formula := by
  exact translatedBendMember

/-- A translated routed-clause source is retained as soon as its translated
clause site belongs to the neighboring site family. -/
theorem routedClauseSource_periodTranslate_retainedComponentMember
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : ClauseRouteSite)
    (shift : Cell)
    (translatedSiteMember :
      clauseRouteSitePeriodTranslate site shift ∈
        drawingClauseRouteSites formula) :
    ((DrawingPlanarSATClauseSource.routedClause site).periodTranslate
      formula shift).RetainedComponentMember formula := by
  exact translatedSiteMember

/-- The crossover family is closed under any common translation that leaves
both underlying segment occurrences in the neighboring block. -/
theorem crossoverSource_periodTranslate_retainedComponentMember_of_neighbors
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (crossing : CrossingRecord)
    (localClauseIndex : Nat)
    (sourceMember :
      (DrawingPlanarSATClauseSource.crossover
        crossing localClauseIndex).RetainedComponentMember formula)
    (shift : Cell)
    (firstTranslatedNeighbor :
      IsNeighborTranslation
        (Cell.add crossing.firstTranslate shift))
    (secondTranslatedNeighbor :
      IsNeighborTranslation
        (Cell.add crossing.secondTranslate shift)) :
    ((DrawingPlanarSATClauseSource.crossover
        crossing localClauseIndex).periodTranslate
      formula shift).RetainedComponentMember formula := by
  apply crossoverSource_periodTranslate_retainedComponentMember
  exact crossing.periodTranslate_mem_orientedCrossingHalo_of_neighbors
    sourceMember shift firstTranslatedNeighbor secondTranslatedNeighbor

/-- The bend family is closed under translations that keep the bend's route
occurrence in the neighboring block. -/
theorem bendSource_periodTranslate_retainedComponentMember_of_neighbor
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (routeBend : RouteBend)
    (localClauseIndex : Nat)
    (sourceMember :
      (DrawingPlanarSATClauseSource.bend
        routeBend localClauseIndex).RetainedComponentMember formula)
    (shift : Cell)
    (translatedNeighbor :
      IsNeighborTranslation
        (Cell.add routeBend.translate shift)) :
    ((DrawingPlanarSATClauseSource.bend
        routeBend localClauseIndex).periodTranslate
      formula shift).RetainedComponentMember formula := by
  apply bendSource_periodTranslate_retainedComponentMember
  rw [List.mem_dedup]
  exact routeBend.periodTranslate_mem_drawing_of_neighbor
    (List.mem_dedup.mp sourceMember) shift translatedNeighbor

/-- The routed-clause family is closed under translations that keep its
clause occurrence in the neighboring block. -/
theorem routedClauseSource_periodTranslate_retainedComponentMember_of_neighbor
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : ClauseRouteSite)
    (sourceMember :
      (DrawingPlanarSATClauseSource.routedClause site)
        |>.RetainedComponentMember formula)
    (shift : Cell)
    (translatedNeighbor :
      IsNeighborTranslation (Cell.add site.2 shift)) :
    ((DrawingPlanarSATClauseSource.routedClause site).periodTranslate
      formula shift).RetainedComponentMember formula := by
  apply routedClauseSource_periodTranslate_retainedComponentMember
  exact clauseRouteSitePeriodTranslate_mem_drawing_of_neighbor
    site sourceMember shift translatedNeighbor

/-- For a routed-variable arm, an exact translated link at any target
presentation index gives a retained source with the translated component and
the original local clause index. -/
theorem exists_retainedTargetSource_routedVariable_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (armIndex : Nat)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable))
    (localClauseIndex : Nat)
    (shift : Cell)
    (sourceArmEq : arm = link.first.duplicatorArm)
    (translatedSiteMember :
      variableRouteSitePeriodTranslate site shift ∈
        drawingVariableRouteSites formula)
    (targetArmIndex : Nat)
    (translatedLinkMember :
      (planarSATNodeLinkPeriodTranslate
          (PeriodicCNF.incidenceGraph formula) link shift,
        targetArmIndex) ∈
        (routedVariableLinksAt formula
          (variableRouteSitePeriodTranslate site shift)).zipIdx) :
    ∃ targetSource : DrawingPlanarSATClauseSource Variable,
      targetSource.RetainedComponentMember formula ∧
        targetSource.component =
          ((DrawingPlanarSATClauseSource.routedVariable
              site armIndex arm link localClauseIndex).periodTranslate
            formula shift).component ∧
        targetSource.localClauseIndex = localClauseIndex := by
  let targetLink :=
    planarSATNodeLinkPeriodTranslate
      (PeriodicCNF.incidenceGraph formula) link shift
  let targetSource : DrawingPlanarSATClauseSource Variable :=
    .routedVariable
      (variableRouteSitePeriodTranslate site shift)
      targetArmIndex arm targetLink localClauseIndex
  refine ⟨targetSource, ?_, rfl, rfl⟩
  exact
    ⟨translatedSiteMember, translatedLinkMember, by
      simpa only [targetLink,
        planarSATNodeLinkPeriodTranslate,
        PlanarSATNode.duplicatorArm_periodTranslate] using
          sourceArmEq⟩

end PeriodicOrthocrossing
end LeanTrominoes
