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

/-- The target terminal of a metadata-rich route occurrence translates
without changing its indexed segment or endpoint. -/
@[simp]
theorem CNFRouteOccurrence.targetTerminal_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrence : CNFRouteOccurrence Variable) (shift : Cell) :
    (occurrence.periodTranslate shift).targetTerminal formula =
      (occurrence.targetTerminal formula).periodTranslate shift := by
  rfl

/-- Translating a metadata-rich route occurrence translates its lifted
variable endpoint site by the same drawing-period shift. -/
@[simp]
theorem CNFRouteOccurrence.variableOccurrence_periodTranslate
    {Variable : Type*}
    (occurrence : CNFRouteOccurrence Variable) (shift : Cell) :
    (occurrence.periodTranslate shift).variableOccurrence =
      variableRouteSitePeriodTranslate
        occurrence.variableOccurrence shift := by
  rcases occurrence with ⟨incidence, edgeIndex, translate⟩
  rcases translate with ⟨translateX, translateY⟩
  rcases shift with ⟨shiftX, shiftY⟩
  simp [CNFRouteOccurrence.variableOccurrence,
    CNFRouteOccurrence.periodTranslate, CNFRouteOccurrence.edge,
    variableRouteSitePeriodTranslate, Cell.add]
  constructor <;> ring

/-- Translating a routed-variable site translates the two clause positions
of each fixed duplicator arm by the refined drawing period. -/
theorem routedVariableEqualityPositions_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (arm : DuplicatorArm) (shift : Cell) :
    routedVariableEqualityPositions formula
        (variableRouteSitePeriodTranslate site shift) arm =
      EqualityPositions.periodTranslate
        (routedVariableEqualityPositions formula site arm)
        (carrierMacroPeriodTranslation
          (PeriodicCNF.incidenceGraph formula) shift) := by
  cases arm <;>
    simp [routedVariableEqualityPositions,
      EqualityPositions.periodTranslate,
      routedVariableOrigin_periodTranslate,
      duplicatorArmEqualityPositions,
      Cell.add] <;>
    constructor <;> constructor <;> ring

/-- A graph degree bound recovers the source formula's variable-occurrence
bound. -/
theorem occurrencesAtMost_of_incidenceGraph_degreeAtMost
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {bound : Nat}
    (degree : formula.incidenceGraph.DegreeAtMost bound) :
    formula.OccurrencesAtMost bound := by
  intro atom
  rw [← PeriodicCNF.incidenceGraph_variable_degree]
  exact degree (.variable atom)

/-- Every active routed-variable link exposes the metadata-rich route
occurrence that supplies its first terminal endpoint. -/
theorem exists_routeOccurrence_of_routedVariableLinkMember
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    {link : EqualityLink (PlanarSATNode Variable)}
    {armIndex : Nat}
    (linkMember :
      (link, armIndex) ∈
        (routedVariableLinksAt formula site).zipIdx) :
    ∃ occurrence ∈ variableRouteOccurrencesAt formula site,
      link.first =
        .carrier (.terminal
          (occurrence.targetTerminal formula)) := by
  have rawLinkMember :
      link ∈ routedVariableLinksAt formula site :=
    List.fst_mem_of_mem_zipIdx linkMember
  rcases List.mem_map.mp rawLinkMember with
    ⟨taggedNode, taggedNodeMember, linkEq⟩
  have nodeMember :
      taggedNode.1 ∈ routedVariableNodes formula site :=
    List.mem_of_mem_take
      (List.fst_mem_of_mem_zipIdx taggedNodeMember)
  rcases
      (mem_routedVariableNodes_iff
        formula site taggedNode.1).mp nodeMember with
    ⟨occurrence, occurrenceMember, nodeEq⟩
  refine ⟨occurrence, occurrenceMember, ?_⟩
  rw [← linkEq]
  exact nodeEq

/-- Membership determines all fields of a routed-variable link from its first
endpoint and site. -/
theorem routedVariableLink_eq_of_member
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    {link : EqualityLink (PlanarSATNode Variable)}
    (linkMember : link ∈ routedVariableLinksAt formula site) :
    link =
      ⟨link.first, .atom site,
        routedVariableEqualityPositions formula site
          link.first.duplicatorArm⟩ := by
  rcases List.mem_map.mp linkMember with
    ⟨taggedNode, taggedNodeMember, linkEq⟩
  rw [← linkEq]

/-- At a degree-at-most-three site, every listed routed-variable node occurs
among the three active links, at some finite presentation index. -/
theorem exists_routedVariableLinkIndex_of_nodeMember
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrences : formula.OccurrencesAtMost 3)
    (site : VariableRouteSite Variable)
    (node : PlanarSATNode Variable)
    (nodeMember : node ∈ routedVariableNodes formula site) :
    ∃ armIndex : Nat,
      ((⟨node, .atom site,
          routedVariableEqualityPositions formula site
            node.duplicatorArm⟩ :
          EqualityLink (PlanarSATNode Variable)),
        armIndex) ∈
        (routedVariableLinksAt formula site).zipIdx := by
  have nodesLengthLe :
      (routedVariableNodes formula site).length ≤ 3 := by
    calc
      (routedVariableNodes formula site).length ≤
          ((variableRouteOccurrencesAt formula site).map fun occurrence =>
            (PlanarSATNode.carrier
              (.terminal (occurrence.targetTerminal formula)) :
              PlanarSATNode Variable)).length :=
        List.Sublist.length_le (List.dedup_sublist _)
      _ ≤ 3 := by
        simpa using
          variableRouteOccurrencesAt_length_le_three
            formula occurrences site
  have nodeTakeMember :
      node ∈ (routedVariableNodes formula site).take 3 := by
    rw [List.take_of_length_le nodesLengthLe]
    exact nodeMember
  rcases List.mem_iff_getElem.mp nodeTakeMember with
    ⟨armIndex, armIndexLt, nodeLookup⟩
  have taggedNodeMember :
      (node, armIndex) ∈
        ((routedVariableNodes formula site).take 3).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff]
    exact ⟨armIndexLt, nodeLookup⟩
  have doubleTaggedNodeMember :
      ((node, armIndex), armIndex) ∈
        ((routedVariableNodes formula site).take 3).zipIdx.zipIdx := by
    apply (List.mem_zipIdx_iff_getElem?).mpr
    have lookup :=
      (List.mem_zipIdx_iff_getElem?).mp taggedNodeMember
    simp [List.getElem?_zipIdx, lookup]
  refine ⟨armIndex, ?_⟩
  unfold routedVariableLinksAt
  rw [List.zipIdx_map]
  apply List.mem_map.mpr
  exact
    ⟨((node, armIndex), armIndex),
      doubleTaggedNodeMember, rfl⟩

/-- Translating the route occurrence behind an active routed-variable link
puts the exact translated link into the translated site's active family,
possibly at a different finite presentation index. -/
theorem exists_routedVariableLinkIndex_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (degree :
      formula.incidenceGraph.DegreeAtMost 3)
    (site : VariableRouteSite Variable)
    (link : EqualityLink (PlanarSATNode Variable))
    (armIndex : Nat)
    (linkMember :
      (link, armIndex) ∈
        (routedVariableLinksAt formula site).zipIdx)
    (occurrence : CNFRouteOccurrence Variable)
    (occurrenceMember :
      occurrence ∈ variableRouteOccurrencesAt formula site)
    (linkFirstEq :
      link.first =
        .carrier (.terminal
          (occurrence.targetTerminal formula)))
    (shift : Cell)
    (translatedNeighbor :
      IsNeighborTranslation
        (Cell.add occurrence.translate shift)) :
    ∃ targetArmIndex : Nat,
      (planarSATNodeLinkPeriodTranslate
          formula.incidenceGraph link shift,
        targetArmIndex) ∈
          (routedVariableLinksAt formula
            (variableRouteSitePeriodTranslate site shift)).zipIdx := by
  let targetSite :=
    variableRouteSitePeriodTranslate site shift
  let targetOccurrence := occurrence.periodTranslate shift
  let targetNode : PlanarSATNode Variable :=
    .carrier (.terminal
      (targetOccurrence.targetTerminal formula))
  have occurrenceData :=
    variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula site occurrenceMember
  have targetOccurrenceMember :
      targetOccurrence ∈ drawingCNFRouteOccurrences formula :=
    occurrence.periodTranslate_mem_drawing_of_neighbor
      occurrenceData.1 shift translatedNeighbor
  have targetOccurrenceSiteEq :
      targetOccurrence.variableOccurrence = targetSite := by
    simpa only [targetOccurrence, targetSite,
        CNFRouteOccurrence.variableOccurrence_periodTranslate] using
      congrArg
        (fun sourceSite =>
          variableRouteSitePeriodTranslate sourceSite shift)
        occurrenceData.2
  have targetOccurrenceAtMember :
      targetOccurrence ∈
        variableRouteOccurrencesAt formula targetSite := by
    simp [variableRouteOccurrencesAt,
      targetOccurrenceMember, targetOccurrenceSiteEq]
  have targetNodeMember :
      targetNode ∈ routedVariableNodes formula targetSite := by
    apply (mem_routedVariableNodes_iff
      formula targetSite targetNode).mpr
    exact
      ⟨targetOccurrence, targetOccurrenceAtMember, rfl⟩
  rcases exists_routedVariableLinkIndex_of_nodeMember
      formula
      (occurrencesAtMost_of_incidenceGraph_degreeAtMost degree)
      targetSite targetNode targetNodeMember with
    ⟨targetArmIndex, targetLinkMember⟩
  refine ⟨targetArmIndex, ?_⟩
  have sourceLinkEq :
      link =
        ⟨link.first, .atom site,
          routedVariableEqualityPositions formula site
            link.first.duplicatorArm⟩ :=
    routedVariableLink_eq_of_member
      formula site (List.fst_mem_of_mem_zipIdx linkMember)
  have targetNodeEq :
      targetNode =
        link.first.periodTranslate formula.incidenceGraph shift := by
    rw [linkFirstEq]
    rfl
  have targetLinkEq :
      (⟨targetNode, .atom targetSite,
          routedVariableEqualityPositions formula targetSite
            targetNode.duplicatorArm⟩ :
        EqualityLink (PlanarSATNode Variable)) =
        planarSATNodeLinkPeriodTranslate
          formula.incidenceGraph link shift := by
    rw [sourceLinkEq]
    unfold planarSATNodeLinkPeriodTranslate
    rw [targetNodeEq]
    dsimp only [targetSite]
    rw [PlanarSATNode.duplicatorArm_periodTranslate,
      routedVariableEqualityPositions_periodTranslate]
    rfl
  rw [← targetLinkEq]
  exact targetLinkMember

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

/-- A retained routed-variable source has a retained translated
representative whenever the route occurrence supplying its first endpoint
stays in the neighboring block.  The representative may use the target
site's new finite presentation index. -/
theorem
    exists_retainedTargetSource_routedVariable_periodTranslate_of_neighbor
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (degree :
      formula.incidenceGraph.DegreeAtMost 3)
    (site : VariableRouteSite Variable)
    (armIndex : Nat)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable))
    (localClauseIndex : Nat)
    (sourceMember :
      (DrawingPlanarSATClauseSource.routedVariable
        site armIndex arm link localClauseIndex)
        |>.RetainedComponentMember formula)
    (occurrence : CNFRouteOccurrence Variable)
    (occurrenceMember :
      occurrence ∈ variableRouteOccurrencesAt formula site)
    (linkFirstEq :
      link.first =
        .carrier (.terminal
          (occurrence.targetTerminal formula)))
    (shift : Cell)
    (translatedNeighbor :
      IsNeighborTranslation
        (Cell.add occurrence.translate shift)) :
    ∃ targetSource : DrawingPlanarSATClauseSource Variable,
      targetSource.RetainedComponentMember formula ∧
        targetSource.component =
          ((DrawingPlanarSATClauseSource.routedVariable
              site armIndex arm link localClauseIndex).periodTranslate
            formula shift).component ∧
        targetSource.localClauseIndex = localClauseIndex := by
  have occurrenceData :=
    variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula site occurrenceMember
  have translatedSiteMember :
      variableRouteSitePeriodTranslate site shift ∈
        drawingVariableRouteSites formula :=
    variableRouteSitePeriodTranslate_mem_drawing_of_occurrence
      site occurrence occurrenceData.1 occurrenceData.2
      shift translatedNeighbor
  rcases exists_routedVariableLinkIndex_periodTranslate
      formula degree site link armIndex sourceMember.2.1
      occurrence occurrenceMember linkFirstEq shift
      translatedNeighbor with
    ⟨targetArmIndex, translatedLinkMember⟩
  exact exists_retainedTargetSource_routedVariable_periodTranslate
    formula site armIndex arm link localClauseIndex shift
    sourceMember.2.2 translatedSiteMember
    targetArmIndex translatedLinkMember

/-- Family-specific sufficient data for realizing a physical source
translation inside the retained finite component family.  Carrier links are
the exceptional family: because only one orbit representative is retained,
their condition records exact selected-link membership rather than a
neighboring-window bound. -/
def DrawingPlanarSATClauseSource.RetainedOrbitCondition
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (shift : Cell) : Prop :=
  let graph := PeriodicCNF.incidenceGraph formula
  match source with
  | .crossover crossing _ =>
      IsNeighborTranslation
          (Cell.add crossing.firstTranslate shift) ∧
        IsNeighborTranslation
          (Cell.add crossing.secondTranslate shift)
  | .carrier link _ =>
      carrierLinkPeriodTranslate graph link shift ∈
        retainedDrawingCompleteCarrierLinks graph
  | .bend routeBend _ =>
      IsNeighborTranslation
        (Cell.add routeBend.translate shift)
  | .routedClause site =>
      IsNeighborTranslation (Cell.add site.2 shift)
  | .routedVariable site _ _ link _ =>
      ∃ occurrence ∈ variableRouteOccurrencesAt formula site,
        link.first =
            .carrier (.terminal
              (occurrence.targetTerminal formula)) ∧
          IsNeighborTranslation
            (Cell.add occurrence.translate shift)

/-- The family-specific orbit condition always supplies a retained source
with the exact translated component and unchanged local clause index.
Enumeration-only fields, notably a routed-variable arm index, may change. -/
theorem DrawingPlanarSATClauseSource.exists_retainedTarget_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (degree :
      formula.incidenceGraph.DegreeAtMost 3)
    (source : DrawingPlanarSATClauseSource Variable)
    (sourceMember : source.RetainedComponentMember formula)
    (shift : Cell)
    (condition :
      source.RetainedOrbitCondition formula shift) :
    ∃ targetSource : DrawingPlanarSATClauseSource Variable,
      targetSource.RetainedComponentMember formula ∧
        targetSource.component =
          (source.periodTranslate formula shift).component ∧
        targetSource.localClauseIndex =
          source.localClauseIndex := by
  cases source with
  | crossover crossing localClauseIndex =>
      refine
        ⟨.crossover
            (crossing.periodTranslate formula.incidenceGraph shift)
            localClauseIndex,
          ?_, rfl, rfl⟩
      exact
        crossoverSource_periodTranslate_retainedComponentMember_of_neighbors
          formula crossing localClauseIndex sourceMember shift
          condition.1 condition.2
  | carrier link localClauseIndex =>
      exact
        ⟨.carrier
            (carrierLinkPeriodTranslate
              formula.incidenceGraph link shift)
            localClauseIndex,
          condition, rfl, rfl⟩
  | bend routeBend localClauseIndex =>
      refine
        ⟨.bend (routeBend.periodTranslate shift)
            localClauseIndex,
          ?_, rfl, rfl⟩
      exact
        bendSource_periodTranslate_retainedComponentMember_of_neighbor
          formula routeBend localClauseIndex sourceMember shift
          condition
  | routedClause site =>
      refine
        ⟨.routedClause
            (clauseRouteSitePeriodTranslate site shift),
          ?_, rfl, rfl⟩
      exact
        routedClauseSource_periodTranslate_retainedComponentMember_of_neighbor
          formula site sourceMember shift condition
  | routedVariable site armIndex arm link localClauseIndex =>
      rcases condition with
        ⟨occurrence, occurrenceMember,
          linkFirstEq, translatedNeighbor⟩
      exact
        exists_retainedTargetSource_routedVariable_periodTranslate_of_neighbor
          formula degree site armIndex arm link localClauseIndex
          sourceMember occurrence occurrenceMember linkFirstEq
          shift translatedNeighbor

end PeriodicOrthocrossing
end LeanTrominoes
