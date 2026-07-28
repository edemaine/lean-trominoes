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
