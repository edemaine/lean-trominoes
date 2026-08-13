/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossoverIncidenceDrawing
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierPortGeometry
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATVariableGauge
import LeanTrominoes.PeriodicOrthocrossingRoutedClauseIncidenceDrawing
import LeanTrominoes.RetainedOccurrenceTerminalVectorDistinctness

/-!
# Incidence-key distinctness of the retained planar SAT source

The terminal-vector separation argument needs each periodic clause to list
every physical incidence `(atom, offset)` at most once.  This is weaker than
requiring distinct atoms: a legitimate periodic equality can connect two
different translates of one protovariable.

This file first proves ordinary variable distinctness inside every finite
embedded clause of the retained planar-SAT block.  It then transports that
fact through periodicization, opaque wrapping, variable gauging, clause
anchor normalization, and clause-orbit deduplication.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 2000000

private theorem nodup_of_map_nodup
    {Source Target : Type*} [DecidableEq Source]
    (map : Source → Target) (values : List Source)
    (mappedNodup : (values.map map).Nodup) :
    values.Nodup := by
  induction values with
  | nil =>
      simp
  | cons value values induction =>
      simp only [List.map_cons, List.nodup_cons]
        at mappedNodup ⊢
      constructor
      · intro member
        apply mappedNodup.1
        exact List.mem_map.mpr ⟨value, member, rfl⟩
      · exact induction mappedNodup.2

private theorem EmbeddedClause.atomsNodup_map
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    (variableMap : Source → Target)
    (injective : Function.Injective variableMap)
    (positionMap : Cell → Cell)
    {clause : EmbeddedClause Source}
    (distinct : clause.AtomsNodup) :
    (clause.map variableMap positionMap).AtomsNodup := by
  unfold EmbeddedClause.AtomsNodup at distinct ⊢
  rw [EmbeddedClause.map, List.map_map]
  simpa [Function.comp_def] using distinct.map injective

private theorem equalityFamily_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (links : List (EqualityLink Variable))
    (endpointsDifferent :
      ∀ link ∈ links, link.first ≠ link.second) :
    ∀ clause ∈ equalityFamily links, clause.AtomsNodup := by
  intro clause clauseMember
  unfold equalityFamily at clauseMember
  rcases List.mem_flatMap.mp clauseMember with
    ⟨link, linkMember, clauseMember⟩
  have different := endpointsDifferent link linkMember
  simp only [equalityInstance, List.mem_cons,
    List.not_mem_nil, or_false] at clauseMember
  rcases clauseMember with rfl | rfl <;>
    simpa [EmbeddedClause.AtomsNodup] using different

private theorem crossoverFormula_allAtomsNodup :
    ∀ clause ∈ crossoverFormula, clause.AtomsNodup := by
  have checked :
      crossoverFormula.all
        (fun clause =>
          decide ((clause.literals.map Prod.fst).Nodup)) = true := by
    native_decide
  intro clause clauseMember
  have clauseChecked :=
    (List.all_eq_true.mp checked) clause clauseMember
  unfold EmbeddedClause.AtomsNodup
  exact of_decide_eq_true clauseChecked

private theorem scopedCarrierCrossoverVariableMap_injective
    (crossing : CrossingRecord) :
    Function.Injective
      (scopedCrossoverVariableMap crossing
        (carrierNodeCrossingPorts crossing)) := by
  intro first second equal
  cases first <;> cases second <;>
    simp_all [scopedCrossoverVariableMap,
      carrierNodeCrossingPorts]

private theorem drawingCarrierNodeCrossoverFormula_allAtomsNodup
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    ∀ clause ∈ drawingCarrierNodeCrossoverFormula graph,
      clause.AtomsNodup := by
  intro clause clauseMember
  unfold drawingCarrierNodeCrossoverFormula
    crossoverFamily at clauseMember
  rcases List.mem_flatMap.mp clauseMember with
    ⟨crossing, _crossingMember, clauseMember⟩
  unfold scopedCrossoverInstance instantiateFormula
    at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨sourceClause, sourceMember, clauseEqual⟩
  subst clause
  have sourceDistinct :=
    crossoverFormula_allAtomsNodup
      sourceClause sourceMember
  have renamedDistinct :=
    EmbeddedClause.atomsNodup_map
      (scopedCrossoverVariableMap crossing
        (carrierNodeCrossingPorts crossing))
      (scopedCarrierCrossoverVariableMap_injective crossing)
      id sourceDistinct
  exact EmbeddedClause.atomsNodup_map
    id Function.injective_id
    (fun position =>
      Cell.add (crossingMacroOrigin crossing)
        (Cell.scale 1 position))
    renamedDistinct

private theorem retainedDrawingRouteWireFormula_allAtomsNodup
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal) :
    ∀ clause ∈ retainedDrawingRouteWireFormula graph,
      clause.AtomsNodup := by
  intro clause clauseMember
  rw [retainedDrawingRouteWireFormula,
    List.mem_append] at clauseMember
  rcases clauseMember with carrierMember | bendMember
  · apply equalityFamily_allAtomsNodup
      (retainedDrawingCompleteCarrierLinks graph)
      (fun link linkMember =>
        retainedDrawingCompleteCarrierLink_endpoints_ne
          wellFormed degree isLocal linkMember)
      clause carrierMember
  · apply equalityFamily_allAtomsNodup
      (drawingRouteBendLinks graph)
      (fun link linkMember => ?_)
      clause bendMember
    rcases List.mem_map.mp linkMember with
      ⟨bend, _bendMember, linkEqual⟩
    subst link
    intro endpointsEqual
    exact RouteBend.incomingTerminal_ne_outgoingTerminal
      bend bend (CarrierNode.terminal.inj endpointsEqual)

private theorem retainedDrawingRoutePlanarCoreFormula_allAtomsNodup
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal) :
    ∀ clause ∈ retainedDrawingRoutePlanarCoreFormula graph,
      clause.AtomsNodup := by
  intro clause clauseMember
  rw [retainedDrawingRoutePlanarCoreFormula,
    List.mem_append] at clauseMember
  rcases clauseMember with crossoverMember | wireMember
  · exact drawingCarrierNodeCrossoverFormula_allAtomsNodup
      graph clause crossoverMember
  · unfold retainedScopedDrawingRouteWireFormula at wireMember
    rcases List.mem_map.mp wireMember with
      ⟨sourceClause, sourceMember, clauseEqual⟩
    subst clause
    apply EmbeddedClause.atomsNodup_map
      (fun node =>
        (Sum.inl node :
          Sum CarrierNode
            (CrossingRecord × CrossoverInternal)))
      Sum.inl_injective
      id
    exact retainedDrawingRouteWireFormula_allAtomsNodup
      wellFormed degree isLocal sourceClause sourceMember

private theorem routedClauseAt_atomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (site : ClauseRouteSite) :
    (routedClauseAt formula site).AtomsNodup := by
  unfold EmbeddedClause.AtomsNodup routedClauseAt
  rw [List.map_map]
  change
    ((clauseRouteOccurrencesAt formula site).map fun occurrence =>
      PlanarSATNode.carrier
        (.terminal (occurrence.sourceTerminal formula))).Nodup
  apply nodup_of_map_nodup
    PlanarSATNode.duplicatorArm
  have mappedArms :
      (((clauseRouteOccurrencesAt formula site).map fun occurrence =>
        (PlanarSATNode.carrier
          (.terminal (occurrence.sourceTerminal formula)) :
            PlanarSATNode Variable)).map
            (@PlanarSATNode.duplicatorArm Variable)) =
        (clauseRouteOccurrencesAt formula site).map
          (sourceOccurrenceArm formula) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro occurrence _occurrenceMember
    exact (sourceOccurrenceArm_eq formula occurrence).symm
  rw [mappedArms]
  exact sourceOccurrenceArms_nodup formula degree site

private theorem drawingRoutedClauseFormula_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (degree : formula.incidenceGraph.DegreeAtMost 3) :
    ∀ clause ∈ drawingRoutedClauseFormula formula,
      clause.AtomsNodup := by
  intro clause clauseMember
  unfold drawingRoutedClauseFormula at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨site, _siteMember, clauseEqual⟩
  subst clause
  exact routedClauseAt_atomsNodup formula degree site

private theorem drawingRoutedVariableFormula_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    ∀ clause ∈ drawingRoutedVariableFormula formula,
      clause.AtomsNodup := by
  intro clause clauseMember
  unfold drawingRoutedVariableFormula at clauseMember
  rcases List.mem_flatMap.mp clauseMember with
    ⟨site, _siteMember, clauseMember⟩
  unfold routedVariableFormulaAt at clauseMember
  apply equalityFamily_allAtomsNodup
      (routedVariableLinksAt formula site)
      (fun link linkMember =>
        routedVariableLink_first_ne_second
          formula site linkMember)
      clause clauseMember

/-- Every finite clause in the retained planar-SAT block has pairwise
distinct finite variables. -/
theorem retainedDrawingPlanarSATFormula_allAtomsNodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal) :
    ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
      clause.AtomsNodup := by
  intro clause clauseMember
  rw [retainedDrawingPlanarSATFormula,
    List.mem_append] at clauseMember
  rcases clauseMember with initialMember | variableMember
  · rw [List.mem_append] at initialMember
    rcases initialMember with coreMember | clauseMember
    · change
        clause ∈
          (retainedDrawingRoutePlanarCoreFormula
            formula.incidenceGraph).map fun sourceClause =>
              sourceClause.rename planarSATCoreVariableMap
        at coreMember
      rcases List.mem_map.mp coreMember with
        ⟨sourceClause, sourceMember, clauseEqual⟩
      subst clause
      apply EmbeddedClause.atomsNodup_map
        planarSATCoreVariableMap
        planarSATCoreVariableMap_injective
        id
      exact retainedDrawingRoutePlanarCoreFormula_allAtomsNodup
        wellFormed degree isLocal sourceClause sourceMember
    · change
        clause ∈
          (drawingRoutedClauseFormula formula).map fun sourceClause =>
            sourceClause.rename planarSATExternalVariableMap
          at clauseMember
      rcases List.mem_map.mp clauseMember with
        ⟨sourceClause, sourceMember, clauseEqual⟩
      subst clause
      apply EmbeddedClause.atomsNodup_map
        planarSATExternalVariableMap
        Sum.inl_injective
        id
      exact drawingRoutedClauseFormula_allAtomsNodup
        formula degree sourceClause sourceMember
  · change
      clause ∈
        (drawingRoutedVariableFormula formula).map fun sourceClause =>
          sourceClause.rename planarSATExternalVariableMap
        at variableMember
    rcases List.mem_map.mp variableMember with
      ⟨sourceClause, sourceMember, clauseEqual⟩
    subst clause
    apply EmbeddedClause.atomsNodup_map
      planarSATExternalVariableMap
      Sum.inl_injective
      id
    exact drawingRoutedVariableFormula_allAtomsNodup
      formula sourceClause sourceMember

private def denormalizePlanarSATVariable
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (normalized :
      PeriodicPlanarSATVariable Variable × Cell) :
    PlanarSATVariable Variable :=
  match normalized.1 with
  | .terminal indexed endpoint =>
      .inl (.carrier (.terminal
        ⟨indexed, normalized.2, endpoint⟩))
  | .boundary boundary =>
      .inl (.carrier (.boundary
        (boundary.periodTranslate
          formula.incidenceGraph normalized.2)))
  | .atom atom =>
      .inl (.atom (atom, normalized.2))
  | .crossoverInternal (crossing, internal) =>
      .inr
        (crossing.periodTranslate
          formula.incidenceGraph normalized.2,
          internal)

private theorem denormalizePlanarSATVariable_normalize
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (inputVariable : PlanarSATVariable Variable) :
    denormalizePlanarSATVariable formula
        (normalizePlanarSATVariable formula inputVariable) =
      inputVariable := by
  rcases inputVariable with node | ⟨crossing, internal⟩
  · rcases node with carrier | atom
    · rcases carrier with boundary | terminal
      · rcases boundary with ⟨crossing, side⟩
        simp [denormalizePlanarSATVariable,
          normalizePlanarSATVariable,
          CrossingBoundary.periodTranslate,
          CrossingBoundary.periodNormalize,
          CrossingRecord.periodNormalize_periodTranslate_shift]
      · rcases terminal with ⟨indexed, translate, endpoint⟩
        rfl
    · rcases atom with ⟨atom, translate⟩
      rfl
  · simp [denormalizePlanarSATVariable,
      normalizePlanarSATVariable,
      CrossingRecord.periodNormalize_periodTranslate_shift]

/-- Periodicization retains enough data—the prototype and its cell
offset—to reconstruct every finite planar-SAT variable. -/
theorem normalizePlanarSATVariable_injective
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    Function.Injective
      (normalizePlanarSATVariable formula) := by
  intro first second normalizedEqual
  have denormalizedEqual :=
    congrArg (denormalizePlanarSATVariable formula)
      normalizedEqual
  simpa [denormalizePlanarSATVariable_normalize] using
    denormalizedEqual

theorem
    positionPeriodicizedPlanarSATFormula_allIncidenceKeysNodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (finiteFormula :
      List (EmbeddedClause (PlanarSATVariable Variable)))
    (finiteDistinct :
      ∀ clause ∈ finiteFormula, clause.AtomsNodup) :
    (positionPeriodicizedPlanarSATFormula
      formula finiteFormula).AllIncidenceKeysNodup := by
  rw [PositionedPeriodicCNF.AllIncidenceKeysNodup]
  intro positionedClause positionedMember
  unfold positionPeriodicizedPlanarSATFormula
    at positionedMember
  rcases List.mem_map.mp positionedMember with
    ⟨finiteClause, finiteMember, positionedEqual⟩
  subst positionedClause
  have distinct := finiteDistinct finiteClause finiteMember
  unfold EmbeddedClause.AtomsNodup at distinct
  rw [PositionedPeriodicClause.IncidenceKeysNodup]
  change
    (((finiteClause.literals.map
      (periodicizePlanarSATLiteral formula)).map fun literal =>
        (literal.atom, literal.offset))).Nodup
  rw [List.map_map]
  simpa [periodicizePlanarSATLiteral,
    Function.comp_def] using
      distinct.map
        (normalizePlanarSATVariable_injective formula)

theorem
    PositionedPeriodicCNF.allIncidenceKeysNodup_rename
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    (variableMap : Source → Target)
    (injective : Function.Injective variableMap)
    {source : PositionedPeriodicCNF Source}
    (distinct : source.AllIncidenceKeysNodup) :
    (source.rename variableMap).AllIncidenceKeysNodup := by
  rw [PositionedPeriodicCNF.AllIncidenceKeysNodup]
    at distinct ⊢
  intro renamedClause renamedMember
  unfold PositionedPeriodicCNF.rename at renamedMember
  rcases List.mem_map.mp renamedMember with
    ⟨sourceClause, sourceMember, renamedEqual⟩
  subst renamedClause
  have sourceDistinct := distinct sourceClause sourceMember
  rw [PositionedPeriodicClause.IncidenceKeysNodup]
    at sourceDistinct ⊢
  rw [List.map_map]
  let keyMap : Source × Cell → Target × Cell :=
    fun key => (variableMap key.1, key.2)
  have keyMapInjective : Function.Injective keyMap := by
    rintro ⟨firstAtom, firstOffset⟩
      ⟨secondAtom, secondOffset⟩ equal
    have atomsEqual :
        variableMap firstAtom =
          variableMap secondAtom :=
      congrArg Prod.fst equal
    have offsetsEqual :
        firstOffset = secondOffset :=
      congrArg Prod.snd equal
    exact Prod.ext (injective atomsEqual) offsetsEqual
  simpa [keyMap, Function.comp_def] using
      sourceDistinct.map keyMapInjective

theorem
    PositionedPeriodicCNF.allIncidenceKeysNodup_variableGauge
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (gauge : Variable → Cell)
    (distinct : source.AllIncidenceKeysNodup) :
    (source.variableGauge gauge).AllIncidenceKeysNodup := by
  rw [PositionedPeriodicCNF.AllIncidenceKeysNodup]
    at distinct ⊢
  intro gaugedClause gaugedMember
  unfold PositionedPeriodicCNF.variableGauge at gaugedMember
  rcases List.mem_map.mp gaugedMember with
    ⟨sourceClause, sourceMember, gaugedEqual⟩
  subst gaugedClause
  have sourceDistinct := distinct sourceClause sourceMember
  rw [PositionedPeriodicClause.IncidenceKeysNodup]
    at sourceDistinct ⊢
  rw [PeriodicClause.variableGauge,
    List.map_map]
  let keyMap : Variable × Cell → Variable × Cell :=
    fun key => (key.1, Cell.add key.2 (gauge key.1))
  have keyMapInjective : Function.Injective keyMap := by
    rintro ⟨firstAtom, firstOffset⟩
      ⟨secondAtom, secondOffset⟩ equal
    have atomsEqual :
        firstAtom = secondAtom :=
      congrArg Prod.fst equal
    subst secondAtom
    have offsetsEqual :
        firstOffset = secondOffset := by
      rcases firstOffset with ⟨firstX, firstY⟩
      rcases secondOffset with ⟨secondX, secondY⟩
      rcases gauge firstAtom with ⟨gaugeX, gaugeY⟩
      simp [keyMap, Cell.add, Prod.mk.injEq] at equal ⊢
      omega
    exact Prod.ext rfl offsetsEqual
  simpa [PeriodicLiteral.variableGauge,
    keyMap, Function.comp_def] using
      sourceDistinct.map keyMapInjective

theorem
    PositionedPeriodicCNF.allIncidenceKeysNodup_anchorNormalize
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (distinct : source.AllIncidenceKeysNodup) :
    (source.anchorNormalize placement).AllIncidenceKeysNodup := by
  rw [PositionedPeriodicCNF.AllIncidenceKeysNodup]
    at distinct ⊢
  intro normalizedClause normalizedMember
  unfold PositionedPeriodicCNF.anchorNormalize
    at normalizedMember
  rcases List.mem_map.mp normalizedMember with
    ⟨sourceClause, sourceMember, normalizedEqual⟩
  subst normalizedClause
  have sourceDistinct := distinct sourceClause sourceMember
  rw [PositionedPeriodicClause.IncidenceKeysNodup]
    at sourceDistinct ⊢
  rw [PeriodicClause.anchorNormalize, List.map_map]
  let anchor := PeriodicCNF.clauseAnchor sourceClause.literals
  let keyMap : Variable × Cell → Variable × Cell :=
    fun key => (key.1, Cell.sub key.2 anchor)
  have keyMapInjective : Function.Injective keyMap := by
    rintro ⟨firstAtom, firstOffset⟩
      ⟨secondAtom, secondOffset⟩ equal
    have atomsEqual :
        firstAtom = secondAtom :=
      congrArg Prod.fst equal
    subst secondAtom
    have offsetsEqual :
        firstOffset = secondOffset := by
      rcases firstOffset with ⟨firstX, firstY⟩
      rcases secondOffset with ⟨secondX, secondY⟩
      rcases anchor with ⟨anchorX, anchorY⟩
      simp [keyMap, Cell.sub, Prod.mk.injEq] at equal ⊢
      omega
    exact Prod.ext rfl offsetsEqual
  simpa [PeriodicLiteral.anchorNormalize,
    anchor, keyMap, Function.comp_def] using
      sourceDistinct.map keyMapInjective

theorem
    PositionedPeriodicCNF.allIncidenceKeysNodup_deduplicateByLiterals
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (distinct : source.AllIncidenceKeysNodup) :
    source.deduplicateByLiterals.AllIncidenceKeysNodup := by
  rw [PositionedPeriodicCNF.AllIncidenceKeysNodup]
    at distinct ⊢
  intro retainedClause retainedMember
  unfold PositionedPeriodicCNF.deduplicateByLiterals
    at retainedMember
  rcases List.mem_map.mp retainedMember with
    ⟨literals, literalsMember, retainedEqual⟩
  subst retainedClause
  have originalMember :
      literals ∈ source.erase.clauses :=
    List.mem_dedup.mp literalsMember
  unfold PositionedPeriodicCNF.erase at originalMember
  rcases List.mem_map.mp originalMember with
    ⟨sourceClause, sourceMember, literalsEqual⟩
  subst literals
  have sourceDistinct := distinct sourceClause sourceMember
  rw [PositionedPeriodicClause.IncidenceKeysNodup]
    at sourceDistinct ⊢
  exact sourceDistinct

theorem wrappedPeriodicVariable_mk_injective
    {Original : Type*} :
    Function.Injective
      (@WrappedPeriodicVariable.mk Original) := by
  intro first second equal
  exact congrArg WrappedPeriodicVariable.original equal

end PeriodicOrthocrossing
end LeanTrominoes
