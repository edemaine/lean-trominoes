import LeanTrominoes.PeriodicCNFPlanarRetainedWidth
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRibbonReady

/-!
# Nonempty clauses in the retained planar SAT formula

The periodic planarity proof needs every retained clause vertex to have an
incident route.  All fixed crossover and equality gadgets are structurally
nonempty.  The only possible empty clauses are routed copies of empty source
clauses, so a source-level nonemptiness premise suffices for the complete
finite retained block and hence for the final gauged periodic formula.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- Renaming and moving an embedded clause do not turn a nonempty literal
list into an empty one. -/
theorem EmbeddedClause.map_literals_ne_nil
    {Source Target : Type*}
    (variableMap : Source → Target)
    (positionMap : Cell → Cell)
    (clause : EmbeddedClause Source)
    (nonempty : clause.literals ≠ []) :
    (clause.map variableMap positionMap).literals ≠ [] := by
  intro empty
  apply nonempty
  apply List.length_eq_zero_iff.mp
  have lengthZero := congrArg List.length empty
  simpa [EmbeddedClause.map] using lengthZero

/-- Every instantiated copy of a nonempty embedded formula remains
nonempty. -/
theorem instantiateFormula_clausesNonempty
    {Source Target : Type*}
    (variableMap : Source → Target)
    (origin : Cell) (scale : Int)
    (formula : List (EmbeddedClause Source))
    (nonempty :
      ∀ clause ∈ formula, clause.literals ≠ []) :
    ∀ clause ∈ instantiateFormula variableMap origin scale formula,
      clause.literals ≠ [] := by
  intro clause clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨sourceClause, sourceClauseMember, rfl⟩
  apply EmbeddedClause.map_literals_ne_nil
  apply EmbeddedClause.map_literals_ne_nil
  exact nonempty sourceClause sourceClauseMember

/-- The fixed crossover truth-table presentation has no empty clause. -/
theorem crossoverFormula_clausesNonempty :
    ∀ clause ∈ crossoverFormula, clause.literals ≠ [] := by
  native_decide

/-- Every finite family of scoped crossover instances has nonempty
clauses. -/
theorem crossoverFamily_clausesNonempty
    {Site Variable : Type*}
    (sites : List Site)
    (ports : Site → CrossoverPorts Variable)
    (origin : Site → Cell) (scale : Int) :
    ∀ clause ∈ crossoverFamily sites ports origin scale,
      clause.literals ≠ [] := by
  intro clause clauseMember
  rcases List.mem_flatMap.mp clauseMember with
    ⟨site, _siteMember, localMember⟩
  exact
    instantiateFormula_clausesNonempty
      (scopedCrossoverVariableMap site (ports site))
      (origin site) scale crossoverFormula
      crossoverFormula_clausesNonempty clause localMember

/-- Every equality-wire family consists of binary clauses. -/
theorem equalityFamily_clausesNonempty
    {Variable : Type*}
    (links : List (EqualityLink Variable)) :
    ∀ clause ∈ equalityFamily links, clause.literals ≠ [] := by
  intro clause clauseMember
  rcases List.mem_flatMap.mp clauseMember with
    ⟨link, _linkMember, localMember⟩
  simp [equalityInstance] at localMember
  rcases localMember with localEq | localEq <;>
    subst clause <;> simp

/-- The complete retained route core has no empty clause. -/
theorem retainedDrawingRoutePlanarCoreFormula_clausesNonempty
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    ∀ clause ∈ retainedDrawingRoutePlanarCoreFormula graph,
      clause.literals ≠ [] := by
  intro clause clauseMember
  rcases List.mem_append.mp clauseMember with
    crossoverMember | wireMember
  · exact
      crossoverFamily_clausesNonempty
        (orientedCrossingHalo graph)
        carrierNodeCrossingPorts crossingMacroOrigin 1
        clause crossoverMember
  · rcases List.mem_map.mp wireMember with
      ⟨sourceClause, sourceClauseMember, rfl⟩
    apply EmbeddedClause.map_literals_ne_nil
    rcases List.mem_append.mp sourceClauseMember with
      carrierMember | bendMember
    · exact
        equalityFamily_clausesNonempty
          (retainedDrawingCompleteCarrierLinks graph)
          sourceClause carrierMember
    · exact
        equalityFamily_clausesNonempty
          (drawingRouteBendLinks graph)
          sourceClause bendMember

/-- Embedding the retained route core preserves clause nonemptiness. -/
theorem retainedScopedDrawingPlanarSATCore_clausesNonempty
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    ∀ clause ∈ retainedScopedDrawingPlanarSATCore formula,
      clause.literals ≠ [] := by
  intro clause clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨sourceClause, sourceClauseMember, rfl⟩
  apply EmbeddedClause.map_literals_ne_nil
  exact
    retainedDrawingRoutePlanarCoreFormula_clausesNonempty
      (PeriodicCNF.incidenceGraph formula)
      sourceClause sourceClauseMember

/-- A nonempty source clause yields only nonempty routed copies. -/
theorem drawingRoutedClauseFormula_clausesNonempty
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ []) :
    ∀ clause ∈ drawingRoutedClauseFormula formula,
      clause.literals ≠ [] := by
  intro clause clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨site, siteMember, rfl⟩
  rcases List.mem_flatMap.mp siteMember with
    ⟨taggedClause, taggedClauseMember, translatedMember⟩
  rcases List.mem_map.mp translatedMember with
    ⟨translate, _translateMember, siteEq⟩
  subst site
  intro empty
  have lengthZero := congrArg List.length empty
  simp only [routedClauseAt, List.length_map] at lengthZero
  rw [clauseRouteOccurrencesAt_length
    formula taggedClause taggedClauseMember translate] at lengthZero
  apply sourceClausesNonempty taggedClause.1
    (List.fst_mem_of_mem_zipIdx taggedClauseMember)
  exact List.length_eq_zero_iff.mp lengthZero

/-- Scoping routed source clauses preserves their nonemptiness. -/
theorem scopedDrawingRoutedClauseFormula_clausesNonempty
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ []) :
    ∀ clause ∈ scopedDrawingRoutedClauseFormula formula,
      clause.literals ≠ [] := by
  intro clause clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨sourceClause, sourceClauseMember, rfl⟩
  apply EmbeddedClause.map_literals_ne_nil
  exact
    drawingRoutedClauseFormula_clausesNonempty
      formula sourceClausesNonempty sourceClause sourceClauseMember

/-- Every active routed-variable arm is a binary equality family. -/
theorem scopedDrawingRoutedVariableFormula_clausesNonempty
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    ∀ clause ∈ scopedDrawingRoutedVariableFormula formula,
      clause.literals ≠ [] := by
  intro clause clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨sourceClause, sourceClauseMember, rfl⟩
  apply EmbeddedClause.map_literals_ne_nil
  rcases List.mem_flatMap.mp sourceClauseMember with
    ⟨site, _siteMember, localMember⟩
  exact
    equalityFamily_clausesNonempty
      (routedVariableLinksAt formula site)
      sourceClause localMember

/-- Source-clause nonemptiness is the only extra premise needed to show
that the complete retained finite planar-SAT formula has no empty clause. -/
theorem retainedDrawingPlanarSATFormula_clausesNonempty_of_source
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ []) :
    ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
      clause.literals ≠ [] := by
  intro clause clauseMember
  rcases List.mem_append.mp clauseMember with
    coreOrClauseMember | variableMember
  · rcases List.mem_append.mp coreOrClauseMember with
      coreMember | routedClauseMember
    · exact
        retainedScopedDrawingPlanarSATCore_clausesNonempty
          formula clause coreMember
    · exact
        scopedDrawingRoutedClauseFormula_clausesNonempty
          formula sourceClausesNonempty clause routedClauseMember
  · exact
      scopedDrawingRoutedVariableFormula_clausesNonempty
        formula clause variableMember

/-- The final gauged and deduplicated retained periodic formula has no empty
clause whenever the source formula has none. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATFormula_clausesNonempty_of_source
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ []) :
    ∀ clause ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).erase.clauses,
      clause ≠ [] :=
  retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATFormula_clausesNonempty
    formula
    (retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty)

end PeriodicOrthocrossing
end LeanTrominoes
