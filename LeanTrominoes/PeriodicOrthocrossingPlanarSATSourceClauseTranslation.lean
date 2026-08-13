/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATSourceMembership
import LeanTrominoes.PeriodicOrthocrossingPlanarSATSourceRouteTranslation
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATVariableGauge

/-!
# Clause shape under planar-SAT source translation

Period translation changes the physical variables and clause positions of a
local gadget, but not its presentation order or any clause arity.  Thus a
clause index and literal index valid in one source remain valid in every
physical translate of that source.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- The clause-arity profile of an embedded finite formula, retaining clause
order while forgetting variables and positions. -/
def embeddedFormulaArityProfile
    {Variable : Type*}
    (formula : List (EmbeddedClause Variable)) : List Nat :=
  formula.map fun clause => clause.literals.length

/-- Translating a planar-SAT clause source preserves its ordered clause-arity
profile. -/
theorem DrawingPlanarSATClauseSource.clauseFormula_arityProfile_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (shift : Cell) :
    embeddedFormulaArityProfile
        ((source.periodTranslate formula shift).clauseFormula formula) =
      embeddedFormulaArityProfile
        (source.clauseFormula formula) := by
  cases source <;>
    simp [DrawingPlanarSATClauseSource.periodTranslate,
      DrawingPlanarSATClauseSource.clauseFormula,
      embeddedFormulaArityProfile,
      drawingPlanarSATCrossoverFormulaAt,
      drawingPlanarSATCarrierFormulaAt,
      drawingPlanarSATBendFormulaAt,
      drawingPlanarSATRoutedVariableFormulaAt,
      scopedCrossoverInstance, instantiateFormula,
      equalityInstance, routedClauseAt,
      clauseRouteOccurrencesAt_periodTranslate,
      EmbeddedClause.rename, EmbeddedClause.place,
      EmbeddedClause.map, List.map_map, Function.comp_def]

/-- Equal ordered arity profiles transfer any valid clause/literal index pair
to the target formula. -/
theorem exists_clauseLiteral_of_arityProfile_eq
    {Variable : Type*}
    (sourceFormula targetFormula :
      List (EmbeddedClause Variable))
    (profileEq :
      embeddedFormulaArityProfile targetFormula =
        embeddedFormulaArityProfile sourceFormula)
    (sourceClause : EmbeddedClause Variable)
    (clauseIndex : Nat)
    (sourceClauseMember :
      (sourceClause, clauseIndex) ∈ sourceFormula.zipIdx)
    (sourceLiteral : Variable × Bool)
    (literalIndex : Nat)
    (sourceLiteralMember :
      (sourceLiteral, literalIndex) ∈
        sourceClause.literals.zipIdx) :
    ∃ targetClause targetLiteral,
      (targetClause, clauseIndex) ∈ targetFormula.zipIdx ∧
        (targetLiteral, literalIndex) ∈
          targetClause.literals.zipIdx := by
  have sourceClauseLookup :
      sourceFormula[clauseIndex]? = some sourceClause :=
    (List.mem_zipIdx_iff_getElem?).mp sourceClauseMember
  have sourceLiteralLookup :
      sourceClause.literals[literalIndex]? = some sourceLiteral :=
    (List.mem_zipIdx_iff_getElem?).mp sourceLiteralMember
  have profileLookup :=
    congrArg (fun profile => profile[clauseIndex]?) profileEq
  simp only [embeddedFormulaArityProfile, List.getElem?_map,
    sourceClauseLookup, Option.map_some] at profileLookup
  rcases Option.map_eq_some_iff.mp profileLookup with
    ⟨targetClause, targetClauseLookup, targetLengthEq⟩
  have targetLiteralIndexLt :
      literalIndex < targetClause.literals.length := by
    have sourceLiteralIndexLt :
        literalIndex < sourceClause.literals.length :=
      (List.getElem?_eq_some_iff.mp sourceLiteralLookup).1
    simpa only [targetLengthEq] using sourceLiteralIndexLt
  let targetLiteral := targetClause.literals[literalIndex]
  refine ⟨targetClause, targetLiteral,
    (List.mem_zipIdx_iff_getElem?).mpr targetClauseLookup, ?_⟩
  apply (List.mem_zipIdx_iff_getElem?).mpr
  rw [List.getElem?_eq_getElem targetLiteralIndexLt]

/-- A clause and literal at recorded local indices have counterparts at the
same indices in every translated source. -/
theorem DrawingPlanarSATClauseSource.exists_periodTranslatedClauseLiteral
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (shift : Cell)
    (sourceClause : EmbeddedClause (PlanarSATVariable Variable))
    (sourceClauseMember :
      (sourceClause, source.localClauseIndex) ∈
        (source.clauseFormula formula).zipIdx)
    (sourceLiteral : PlanarSATVariable Variable × Bool)
    (literalIndex : Nat)
    (sourceLiteralMember :
      (sourceLiteral, literalIndex) ∈
        sourceClause.literals.zipIdx) :
    ∃ targetClause targetLiteral,
      (targetClause,
          (source.periodTranslate formula shift).localClauseIndex) ∈
        ((source.periodTranslate formula shift).clauseFormula
          formula).zipIdx ∧
      (targetLiteral, literalIndex) ∈
        targetClause.literals.zipIdx := by
  rw [DrawingPlanarSATClauseSource.localClauseIndex_periodTranslate]
  exact exists_clauseLiteral_of_arityProfile_eq
    (source.clauseFormula formula)
    ((source.periodTranslate formula shift).clauseFormula formula)
    (source.clauseFormula_arityProfile_periodTranslate formula shift)
    sourceClause source.localClauseIndex sourceClauseMember
    sourceLiteral literalIndex sourceLiteralMember

/-! ## Exact literal and anchor translation -/

/-- Translate every kind of finite planar-SAT variable to the same physical
period occurrence. -/
def PlanarSATVariable.periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (input : PlanarSATVariable Variable) (shift : Cell) :
    PlanarSATVariable Variable :=
  match input with
  | .inl node =>
      .inl (node.periodTranslate
        (PeriodicCNF.incidenceGraph formula) shift)
  | .inr (crossing, internal) =>
      .inr
        (crossing.periodTranslate
          (PeriodicCNF.incidenceGraph formula) shift, internal)

@[simp]
theorem CNFRouteOccurrence.sourceTerminal_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrence : CNFRouteOccurrence Variable) (shift : Cell) :
    (occurrence.periodTranslate shift).sourceTerminal formula =
      (occurrence.sourceTerminal formula).periodTranslate shift := by
  rfl

@[simp]
theorem CNFRouteOccurrence.incidence_periodTranslate
    {Variable : Type*}
    (occurrence : CNFRouteOccurrence Variable) (shift : Cell) :
    (occurrence.periodTranslate shift).incidence =
      occurrence.incidence := by
  rfl

@[simp]
theorem RouteBend.equalityLink_first_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (routeBend : RouteBend) (shift : Cell) :
    ((routeBend.periodTranslate shift).equalityLink graph).first =
      (routeBend.equalityLink graph).first.periodTranslate
        graph shift := by
  rfl

@[simp]
theorem RouteBend.equalityLink_second_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (routeBend : RouteBend) (shift : Cell) :
    ((routeBend.periodTranslate shift).equalityLink graph).second =
      (routeBend.equalityLink graph).second.periodTranslate
        graph shift := by
  rfl

@[simp]
theorem PlanarSATVariable.periodTranslate_planarSATCoreVariableMap
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (input :
      Sum CarrierNode (CrossingRecord × CrossoverInternal))
    (shift : Cell) :
    (planarSATCoreVariableMap input).periodTranslate
        formula shift =
      planarSATCoreVariableMap
        (match input with
        | .inl node =>
            .inl (node.periodTranslate
              (PeriodicCNF.incidenceGraph formula) shift)
        | .inr (crossing, internal) =>
            .inr
              (crossing.periodTranslate
                (PeriodicCNF.incidenceGraph formula) shift,
                internal)) := by
  rcases input with node | ⟨crossing, internal⟩
  · rfl
  · rfl

@[simp]
theorem PlanarSATVariable.periodTranslate_planarSATExternalVariableMap
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (node : PlanarSATNode Variable)
    (shift : Cell) :
    (planarSATExternalVariableMap node).periodTranslate
        formula shift =
      planarSATExternalVariableMap
        (node.periodTranslate
          (PeriodicCNF.incidenceGraph formula) shift) := by
  rfl

@[simp]
theorem PlanarSATVariable.periodTranslate_scopedCrossoverVariableMap
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (crossing : CrossingRecord)
    (input : CrossoverVariable)
    (shift : Cell) :
    (planarSATCoreVariableMap
      (scopedCrossoverVariableMap crossing
        (carrierNodeCrossingPorts crossing) input)).periodTranslate
          formula shift =
      planarSATCoreVariableMap
        (scopedCrossoverVariableMap
          (crossing.periodTranslate
            (PeriodicCNF.incidenceGraph formula) shift)
          (carrierNodeCrossingPorts
            (crossing.periodTranslate
              (PeriodicCNF.incidenceGraph formula) shift))
          input) := by
  cases input <;>
    simp [PlanarSATVariable.periodTranslate,
      planarSATCoreVariableMap,
      scopedCrossoverVariableMap,
      carrierNodeCrossingPorts,
      PlanarSATNode.periodTranslate,
      CarrierNode.periodTranslate,
      CrossingBoundary.periodTranslate]

@[simp]
theorem scopedCrossoverVariableMap_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (crossing : CrossingRecord)
    (input : CrossoverVariable)
    (shift : Cell) :
    scopedCrossoverVariableMap
        (crossing.periodTranslate graph shift)
        (carrierNodeCrossingPorts
          (crossing.periodTranslate graph shift))
        input =
      (match
        scopedCrossoverVariableMap crossing
          (carrierNodeCrossingPorts crossing) input with
      | .inl node =>
          .inl (node.periodTranslate graph shift)
      | .inr (sourceCrossing, internal) =>
          .inr
            (sourceCrossing.periodTranslate graph shift,
              internal)) := by
  cases input <;>
    simp [scopedCrossoverVariableMap,
      carrierNodeCrossingPorts,
      CarrierNode.periodTranslate,
      CrossingBoundary.periodTranslate]

/-- Period translation acts pointwise on the variables of every clause in a
source formula, without changing the clause presentation order. -/
theorem
    DrawingPlanarSATClauseSource.clauseFormula_literals_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (shift : Cell) :
    ((source.periodTranslate formula shift).clauseFormula
      formula).map EmbeddedClause.literals =
      (source.clauseFormula formula).map fun clause =>
        clause.literals.map fun literal =>
          (literal.1.periodTranslate formula shift,
            literal.2) := by
  cases source <;>
    simp [DrawingPlanarSATClauseSource.periodTranslate,
      DrawingPlanarSATClauseSource.clauseFormula,
      drawingPlanarSATCrossoverFormulaAt,
      drawingPlanarSATCarrierFormulaAt,
      drawingPlanarSATBendFormulaAt,
      drawingPlanarSATRoutedVariableFormulaAt,
      scopedCrossoverInstance, instantiateFormula,
      crossoverFormula,
      equalityInstance, routedClauseAt,
      clauseRouteOccurrencesAt_periodTranslate,
      EmbeddedClause.rename, EmbeddedClause.place,
      EmbeddedClause.map, List.map_map, Function.comp_def,
      PlanarSATNode.periodTranslate,
      planarSATNodeLinkPeriodTranslate,
      CarrierNode.periodTranslate]

/-- Clauses at one unchanged local index have exactly pointwise translated
literal lists. -/
theorem DrawingPlanarSATClauseSource.clauseLiterals_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (shift : Cell)
    (sourceClause targetClause :
      EmbeddedClause (PlanarSATVariable Variable))
    (sourceMember :
      (sourceClause, source.localClauseIndex) ∈
        (source.clauseFormula formula).zipIdx)
    (targetMember :
      (targetClause,
          (source.periodTranslate formula shift).localClauseIndex) ∈
        ((source.periodTranslate formula shift).clauseFormula
          formula).zipIdx) :
    targetClause.literals =
      sourceClause.literals.map fun literal =>
        (literal.1.periodTranslate formula shift,
          literal.2) := by
  have sourceLookup :=
    (List.mem_zipIdx_iff_getElem?).mp sourceMember
  have targetLookup :=
    (List.mem_zipIdx_iff_getElem?).mp targetMember
  rw [DrawingPlanarSATClauseSource.localClauseIndex_periodTranslate]
    at targetLookup
  have formulaEq :=
    source.clauseFormula_literals_periodTranslate formula shift
  have lookupEq :=
    congrArg
      (fun clauses => clauses[source.localClauseIndex]?)
      formulaEq
  simp only [List.getElem?_map, sourceLookup, targetLookup,
    Option.map_some] at lookupEq
  exact Option.some.inj lookupEq

/-- Periodic normalization preserves the variable prototype and adds the
physical source shift to its offset. -/
theorem normalizePlanarSATVariable_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (input : PlanarSATVariable Variable)
    (shift : Cell) :
    normalizePlanarSATVariable formula
        (input.periodTranslate formula shift) =
      ((normalizePlanarSATVariable formula input).1,
        Cell.add
          (normalizePlanarSATVariable formula input).2 shift) := by
  rcases input with node | ⟨crossing, internal⟩
  · cases node with
    | carrier carrier =>
        cases carrier with
        | boundary boundary =>
            change
              (PeriodicPlanarSATVariable.boundary
                  ((boundary.periodTranslate
                    formula.incidenceGraph shift).periodNormalize
                      formula.incidenceGraph),
                crossingPeriodShift formula.incidenceGraph
                  (boundary.crossing.periodTranslate
                    formula.incidenceGraph shift)) =
              (PeriodicPlanarSATVariable.boundary
                  (boundary.periodNormalize
                    formula.incidenceGraph),
                Cell.add
                  (crossingPeriodShift
                    formula.incidenceGraph boundary.crossing)
                  shift)
            rw [CrossingBoundary.periodNormalize_periodTranslate,
              crossingPeriodShift_periodTranslate]
        | terminal terminal =>
            rcases terminal with
              ⟨indexed, translate, endpoint⟩
            rfl
    | atom site =>
        rcases site with ⟨atom, translate⟩
        rfl
  · simp [PlanarSATVariable.periodTranslate,
      normalizePlanarSATVariable,
      CrossingRecord.periodNormalize_periodTranslate,
      crossingPeriodShift_periodTranslate]

/-- Canonically gauged periodic literal associated with one finite planar-SAT
literal. -/
def gaugedPeriodicPlanarSATLiteral
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (literal : PlanarSATVariable Variable × Bool) :
    PeriodicLiteral
      (WrappedPeriodicPlanarSATVariable Variable) :=
  (wrapPeriodicPlanarSATLiteral
    (periodicizePlanarSATLiteral formula literal)).variableGauge
      (retainedDrawingWrappedPeriodicPlanarSATVariableGauge formula)

/-- Canonical variable gauging commutes with source translation: the atom and
truth value stay fixed, while the literal offset gains the common shift. -/
theorem gaugedPeriodicPlanarSATLiteral_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (literal : PlanarSATVariable Variable × Bool)
    (shift : Cell) :
    gaugedPeriodicPlanarSATLiteral formula
        (literal.1.periodTranslate formula shift,
          literal.2) =
      let source :=
        gaugedPeriodicPlanarSATLiteral formula literal
      ⟨source.atom, Cell.add source.offset shift,
        source.value⟩ := by
  rcases literal with ⟨input, value⟩
  simp [gaugedPeriodicPlanarSATLiteral,
    periodicizePlanarSATLiteral,
    wrapPeriodicPlanarSATLiteral,
    PeriodicLiteral.variableGauge,
    normalizePlanarSATVariable_periodTranslate]
  rcases normalizePlanarSATVariable formula input with
    ⟨atom, ⟨offsetX, offsetY⟩⟩
  rcases shift with ⟨shiftX, shiftY⟩
  rcases
    retainedDrawingWrappedPeriodicPlanarSATVariableGauge
      formula ⟨atom⟩ with
    ⟨gaugeX, gaugeY⟩
  simp [Cell.add]
  constructor <;> ring

/-- Canonically gauged periodic clause associated with one finite planar-SAT
clause. -/
def gaugedPeriodicPlanarSATClause
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clause : EmbeddedClause (PlanarSATVariable Variable)) :
    PeriodicClause
      (WrappedPeriodicPlanarSATVariable Variable) :=
  PeriodicClause.variableGauge
    (retainedDrawingWrappedPeriodicPlanarSATVariableGauge formula)
    (wrapPeriodicPlanarSATClause
      (periodicizePlanarSATClause formula clause))

/-- At an unchanged local source index, the canonically gauged target clause
is the pointwise period translate of the source clause. -/
theorem DrawingPlanarSATClauseSource.gaugedClause_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (shift : Cell)
    (sourceClause targetClause :
      EmbeddedClause (PlanarSATVariable Variable))
    (sourceMember :
      (sourceClause, source.localClauseIndex) ∈
        (source.clauseFormula formula).zipIdx)
    (targetMember :
      (targetClause,
          (source.periodTranslate formula shift).localClauseIndex) ∈
        ((source.periodTranslate formula shift).clauseFormula
          formula).zipIdx) :
    gaugedPeriodicPlanarSATClause formula targetClause =
      (gaugedPeriodicPlanarSATClause
        formula sourceClause).map
          fun literal =>
            ⟨literal.atom, Cell.add literal.offset shift,
              literal.value⟩ := by
  simp only [gaugedPeriodicPlanarSATClause,
    periodicizePlanarSATClause,
    wrapPeriodicPlanarSATClause,
    PeriodicClause.variableGauge]
  simp only [List.map_map]
  rw [source.clauseLiterals_periodTranslate
    formula shift sourceClause targetClause
    sourceMember targetMember]
  simp only [List.map_map]
  apply List.map_congr_left
  intro literal literalMember
  exact gaugedPeriodicPlanarSATLiteral_periodTranslate
    formula literal shift

/-- Adding one common physical period shift to every literal offset does not
change the anchor-normalized clause orbit representative. -/
theorem PeriodicClause.anchorNormalize_map_periodTranslate
    {Variable : Type*}
    (clause : PeriodicClause Variable)
    (shift : Cell) :
    PeriodicClause.anchorNormalize
        (clause.map fun literal =>
          (⟨literal.atom, Cell.add literal.offset shift,
            literal.value⟩ : PeriodicLiteral Variable)) =
      PeriodicClause.anchorNormalize clause := by
  cases clause with
  | nil =>
      rfl
  | cons first rest =>
      have anchorEq :
          PeriodicCNF.clauseAnchor
              ((first :: rest).map fun literal =>
                (⟨literal.atom,
                    Cell.add literal.offset shift,
                    literal.value⟩ :
                  PeriodicLiteral Variable)) =
            Cell.add
              (PeriodicCNF.clauseAnchor (first :: rest))
              shift := by
        simp [PeriodicCNF.clauseAnchor]
      simp only [PeriodicClause.anchorNormalize,
        anchorEq, List.map_map]
      apply List.map_congr_left
      intro literal literalMember
      rcases literal with
        ⟨literalAtom, ⟨literalX, literalY⟩, literalValue⟩
      rcases shift with ⟨shiftX, shiftY⟩
      simp [PeriodicLiteral.anchorNormalize,
        Cell.add, Cell.sub]

/-- At unchanged local clause index, physical source translation leaves the
anchor-normalized canonically gauged clause exactly unchanged. -/
theorem
    DrawingPlanarSATClauseSource.anchorNormalizedGaugedClause_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (shift : Cell)
    (sourceClause targetClause :
      EmbeddedClause (PlanarSATVariable Variable))
    (sourceMember :
      (sourceClause, source.localClauseIndex) ∈
        (source.clauseFormula formula).zipIdx)
    (targetMember :
      (targetClause,
          (source.periodTranslate formula shift).localClauseIndex) ∈
        ((source.periodTranslate formula shift).clauseFormula
          formula).zipIdx) :
    (gaugedPeriodicPlanarSATClause
        formula targetClause).anchorNormalize =
      (gaugedPeriodicPlanarSATClause
        formula sourceClause).anchorNormalize := by
  rw [source.gaugedClause_periodTranslate
    formula shift sourceClause targetClause
    sourceMember targetMember]
  exact
    PeriodicClause.anchorNormalize_map_periodTranslate
      (gaugedPeriodicPlanarSATClause formula sourceClause)
      shift

/-- Translating every literal of a nonempty periodic clause translates its
anchor by the same amount. -/
theorem clauseAnchor_map_periodTranslate
    {Variable : Type*}
    (clause : PeriodicClause Variable)
    (shift : Cell)
    (nonempty : clause ≠ []) :
    PeriodicCNF.clauseAnchor
        (clause.map fun literal =>
          ⟨literal.atom, Cell.add literal.offset shift,
            literal.value⟩) =
      Cell.add (PeriodicCNF.clauseAnchor clause) shift := by
  cases clause with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
      simp [PeriodicCNF.clauseAnchor]

/-- The canonically gauged clause anchor is equivariant under physical source
translation. -/
theorem DrawingPlanarSATClauseSource.clauseAnchor_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (shift : Cell)
    (sourceClause targetClause :
      EmbeddedClause (PlanarSATVariable Variable))
    (sourceMember :
      (sourceClause, source.localClauseIndex) ∈
        (source.clauseFormula formula).zipIdx)
    (targetMember :
      (targetClause,
          (source.periodTranslate formula shift).localClauseIndex) ∈
        ((source.periodTranslate formula shift).clauseFormula
          formula).zipIdx)
    (nonempty : sourceClause.literals ≠ []) :
    PeriodicCNF.clauseAnchor
        (gaugedPeriodicPlanarSATClause formula targetClause) =
      Cell.add
        (PeriodicCNF.clauseAnchor
          (gaugedPeriodicPlanarSATClause
            formula sourceClause))
        shift := by
  rw [source.gaugedClause_periodTranslate
    formula shift sourceClause targetClause
    sourceMember targetMember]
  apply clauseAnchor_map_periodTranslate
  simpa [gaugedPeriodicPlanarSATClause,
    periodicizePlanarSATClause,
    wrapPeriodicPlanarSATClause,
    PeriodicClause.variableGauge] using nonempty

end PeriodicOrthocrossing
end LeanTrominoes
