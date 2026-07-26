import LeanTrominoes.PeriodicCNFPlanarFormula
import LeanTrominoes.PlanarThreeSATWidth

/-!
# Width of the routed planar SAT presentation

All local Figure 8 crossover, duplicator, and equality-wire clauses are
already width three.  The only input-dependent clauses are the routed copies
of source clauses.  This file proves that their literal lists have exactly
the source-clause length and composes the component bounds into a width-three
certificate for the complete finite routed block.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Every complete straight-carrier formula is an equality-wire family. -/
theorem drawingCompleteCarrierFormula_widthAtMostThree
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    FormulaWidthAtMost 3
      (drawingCompleteCarrierFormula graph) := by
  exact equalityFamily_widthAtMostThree
    (drawingCompleteCarrierLinks graph)

/-- Every route-bend formula is an equality-wire family. -/
theorem drawingRouteBendFormula_widthAtMostThree
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    FormulaWidthAtMost 3
      (drawingRouteBendFormula graph) := by
  exact equalityFamily_widthAtMostThree
    (drawingRouteBendLinks graph)

/-- Complete straight carriers and bends have width at most three. -/
theorem drawingRouteWireFormula_widthAtMostThree
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    FormulaWidthAtMost 3
      (drawingRouteWireFormula graph) := by
  apply
    (formulaWidthAtMost_append_iff 3
      (drawingCompleteCarrierFormula graph)
      (drawingRouteBendFormula graph)).mpr
  exact
    ⟨drawingCompleteCarrierFormula_widthAtMostThree graph,
      drawingRouteBendFormula_widthAtMostThree graph⟩

/-- Every carrier-node crossover family has width at most three. -/
theorem drawingCarrierNodeCrossoverFormula_widthAtMostThree
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    FormulaWidthAtMost 3
      (drawingCarrierNodeCrossoverFormula graph) := by
  exact crossoverFamily_widthAtMostThree
    (orientedCrossings graph)
    carrierNodeCrossingPorts crossingMacroOrigin 1

/-- Scoping route variables into the crossover sum preserves width. -/
theorem scopedDrawingRouteWireFormula_widthAtMostThree
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    FormulaWidthAtMost 3
      (scopedDrawingRouteWireFormula graph) := by
  exact
    (formulaWidthAtMost_map_iff 3
      (fun node =>
        (Sum.inl node :
          Sum CarrierNode
            (CrossingRecord × CrossoverInternal)))
      id (drawingRouteWireFormula graph)).mpr
        (drawingRouteWireFormula_widthAtMostThree graph)

/-- The complete crossover-and-route core has width at most three. -/
theorem drawingRoutePlanarCoreFormula_widthAtMostThree
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    FormulaWidthAtMost 3
      (drawingRoutePlanarCoreFormula graph) := by
  apply
    (formulaWidthAtMost_append_iff 3
      (drawingCarrierNodeCrossoverFormula graph)
      (scopedDrawingRouteWireFormula graph)).mpr
  exact
    ⟨drawingCarrierNodeCrossoverFormula_widthAtMostThree graph,
      scopedDrawingRouteWireFormula_widthAtMostThree graph⟩

/-- Renaming the route core into the complete planar-SAT variable type
preserves width. -/
theorem scopedDrawingPlanarSATCore_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    FormulaWidthAtMost 3
      (scopedDrawingPlanarSATCore formula) := by
  exact
    (formulaWidthAtMost_map_iff 3
      planarSATCoreVariableMap id
      (drawingRoutePlanarCoreFormula
        (PeriodicCNF.incidenceGraph formula))).mpr
      (drawingRoutePlanarCoreFormula_widthAtMostThree
        (PeriodicCNF.incidenceGraph formula))

/-- Routed variable gadgets are families of active equality arms, hence
width three. -/
theorem drawingRoutedVariableFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    FormulaWidthAtMost 3
      (drawingRoutedVariableFormula formula) := by
  apply
    (formulaWidthAtMost_flatMap_iff 3
      (drawingVariableRouteSites formula)
      (routedVariableFormulaAt formula)).mpr
  intro site _
  exact equalityFamily_widthAtMostThree
    (routedVariableLinksAt formula site)

/-- Scoping routed variable gadgets preserves width. -/
theorem scopedDrawingRoutedVariableFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    FormulaWidthAtMost 3
      (scopedDrawingRoutedVariableFormula formula) := by
  exact
    (formulaWidthAtMost_map_iff 3
      planarSATExternalVariableMap id
      (drawingRoutedVariableFormula formula)).mpr
        (drawingRoutedVariableFormula_widthAtMostThree formula)

/-! ## Routed source-clause lengths -/

/-- A keyed `flatMap` over a list with distinct keys selects exactly the
member carrying the requested key. -/
theorem flatMap_if_key_eq_of_nodup
    {Key Value Output : Type*} [DecidableEq Key]
    (items : List (Value × Key))
    (keysNodup : (items.map Prod.snd).Nodup)
    (selected : Value × Key) (selectedMem : selected ∈ items)
    (output : Value × Key → List Output) :
    items.flatMap (fun item =>
        if item.2 = selected.2 then output item else []) =
      output selected := by
  induction items with
  | nil =>
      simp at selectedMem
  | cons head tail induction =>
      simp only [List.map_cons, List.nodup_cons] at keysNodup
      rcases keysNodup with ⟨headKeyFresh, tailKeysNodup⟩
      simp only [List.mem_cons] at selectedMem
      rcases selectedMem with selectedEq | selectedTailMem
      · subst selected
        simp only [List.flatMap_cons, ↓reduceIte]
        have noTailKey :
            ∀ item ∈ tail, item.2 ≠ head.2 := by
          intro item itemMem keyEq
          apply headKeyFresh
          exact List.mem_map.mpr
            ⟨item, itemMem, keyEq⟩
        have tailEmpty :
            tail.flatMap (fun item =>
              if item.2 = head.2 then output item else []) = [] := by
          apply List.flatMap_eq_nil_iff.mpr
          intro item itemMem
          simp [noTailKey item itemMem]
        rw [tailEmpty]
        simp
      · have headKeyNe : head.2 ≠ selected.2 := by
          intro keyEq
          apply headKeyFresh
          exact List.mem_map.mpr
            ⟨selected, selectedTailMem, keyEq.symm⟩
        simp only [List.flatMap_cons, if_neg headKeyNe,
          List.nil_append]
        exact induction tailKeysNodup selectedTailMem

/-- Filtering a generated incidence block by clause index either retains the
whole block or removes it. -/
theorem filter_clauseIncidenceBlock
    {Variable : Type*}
    (selectedIndex : Nat)
    (taggedClause : PeriodicClause Variable × Nat) :
    ((taggedClause.1.zipIdx.map fun taggedLiteral =>
        (⟨taggedClause.2, taggedClause.1,
          taggedLiteral.2, taggedLiteral.1⟩ :
            CNFIncidence Variable)).filter
      fun incidence =>
        incidence.clauseIndex = selectedIndex) =
      if taggedClause.2 = selectedIndex then
        taggedClause.1.zipIdx.map fun taggedLiteral =>
          ⟨taggedClause.2, taggedClause.1,
            taggedLiteral.2, taggedLiteral.1⟩
      else [] := by
  by_cases same : taggedClause.2 = selectedIndex
  · rw [if_pos same]
    apply List.filter_eq_self.mpr
    intro incidence incidenceMem
    rcases List.mem_map.mp incidenceMem with
      ⟨taggedLiteral, taggedLiteralMem, incidenceEq⟩
    subst incidence
    exact decide_eq_true same
  · rw [if_neg same]
    apply List.filter_eq_nil_iff.mpr
    intro incidence incidenceMem
    rcases List.mem_map.mp incidenceMem with
      ⟨taggedLiteral, taggedLiteralMem, incidenceEq⟩
    subst incidence
    simp [same]

/-- Selecting the metadata incidences for a tagged source clause recovers
exactly that clause's literal block. -/
theorem incidencesWithMetadata_filter_clauseIndex
    {Variable : Type*}
    (formula : PeriodicCNF Variable)
    (taggedClause : PeriodicClause Variable × Nat)
    (taggedMem : taggedClause ∈ formula.clauses.zipIdx) :
    (PeriodicCNF.incidencesWithMetadata formula).filter
        (fun incidence =>
          incidence.clauseIndex = taggedClause.2) =
      taggedClause.1.zipIdx.map fun taggedLiteral =>
        ⟨taggedClause.2, taggedClause.1,
          taggedLiteral.2, taggedLiteral.1⟩ := by
  rw [PeriodicCNF.incidencesWithMetadata,
    List.filter_flatMap]
  simp_rw [filter_clauseIncidenceBlock taggedClause.2]
  exact flatMap_if_key_eq_of_nodup
    formula.clauses.zipIdx
    (List.nodup_zipIdx_map_snd formula.clauses)
    taggedClause taggedMem
    (fun taggedClause =>
      taggedClause.1.zipIdx.map fun taggedLiteral =>
        (⟨taggedClause.2, taggedClause.1,
          taggedLiteral.2, taggedLiteral.1⟩ :
            CNFIncidence Variable))

/-- Filtering a `zipIdx` by a predicate on values has the same length as
filtering the original list. -/
theorem length_filter_zipIdx_fst
    {Value : Type*}
    (items : List Value) (predicate : Value → Bool) :
    (items.zipIdx.filter
      fun tagged => predicate tagged.1).length =
        (items.filter predicate).length := by
  calc
    (items.zipIdx.filter
        fun tagged => predicate tagged.1).length =
      ((items.zipIdx.filter
        fun tagged => predicate tagged.1).map Prod.fst).length := by
          simp
    _ = ((items.zipIdx.map Prod.fst).filter predicate).length := by
          have filteredMap :
              (items.zipIdx.filter
                fun tagged => predicate tagged.1).map Prod.fst =
                (items.zipIdx.map Prod.fst).filter predicate := by
            simpa [Function.comp_def] using
              (@List.filter_map
                (Value × Nat) Value Prod.fst predicate
                items.zipIdx).symm
          rw [filteredMap]
    _ = (items.filter predicate).length := by
          rw [List.zipIdx_map_fst]

/-- At a represented translated clause site, routed occurrences are in
one-to-one correspondence with the source clause's literal occurrences. -/
theorem clauseRouteOccurrencesAt_length
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (taggedClause : PeriodicClause Variable × Nat)
    (taggedMem : taggedClause ∈ formula.clauses.zipIdx)
    (translate : Cell) :
    (clauseRouteOccurrencesAt formula
      (taggedClause.2, translate)).length =
        taggedClause.1.length := by
  rw [clauseRouteOccurrencesAt, List.length_map]
  change
    (formula.incidencesWithMetadata.zipIdx.filter
      (fun taggedIncidence =>
        decide
          (taggedIncidence.1.clauseIndex =
            taggedClause.2))).length =
      taggedClause.1.length
  calc
    (formula.incidencesWithMetadata.zipIdx.filter
      (fun taggedIncidence =>
        decide
          (taggedIncidence.1.clauseIndex =
            taggedClause.2))).length =
        (formula.incidencesWithMetadata.filter
          (fun incidence =>
            decide
              (incidence.clauseIndex =
                taggedClause.2))).length :=
      length_filter_zipIdx_fst
        formula.incidencesWithMetadata
        (fun incidence =>
          decide
            (incidence.clauseIndex =
              taggedClause.2))
    _ = taggedClause.1.length := by
      rw [incidencesWithMetadata_filter_clauseIndex
        formula taggedClause taggedMem]
      simp

/-- Every routed copy of a width-three source clause has width at most
three. -/
theorem drawingRoutedClauseFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceWidth : formula.WidthAtMost 3) :
    FormulaWidthAtMost 3
      (drawingRoutedClauseFormula formula) := by
  intro routedClause routedClauseMem
  rcases List.mem_map.mp routedClauseMem with
    ⟨site, siteMem, routedClauseEq⟩
  subst routedClause
  rcases List.mem_flatMap.mp siteMem with
    ⟨taggedClause, taggedMem, siteMem⟩
  rcases List.mem_map.mp siteMem with
    ⟨translate, translateMem, siteEq⟩
  subst site
  unfold EmbeddedClause.WidthAtMost routedClauseAt
  simp only [List.length_map]
  rw [clauseRouteOccurrencesAt_length
    formula taggedClause taggedMem translate]
  exact sourceWidth taggedClause.1
    (List.fst_mem_of_mem_zipIdx taggedMem)

/-- Scoping routed source clauses preserves width. -/
theorem scopedDrawingRoutedClauseFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceWidth : formula.WidthAtMost 3) :
    FormulaWidthAtMost 3
      (scopedDrawingRoutedClauseFormula formula) := by
  exact
    (formulaWidthAtMost_map_iff 3
      planarSATExternalVariableMap id
      (drawingRoutedClauseFormula formula)).mpr
        (drawingRoutedClauseFormula_widthAtMostThree
          formula sourceWidth)

/-- The complete finite routed planar SAT block preserves width three. -/
theorem drawingPlanarSATFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceWidth : formula.WidthAtMost 3) :
    FormulaWidthAtMost 3
      (drawingPlanarSATFormula formula) := by
  rw [drawingPlanarSATFormula,
    formulaWidthAtMost_append_iff,
    formulaWidthAtMost_append_iff]
  exact
    ⟨⟨scopedDrawingPlanarSATCore_widthAtMostThree formula,
        scopedDrawingRoutedClauseFormula_widthAtMostThree
          formula sourceWidth⟩,
      scopedDrawingRoutedVariableFormula_widthAtMostThree
        formula⟩

end PeriodicOrthocrossing
end LeanTrominoes
