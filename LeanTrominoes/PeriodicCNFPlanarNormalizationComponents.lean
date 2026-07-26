import LeanTrominoes.PeriodicCNFPlanarDeduplicationWrapping
import LeanTrominoes.PeriodicCNFPlanarAtomNormalizationDegree

/-!
# Componentwise normalization of the periodic planar SAT formula

The anchor-normalized routed formula splits exactly into crossover,
straight-carrier, bend, routed-clause, and variable-arm clause families.
Global clause deduplication removes no fewer occurrences than deduplicating
those five components separately, yielding the occurrence-list sublist
bridge used by the final degree certificate.
-/

namespace LeanTrominoes

theorem List.dedup_append_sublist_dedup_append
    {Value : Type*} [DecidableEq Value] :
    ∀ (first second : List Value),
      List.Sublist (first ++ second).dedup
        (first.dedup ++ second.dedup) := by
  intro first
  induction first with
  | nil =>
      intro second
      simp
  | cons value first induction =>
      intro second
      change List.Sublist
        (value :: (first ++ second)).dedup
        ((value :: first).dedup ++ second.dedup)
      by_cases valueTailMem : value ∈ first ++ second
      · rw [List.dedup_cons_of_mem valueTailMem]
        by_cases valueFirstMem : value ∈ first
        · rw [List.dedup_cons_of_mem valueFirstMem]
          exact induction second
        · rw [List.dedup_cons_of_notMem valueFirstMem,
            List.cons_append]
          exact List.sublist_cons_of_sublist value
            (induction second)
      · have valueFirstNotMem : value ∉ first := by
          simp only [List.mem_append, not_or] at valueTailMem
          exact valueTailMem.1
        rw [List.dedup_cons_of_notMem valueTailMem,
          List.dedup_cons_of_notMem valueFirstNotMem,
          List.cons_append]
        exact (induction second).cons_cons value

theorem PeriodicCNF.deduplicate_append_variableOccurrences_sublist
    {Variable : Type*} [DecidableEq Variable]
    (first second :
      List (PeriodicClause Variable)) :
    List.Sublist
      (PeriodicCNF.variableOccurrences
        ⟨(first ++ second).dedup⟩)
      (PeriodicCNF.variableOccurrences
        ⟨first.dedup ++ second.dedup⟩) := by
  unfold PeriodicCNF.variableOccurrences
  exact
    (List.dedup_append_sublist_dedup_append
      first second).flatMap
        (fun clause => clause.map PeriodicLiteral.atom)

theorem List.dedup_flatten_sublist_flatMap_dedup
    {Value : Type*} [DecidableEq Value] :
    ∀ (components : List (List Value)),
      List.Sublist components.flatten.dedup
        (components.flatMap List.dedup) := by
  intro components
  induction components with
  | nil =>
      simp
  | cons first components induction =>
      rw [List.flatten_cons, List.flatMap_cons]
      exact
        (List.dedup_append_sublist_dedup_append
          first components.flatten).trans
        ((List.Sublist.refl first.dedup).append induction)

theorem PeriodicCNF.deduplicate_components_variableOccurrences_sublist
    {Variable : Type*} [DecidableEq Variable]
    (components :
      List (List (PeriodicClause Variable))) :
    List.Sublist
      (PeriodicCNF.variableOccurrences
        ⟨components.flatten.dedup⟩)
      (PeriodicCNF.variableOccurrences
        ⟨components.flatMap List.dedup⟩) := by
  unfold PeriodicCNF.variableOccurrences
  exact
    (List.dedup_flatten_sublist_flatMap_dedup
      components).flatMap
        (fun clause => clause.map PeriodicLiteral.atom)

end LeanTrominoes

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

theorem periodicizePlanarSATClause_external_rename
    {Variable : Type*}
    (clause : EmbeddedClause (PlanarSATNode Variable)) :
    periodicizePlanarSATClause
        (clause.rename
          (@planarSATExternalVariableMap Variable)) =
      PeriodicEquality.periodicizeClause
        normalizePlanarSATNode clause := by
  rcases clause with ⟨position, literals⟩
  simp [periodicizePlanarSATClause,
    periodicizePlanarSATLiteral,
    PeriodicEquality.periodicizeClause,
    PeriodicEquality.periodicizeLiteral,
    EmbeddedClause.rename, EmbeddedClause.map,
    planarSATExternalVariableMap,
    normalizePlanarSATNode,
    List.map_map, Function.comp_def]

theorem normalizedScopedDrawingRoutedClauseFormula_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    ((scopedDrawingRoutedClauseFormula formula).map
      periodicizePlanarSATClause).map
        PeriodicClause.anchorNormalize =
      normalizedRoutedClauseClauses formula := by
  unfold scopedDrawingRoutedClauseFormula
    normalizedRoutedClauseClauses
  simp only [List.map_map]
  apply List.map_congr_left
  intro clause _clauseMem
  exact congrArg PeriodicClause.anchorNormalize
    (periodicizePlanarSATClause_external_rename clause)

theorem normalizedScopedDrawingRoutedVariableFormula_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    ((scopedDrawingRoutedVariableFormula formula).map
      periodicizePlanarSATClause).map
        PeriodicClause.anchorNormalize =
      PeriodicEquality.normalizedFormulaClauses
        normalizePlanarSATNode
        (drawingRoutedVariableLinks formula) := by
  unfold scopedDrawingRoutedVariableFormula
    PeriodicEquality.normalizedFormulaClauses
  rw [drawingRoutedVariableFormula_eq_equalityFamily]
  simp only [List.map_map]
  apply List.map_congr_left
  intro clause _clauseMem
  exact congrArg PeriodicClause.anchorNormalize
    (periodicizePlanarSATClause_external_rename clause)

def normalizedScopedDrawingPlanarSATCoreClauses
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (PeriodicClause (PeriodicPlanarSATVariable Variable)) :=
  ((scopedDrawingPlanarSATCore formula).map
    periodicizePlanarSATClause).map
      PeriodicClause.anchorNormalize

theorem drawingPeriodicPlanarSATFormula_anchorNormalize_clauses
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingPeriodicPlanarSATFormula
      formula).anchorNormalize.clauses =
      normalizedScopedDrawingPlanarSATCoreClauses formula ++
        normalizedRoutedClauseClauses formula ++
          PeriodicEquality.normalizedFormulaClauses
            normalizePlanarSATNode
            (drawingRoutedVariableLinks formula) := by
  unfold drawingPeriodicPlanarSATFormula
    drawingPlanarSATFormula
    PeriodicCNF.anchorNormalize
    normalizedScopedDrawingPlanarSATCoreClauses
  simp only [List.map_append, List.append_assoc]
  rw [normalizedScopedDrawingRoutedClauseFormula_eq,
    normalizedScopedDrawingRoutedVariableFormula_eq]

def embedPeriodicCarrierClause
    {Variable : Type*}
    (clause : PeriodicClause PeriodicCarrierNode) :
    PeriodicClause (PeriodicPlanarSATVariable Variable) :=
  clause.map fun literal =>
    ⟨periodicCarrierNodeToPlanarSATVariable literal.atom,
      literal.offset, literal.value⟩

theorem embedPeriodicCarrierFormula_clauses
    {Variable : Type*}
    (source : PeriodicCNF PeriodicCarrierNode) :
    (embedPeriodicCarrierFormula
      (Variable := Variable) source).clauses =
      source.clauses.map embedPeriodicCarrierClause := by
  rfl

theorem periodicizePlanarSATClause_carrier_core_rename
    {Variable : Type*}
    (clause : EmbeddedClause CarrierNode) :
    periodicizePlanarSATClause
      ((clause.rename fun node =>
        (Sum.inl node :
          Sum CarrierNode
            (CrossingRecord × CrossoverInternal))).rename
        (@planarSATCoreVariableMap Variable)) =
      embedPeriodicCarrierClause
        (PeriodicEquality.periodicizeClause
          normalizeCarrierNode clause) := by
  rcases clause with ⟨position, literals⟩
  simp only [periodicizePlanarSATClause,
    periodicizePlanarSATLiteral,
    PeriodicEquality.periodicizeClause,
    PeriodicEquality.periodicizeLiteral,
    EmbeddedClause.rename, EmbeddedClause.map,
    planarSATCoreVariableMap,
    embedPeriodicCarrierClause,
    List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro literal _literalMem
  rcases literal with ⟨node, polarity⟩
  cases node <;>
    rfl

@[simp]
theorem embedPeriodicCarrierClause_anchorNormalize
    {Variable : Type*}
    (clause : PeriodicClause PeriodicCarrierNode) :
    embedPeriodicCarrierClause clause.anchorNormalize =
      (embedPeriodicCarrierClause
        (Variable := Variable) clause).anchorNormalize := by
  cases clause with
  | nil =>
      rfl
  | cons first rest =>
      rcases first with ⟨atom, ⟨offsetX, offsetY⟩, value⟩
      simp [embedPeriodicCarrierClause,
        PeriodicClause.anchorNormalize,
        PeriodicLiteral.anchorNormalize,
        PeriodicCNF.clauseAnchor,
        List.map_map, Function.comp_def]

def normalizedScopedDrawingCrossoverClauses
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (PeriodicClause (PeriodicPlanarSATVariable Variable)) :=
  (((drawingCarrierNodeCrossoverFormula
    (PeriodicCNF.incidenceGraph formula)).map fun clause =>
      clause.rename
        (@planarSATCoreVariableMap Variable)).map
          periodicizePlanarSATClause).map
            PeriodicClause.anchorNormalize

def embeddedNormalizedCompleteCarrierClauses
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (PeriodicClause (PeriodicPlanarSATVariable Variable)) :=
  (PeriodicEquality.normalizedFormulaClauses
    normalizeCarrierNode
    (drawingCompleteCarrierLinks
      (PeriodicCNF.incidenceGraph formula))).map
        (@embedPeriodicCarrierClause Variable)

def embeddedNormalizedRouteBendClauses
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (PeriodicClause (PeriodicPlanarSATVariable Variable)) :=
  (PeriodicEquality.normalizedFormulaClauses
    normalizeCarrierNode
    (drawingRouteBendLinks
      (PeriodicCNF.incidenceGraph formula))).map
        (@embedPeriodicCarrierClause Variable)

def normalizedEmbeddedRouteWireClauses
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (PeriodicClause (PeriodicPlanarSATVariable Variable)) :=
  embeddedNormalizedCompleteCarrierClauses formula ++
    embeddedNormalizedRouteBendClauses formula

theorem normalizedScopedDrawingRouteWireFormula_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (((scopedDrawingRouteWireFormula
      (PeriodicCNF.incidenceGraph formula)).map fun clause =>
        clause.rename
          (@planarSATCoreVariableMap Variable)).map
            periodicizePlanarSATClause).map
              PeriodicClause.anchorNormalize =
      normalizedEmbeddedRouteWireClauses formula := by
  unfold scopedDrawingRouteWireFormula
    drawingRouteWireFormula
    drawingCompleteCarrierFormula
    drawingRouteBendFormula
    normalizedEmbeddedRouteWireClauses
    embeddedNormalizedCompleteCarrierClauses
    embeddedNormalizedRouteBendClauses
    PeriodicEquality.normalizedFormulaClauses
  simp only [List.map_append, List.map_map]
  apply congrArg₂ (· ++ ·)
  · apply List.map_congr_left
    intro clause _clauseMem
    exact
      (congrArg
        (fun periodicClause =>
          PeriodicClause.anchorNormalize periodicClause)
        (periodicizePlanarSATClause_carrier_core_rename
          (Variable := Variable) clause)).trans
        (embedPeriodicCarrierClause_anchorNormalize
          (Variable := Variable)
          (PeriodicEquality.periodicizeClause
            normalizeCarrierNode clause)).symm
  · apply List.map_congr_left
    intro clause _clauseMem
    exact
      (congrArg
        (fun periodicClause =>
          PeriodicClause.anchorNormalize periodicClause)
        (periodicizePlanarSATClause_carrier_core_rename
          (Variable := Variable) clause)).trans
        (embedPeriodicCarrierClause_anchorNormalize
          (Variable := Variable)
          (PeriodicEquality.periodicizeClause
            normalizeCarrierNode clause)).symm

theorem normalizedScopedDrawingPlanarSATCoreClauses_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    normalizedScopedDrawingPlanarSATCoreClauses formula =
      normalizedScopedDrawingCrossoverClauses formula ++
        normalizedEmbeddedRouteWireClauses formula := by
  unfold normalizedScopedDrawingPlanarSATCoreClauses
    scopedDrawingPlanarSATCore
    drawingRoutePlanarCoreFormula
    normalizedScopedDrawingCrossoverClauses
  simp only [List.map_append]
  apply congrArg₂ (· ++ ·)
  · rfl
  · exact normalizedScopedDrawingRouteWireFormula_eq formula

theorem periodicCarrierLiteralToPlanarSAT_injective
    {Variable : Type*} :
    Function.Injective
      (fun literal : PeriodicLiteral PeriodicCarrierNode =>
        (⟨periodicCarrierNodeToPlanarSATVariable literal.atom,
          literal.offset, literal.value⟩ :
          PeriodicLiteral
            (PeriodicPlanarSATVariable Variable))) := by
  intro first second equal
  rcases first with ⟨firstAtom, firstOffset, firstValue⟩
  rcases second with ⟨secondAtom, secondOffset, secondValue⟩
  simp only [PeriodicLiteral.mk.injEq] at equal ⊢
  exact
    ⟨periodicCarrierNodeToPlanarSATVariable_injective
        equal.1,
      equal.2⟩

theorem embedPeriodicCarrierClause_injective
    {Variable : Type*} :
    Function.Injective
      (@embedPeriodicCarrierClause Variable) := by
  exact
    (@periodicCarrierLiteralToPlanarSAT_injective
      Variable).list_map

def normalizedDrawingPlanarSATComponents
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List
      (List
        (PeriodicClause
          (PeriodicPlanarSATVariable Variable))) :=
  [normalizedScopedDrawingCrossoverClauses formula,
    embeddedNormalizedCompleteCarrierClauses formula,
    embeddedNormalizedRouteBendClauses formula,
    normalizedRoutedClauseClauses formula,
    PeriodicEquality.normalizedFormulaClauses
      normalizePlanarSATNode
      (drawingRoutedVariableLinks formula)]

theorem drawingPeriodicPlanarSATFormula_anchorNormalize_components
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingPeriodicPlanarSATFormula
      formula).anchorNormalize.clauses =
      (normalizedDrawingPlanarSATComponents
        formula).flatten := by
  rw [
    drawingPeriodicPlanarSATFormula_anchorNormalize_clauses,
    normalizedScopedDrawingPlanarSATCoreClauses_eq]
  unfold normalizedDrawingPlanarSATComponents
    normalizedEmbeddedRouteWireClauses
  simp only [List.flatten_cons, List.flatten_nil,
    List.append_nil, List.append_assoc]

theorem drawingPeriodicPlanarSATFormula_anchorNormalize_five_components
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingPeriodicPlanarSATFormula
      formula).anchorNormalize.clauses =
      normalizedScopedDrawingCrossoverClauses formula ++
        (embeddedNormalizedCompleteCarrierClauses formula ++
          (embeddedNormalizedRouteBendClauses formula ++
            (normalizedRoutedClauseClauses formula ++
              PeriodicEquality.normalizedFormulaClauses
                normalizePlanarSATNode
                (drawingRoutedVariableLinks formula)))) := by
  rw [
    drawingPeriodicPlanarSATFormula_anchorNormalize_clauses,
    normalizedScopedDrawingPlanarSATCoreClauses_eq]
  unfold normalizedEmbeddedRouteWireClauses
  simp only [List.append_assoc]

theorem List.dedup_five_append_sublist
    {Value : Type*} [DecidableEq Value]
    (first second third fourth fifth : List Value) :
    List.Sublist
      (first ++ (second ++ (third ++ (fourth ++ fifth)))).dedup
      (first.dedup ++
        (second.dedup ++
          (third.dedup ++
            (fourth.dedup ++ fifth.dedup)))) := by
  have fourthFifth :=
    List.dedup_append_sublist_dedup_append fourth fifth
  have thirdTail :=
    (List.dedup_append_sublist_dedup_append
      third (fourth ++ fifth)).trans
      ((List.Sublist.refl third.dedup).append fourthFifth)
  have secondTail :=
    (List.dedup_append_sublist_dedup_append
      second (third ++ (fourth ++ fifth))).trans
      ((List.Sublist.refl second.dedup).append thirdTail)
  exact
    (List.dedup_append_sublist_dedup_append
      first
        (second ++ (third ++ (fourth ++ fifth)))).trans
      ((List.Sublist.refl first.dedup).append secondTail)

theorem PeriodicCNF.deduplicate_five_components_variableOccurrences_sublist
    {Variable : Type*} [DecidableEq Variable]
    (first second third fourth fifth :
      List (PeriodicClause Variable)) :
    List.Sublist
      (PeriodicCNF.variableOccurrences
        ⟨(first ++
          (second ++
            (third ++
              (fourth ++ fifth)))).dedup⟩)
      (PeriodicCNF.variableOccurrences
        ⟨first.dedup ++
          (second.dedup ++
            (third.dedup ++
              (fourth.dedup ++ fifth.dedup)))⟩) := by
  unfold PeriodicCNF.variableOccurrences
  exact
    (List.dedup_five_append_sublist
      first second third fourth fifth).flatMap
        (fun clause => clause.map PeriodicLiteral.atom)

/-- The normalized drawing formula with each geometric component
deduplicated separately before concatenation. -/
def componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicCNF (PeriodicPlanarSATVariable Variable) :=
  ⟨(normalizedScopedDrawingCrossoverClauses formula).dedup ++
    ((embeddedNormalizedCompleteCarrierClauses formula).dedup ++
      ((embeddedNormalizedRouteBendClauses formula).dedup ++
        ((normalizedRoutedClauseClauses formula).dedup ++
          (PeriodicEquality.normalizedFormulaClauses
            normalizePlanarSATNode
            (drawingRoutedVariableLinks formula)).dedup)))⟩

theorem PeriodicCNF.five_component_occurrence_count
    {Variable : Type*} [DecidableEq Variable]
    (first second third fourth fifth :
      List (PeriodicClause Variable))
    (atom : Variable) :
    (PeriodicCNF.variableOccurrences
      ⟨first ++
        (second ++
          (third ++
            (fourth ++ fifth)))⟩).count atom =
      (PeriodicCNF.variableOccurrences ⟨first⟩).count atom +
        ((PeriodicCNF.variableOccurrences ⟨second⟩).count atom +
          ((PeriodicCNF.variableOccurrences ⟨third⟩).count atom +
            ((PeriodicCNF.variableOccurrences ⟨fourth⟩).count atom +
              (PeriodicCNF.variableOccurrences
                ⟨fifth⟩).count atom))) := by
  simp [PeriodicCNF.variableOccurrences,
    List.flatMap_append, List.count_append]

theorem
    componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula_occurrence_count
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : PeriodicPlanarSATVariable Variable) :
    (componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula
      formula).variableOccurrences.count atom =
      (PeriodicCNF.variableOccurrences
        ⟨(normalizedScopedDrawingCrossoverClauses
          formula).dedup⟩).count atom +
      ((PeriodicCNF.variableOccurrences
        ⟨(embeddedNormalizedCompleteCarrierClauses
          formula).dedup⟩).count atom +
      ((PeriodicCNF.variableOccurrences
        ⟨(embeddedNormalizedRouteBendClauses
          formula).dedup⟩).count atom +
      ((PeriodicCNF.variableOccurrences
        ⟨(normalizedRoutedClauseClauses
          formula).dedup⟩).count atom +
      (PeriodicCNF.variableOccurrences
        ⟨(PeriodicEquality.normalizedFormulaClauses
          normalizePlanarSATNode
          (drawingRoutedVariableLinks formula)).dedup⟩).count atom))) := by
  unfold componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula
  exact
    PeriodicCNF.five_component_occurrence_count
      (normalizedScopedDrawingCrossoverClauses formula).dedup
      (embeddedNormalizedCompleteCarrierClauses formula).dedup
      (embeddedNormalizedRouteBendClauses formula).dedup
      (normalizedRoutedClauseClauses formula).dedup
      (PeriodicEquality.normalizedFormulaClauses
        normalizePlanarSATNode
        (drawingRoutedVariableLinks formula)).dedup
      atom

theorem
    componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula_atom_occurrence_count
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : Variable) :
    (componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula
      formula).variableOccurrences.count (.atom atom) =
      (PeriodicCNF.variableOccurrences
        ⟨(normalizedScopedDrawingCrossoverClauses
          formula).dedup⟩).count (.atom atom) +
      ((PeriodicCNF.variableOccurrences
        ⟨(embeddedNormalizedCompleteCarrierClauses
          formula).dedup⟩).count (.atom atom) +
      ((PeriodicCNF.variableOccurrences
        ⟨(embeddedNormalizedRouteBendClauses
          formula).dedup⟩).count (.atom atom) +
      ((PeriodicCNF.variableOccurrences
        ⟨(normalizedRoutedClauseClauses
          formula).dedup⟩).count (.atom atom) +
      (PeriodicCNF.variableOccurrences
        ⟨(PeriodicEquality.normalizedFormulaClauses
          normalizePlanarSATNode
          (drawingRoutedVariableLinks formula)).dedup⟩).count
            (.atom atom)))) :=
  componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula_occurrence_count
    formula (.atom atom)

theorem
    componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula_terminal_occurrence_count
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (indexed : IndexedGridSegment) (endpoint : SegmentEnd) :
    (componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula
      formula).variableOccurrences.count
        (.terminal indexed endpoint) =
      (PeriodicCNF.variableOccurrences
        ⟨(normalizedScopedDrawingCrossoverClauses
          formula).dedup⟩).count (.terminal indexed endpoint) +
      ((PeriodicCNF.variableOccurrences
        ⟨(embeddedNormalizedCompleteCarrierClauses
          formula).dedup⟩).count (.terminal indexed endpoint) +
      ((PeriodicCNF.variableOccurrences
        ⟨(embeddedNormalizedRouteBendClauses
          formula).dedup⟩).count (.terminal indexed endpoint) +
      ((PeriodicCNF.variableOccurrences
        ⟨(normalizedRoutedClauseClauses
          formula).dedup⟩).count (.terminal indexed endpoint) +
      (PeriodicCNF.variableOccurrences
        ⟨(PeriodicEquality.normalizedFormulaClauses
          normalizePlanarSATNode
          (drawingRoutedVariableLinks formula)).dedup⟩).count
            (.terminal indexed endpoint)))) :=
  componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula_occurrence_count
    formula (.terminal indexed endpoint)

theorem
    deduplicatedDrawingPeriodicPlanarSATFormula_variableOccurrences_sublist
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List.Sublist
      (deduplicatedDrawingPeriodicPlanarSATFormula
        formula).variableOccurrences
      (componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula
        formula).variableOccurrences := by
  unfold deduplicatedDrawingPeriodicPlanarSATFormula
    componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula
  unfold PeriodicCNF.deduplicate
  rw [
    drawingPeriodicPlanarSATFormula_anchorNormalize_five_components]
  exact
    PeriodicCNF.deduplicate_five_components_variableOccurrences_sublist
      (normalizedScopedDrawingCrossoverClauses formula)
      (embeddedNormalizedCompleteCarrierClauses formula)
      (embeddedNormalizedRouteBendClauses formula)
      (normalizedRoutedClauseClauses formula)
      (PeriodicEquality.normalizedFormulaClauses
        normalizePlanarSATNode
        (drawingRoutedVariableLinks formula))

end PeriodicOrthocrossing
end LeanTrominoes
