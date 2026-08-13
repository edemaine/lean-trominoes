/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarAtomNormalizationDegree
import LeanTrominoes.PeriodicCNFPlanarSATDeduplication

/-!
# Periodic crossover-variable occurrence bounds

Crossover boundaries and internal variables have zero normalization offset
and unique finite-variable preimages.  Their finite degree-eight bounds
therefore survive periodicization, anchor normalization, opaque wrapping,
and clause deduplication.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

theorem drawingPeriodicPlanarSATFormula_variableOccurrences
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingPeriodicPlanarSATFormula formula).variableOccurrences =
    (embeddedVariableOccurrences
        (drawingPlanarSATFormula formula)).map
          (fun inputVariable =>
            (normalizePlanarSATVariable formula inputVariable).1) := by
  simp [drawingPeriodicPlanarSATFormula,
    PeriodicCNF.variableOccurrences,
    periodicizePlanarSATClause,
    periodicizePlanarSATLiteral,
    embeddedVariableOccurrences,
    List.flatMap_map, List.map_flatMap,
    List.map_map, Function.comp_def]

theorem normalizePlanarSATVariable_fst_eq_boundary_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (inputVariable : PlanarSATVariable Variable)
    (boundary : CrossingBoundary) :
    (normalizePlanarSATVariable formula inputVariable).1 =
        .boundary boundary ↔
      ∃ sourceBoundary,
        inputVariable =
          .inl (.carrier (.boundary sourceBoundary)) ∧
        sourceBoundary.periodNormalize
          (PeriodicCNF.incidenceGraph formula) = boundary := by
  cases inputVariable with
  | inl node =>
      cases node with
      | carrier carrier =>
          cases carrier <;>
            simp [normalizePlanarSATVariable]
      | atom atom =>
          simp [normalizePlanarSATVariable]
  | inr internal =>
      simp [normalizePlanarSATVariable]

theorem normalizePlanarSATVariable_fst_eq_crossoverInternal_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (inputVariable : PlanarSATVariable Variable)
    (internal : CrossingRecord × CrossoverInternal) :
    (normalizePlanarSATVariable formula inputVariable).1 =
        .crossoverInternal internal ↔
      ∃ sourceInternal,
        inputVariable = .inr sourceInternal ∧
        (sourceInternal.1.periodNormalize
          (PeriodicCNF.incidenceGraph formula),
            sourceInternal.2) = internal := by
  cases inputVariable with
  | inl node =>
      cases node with
      | carrier carrier =>
          cases carrier <;>
            simp [normalizePlanarSATVariable]
      | atom atom =>
          simp [normalizePlanarSATVariable]
  | inr other =>
      simp [normalizePlanarSATVariable]

/-- The canonical periodic atom named by one role of one crossover
template.  The crossing argument is already the canonical site key; all
literal offsets are zero after clause-anchor normalization. -/
def normalizedCrossoverAtom
    {Variable : Type*}
    (crossing : CrossingRecord) :
    CrossoverVariable → PeriodicPlanarSATVariable Variable
  | .aLeft => .boundary ⟨crossing, .left⟩
  | .aRight => .boundary ⟨crossing, .right⟩
  | .bTop => .boundary ⟨crossing, .top⟩
  | .bBottom => .boundary ⟨crossing, .bottom⟩
  | .aInnerLeft =>
      .crossoverInternal (crossing, .aInnerLeft)
  | .upperLeft =>
      .crossoverInternal (crossing, .upperLeft)
  | .lowerLeft =>
      .crossoverInternal (crossing, .lowerLeft)
  | .bInnerTop =>
      .crossoverInternal (crossing, .bInnerTop)
  | .center =>
      .crossoverInternal (crossing, .center)
  | .bInnerBottom =>
      .crossoverInternal (crossing, .bInnerBottom)
  | .upperRight =>
      .crossoverInternal (crossing, .upperRight)
  | .lowerRight =>
      .crossoverInternal (crossing, .lowerRight)
  | .aInnerRight =>
      .crossoverInternal (crossing, .aInnerRight)

theorem normalizedCrossoverAtom_jointly_injective
    {Variable : Type*} :
    Function.Injective
      (fun pair : CrossingRecord × CrossoverVariable =>
        (@normalizedCrossoverAtom Variable pair.1 pair.2)) := by
  rintro ⟨firstSite, firstVariable⟩
    ⟨secondSite, secondVariable⟩ equal
  cases firstVariable <;>
    cases secondVariable <;>
      simp [normalizedCrossoverAtom] at equal ⊢
  all_goals exact equal

theorem normalize_scopedCrossoverVariable
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (crossing : CrossingRecord)
    (source : CrossoverVariable) :
    normalizePlanarSATVariable formula
        (planarSATCoreVariableMap
          (scopedCrossoverVariableMap crossing
            (carrierNodeCrossingPorts crossing) source)) =
      (normalizedCrossoverAtom
          (crossing.periodNormalize
            (PeriodicCNF.incidenceGraph formula)) source,
        crossingPeriodShift
          (PeriodicCNF.incidenceGraph formula) crossing) := by
  cases source <;>
    simp [scopedCrossoverVariableMap,
      carrierNodeCrossingPorts, planarSATCoreVariableMap,
      normalizePlanarSATVariable, normalizedCrossoverAtom,
      CrossingBoundary.periodNormalize]

/-- One crossover template clause after all variables have been reduced to
their canonical site and the common site shift has been removed. -/
def normalizedCrossoverClause
    {Variable : Type*}
    (crossing : CrossingRecord)
    (clause : EmbeddedClause CrossoverVariable) :
    PeriodicClause (PeriodicPlanarSATVariable Variable) :=
  clause.literals.map fun literal =>
    ⟨normalizedCrossoverAtom crossing literal.1,
      (0, 0), literal.2⟩

/-- The normalized Boolean clauses of one canonical crossover site. -/
def normalizedCrossoverClausesAt
    {Variable : Type*}
    (crossing : CrossingRecord) :
    List (PeriodicClause (PeriodicPlanarSATVariable Variable)) :=
  crossoverFormula.map
    (@normalizedCrossoverClause Variable crossing)

theorem PeriodicClause.anchorNormalize_uniform
    {Variable : Type*}
    (literals : List (Variable × Bool))
    (offset : Cell) :
    PeriodicClause.anchorNormalize
      (literals.map fun literal =>
        (⟨literal.1, offset, literal.2⟩ :
          PeriodicLiteral Variable)) =
      literals.map fun literal =>
        (⟨literal.1, (0, 0), literal.2⟩ :
          PeriodicLiteral Variable) := by
  cases literals with
  | nil =>
      rfl
  | cons first rest =>
      rcases offset with ⟨offsetX, offsetY⟩
      simp [PeriodicClause.anchorNormalize,
        PeriodicCNF.clauseAnchor,
        PeriodicLiteral.anchorNormalize,
        Cell.sub]

theorem normalizedCrossoverClauseAt_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (crossing : CrossingRecord)
    (clause : EmbeddedClause CrossoverVariable) :
    PeriodicClause.anchorNormalize
        (periodicizePlanarSATClause formula
          (((clause.rename
              (scopedCrossoverVariableMap crossing
                (carrierNodeCrossingPorts crossing))).place
              (crossingMacroOrigin crossing) 1).rename
            (@planarSATCoreVariableMap Variable))) =
      normalizedCrossoverClause
        (crossing.periodNormalize
          (PeriodicCNF.incidenceGraph formula)) clause := by
  have rawEq :
      periodicizePlanarSATClause formula
          (((clause.rename
              (scopedCrossoverVariableMap crossing
                (carrierNodeCrossingPorts crossing))).place
              (crossingMacroOrigin crossing) 1).rename
            (@planarSATCoreVariableMap Variable)) =
        clause.literals.map fun literal =>
          ⟨normalizedCrossoverAtom
              (crossing.periodNormalize
                (PeriodicCNF.incidenceGraph formula)) literal.1,
            crossingPeriodShift
              (PeriodicCNF.incidenceGraph formula) crossing,
            literal.2⟩ := by
    unfold periodicizePlanarSATClause
      periodicizePlanarSATLiteral
    simp only [EmbeddedClause.rename, EmbeddedClause.place,
      EmbeddedClause.map, List.map_map]
    apply List.map_congr_left
    intro literal _literalMem
    rcases literal with ⟨source, polarity⟩
    change
      (⟨(normalizePlanarSATVariable formula
          (planarSATCoreVariableMap
            (scopedCrossoverVariableMap crossing
              (carrierNodeCrossingPorts crossing) source))).1,
        (normalizePlanarSATVariable formula
          (planarSATCoreVariableMap
            (scopedCrossoverVariableMap crossing
              (carrierNodeCrossingPorts crossing) source))).2,
        polarity⟩ :
        PeriodicLiteral (PeriodicPlanarSATVariable Variable)) =
      (⟨normalizedCrossoverAtom
          (crossing.periodNormalize
            (PeriodicCNF.incidenceGraph formula)) source,
        crossingPeriodShift
          (PeriodicCNF.incidenceGraph formula) crossing,
        polarity⟩ :
        PeriodicLiteral (PeriodicPlanarSATVariable Variable))
    rw [normalize_scopedCrossoverVariable]
  rw [rawEq]
  simpa [normalizedCrossoverClause, List.map_map,
    Function.comp_def] using
      PeriodicClause.anchorNormalize_uniform
        (clause.literals.map fun literal =>
          (normalizedCrossoverAtom
            (crossing.periodNormalize
              (PeriodicCNF.incidenceGraph formula)) literal.1,
            literal.2))
        (crossingPeriodShift
          (PeriodicCNF.incidenceGraph formula) crossing)

/-- One canonical representative of every normalized crossover clause. -/
def canonicalNormalizedCrossoverClauses
    {Variable Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (PeriodicClause (PeriodicPlanarSATVariable Variable)) :=
  (orientedCrossings graph).flatMap
    (@normalizedCrossoverClausesAt Variable)

/-- An embedded presentation with the same variable occurrences as
`canonicalNormalizedCrossoverClauses`, used to reuse the generic finite
gadget-family occurrence theorem. -/
def canonicalNormalizedCrossoverEmbeddedFormula
    {Variable Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    List (EmbeddedClause (PeriodicPlanarSATVariable Variable)) :=
  (orientedCrossings graph).flatMap fun crossing =>
    instantiateFormula
      (@normalizedCrossoverAtom Variable crossing)
      (0, 0) 1 crossoverFormula

theorem canonicalNormalizedCrossover_variableOccurrences
    {Variable Vertex : Type*}
    [DecidableEq Variable] [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    (PeriodicCNF.variableOccurrences
      ⟨canonicalNormalizedCrossoverClauses
        (Variable := Variable) graph⟩) =
      embeddedVariableOccurrences
        (canonicalNormalizedCrossoverEmbeddedFormula
          (Variable := Variable) graph) := by
  unfold PeriodicCNF.variableOccurrences
    canonicalNormalizedCrossoverClauses
    canonicalNormalizedCrossoverEmbeddedFormula
    normalizedCrossoverClausesAt
    normalizedCrossoverClause
  rw [embeddedVariableOccurrences_flatMap]
  change
    (((orientedCrossings graph).flatMap fun crossing =>
      crossoverFormula.map fun clause =>
        clause.literals.map fun literal =>
          (⟨normalizedCrossoverAtom crossing literal.1,
            (0, 0), literal.2⟩ :
            PeriodicLiteral
              (PeriodicPlanarSATVariable Variable))).flatMap
        (fun clause => clause.map PeriodicLiteral.atom)) =
      (orientedCrossings graph).flatMap fun crossing =>
        embeddedVariableOccurrences
          (instantiateFormula
            (normalizedCrossoverAtom crossing)
            (0, 0) 1 crossoverFormula)
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro crossing _crossingMem
  rw [embeddedVariableOccurrences_instantiateFormula]
  simp [embeddedVariableOccurrences,
    List.flatMap_map, List.map_flatMap, List.map_map,
    Function.comp_def]

theorem canonicalNormalizedCrossoverClauses_occurrencesAtMostEight
    {Variable Vertex : Type*}
    [DecidableEq Variable] [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    (PeriodicCNF.mk
      (canonicalNormalizedCrossoverClauses
        (Variable := Variable) graph)).OccurrencesAtMost 8 := by
  intro atom
  rw [canonicalNormalizedCrossover_variableOccurrences]
  exact
    instantiateFamily_occurrencesAtMost_of_jointly_injective
      8 (orientedCrossings graph)
      (@normalizedCrossoverAtom Variable)
      (fun _ => (0, 0)) 1 crossoverFormula
      (orientedCrossings_nodup graph)
      normalizedCrossoverAtom_jointly_injective
      crossoverFormula_occurrencesAtMostEight atom

theorem canonicalNormalizedCrossoverClauses_boundary_count_le_two
    {Variable Vertex : Type*}
    [DecidableEq Variable] [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (boundary : CrossingBoundary) :
    (PeriodicCNF.variableOccurrences
      ⟨canonicalNormalizedCrossoverClauses
        (Variable := Variable) graph⟩).count
          (.boundary boundary) ≤ 2 := by
  rw [canonicalNormalizedCrossover_variableOccurrences]
  apply
    instantiateFamily_occurrence_count_le_of_jointly_injective
      2 (orientedCrossings graph)
      (@normalizedCrossoverAtom Variable)
      (fun _ => (0, 0)) 1 crossoverFormula
      (orientedCrossings_nodup graph)
      normalizedCrossoverAtom_jointly_injective
      (.boundary boundary)
  rintro ⟨site, source⟩ sourceEq
  apply crossoverFormula_boundary_count_le_two source
  cases source <;>
    simp [normalizedCrossoverAtom] at sourceEq ⊢

theorem List.count_map_eq_count_of_fiber
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    (values : List Source) (map : Source → Target)
    (source : Source) (target : Target)
    (fiber : ∀ value, map value = target ↔ value = source) :
    (values.map map).count target = values.count source := by
  induction values with
  | nil =>
      simp
  | cons value values induction =>
      by_cases valueEq : value = source
      · subst value
        have mappedEq : map source = target :=
          (fiber source).mpr rfl
        simp [mappedEq, induction]
      · have mappedNe : map value ≠ target := by
          intro mappedEq
          exact valueEq ((fiber value).mp mappedEq)
        simp [valueEq, mappedNe, induction]

theorem deduplicatedWrappedDrawingPeriodicPlanarSATFormula_count_le_of
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : PeriodicPlanarSATVariable Variable)
    (bound : Nat)
    (sourceLe :
      (drawingPeriodicPlanarSATFormula
        formula).variableOccurrences.count atom ≤ bound) :
    (deduplicatedWrappedDrawingPeriodicPlanarSATFormula
      formula).variableOccurrences.count ⟨atom⟩ ≤ bound := by
  unfold deduplicatedWrappedDrawingPeriodicPlanarSATFormula
  have dedupLe :=
    ((PeriodicCNF.deduplicate_variableOccurrences_sublist
      (wrappedDrawingPeriodicPlanarSATFormula
        formula).anchorNormalize).subperm.count_le
          (WrappedPeriodicVariable.mk atom))
  rw [PeriodicCNF.variableOccurrences_anchorNormalize,
    wrappedDrawingPeriodicPlanarSATFormula,
    wrapPeriodicPlanarSATFormula_variableOccurrences,
    List.count_map_of_injective
      (drawingPeriodicPlanarSATFormula formula).variableOccurrences
      WrappedPeriodicVariable.mk
      (fun first second equal =>
        congrArg WrappedPeriodicVariable.original equal)
      atom] at dedupLe
  exact dedupLe.trans sourceLe

end PeriodicOrthocrossing
end LeanTrominoes
