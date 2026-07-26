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
            (normalizePlanarSATVariable inputVariable).1) := by
  simp [drawingPeriodicPlanarSATFormula,
    PeriodicCNF.variableOccurrences,
    periodicizePlanarSATClause,
    periodicizePlanarSATLiteral,
    embeddedVariableOccurrences,
    List.flatMap_map, List.map_flatMap,
    List.map_map, Function.comp_def]

theorem normalizePlanarSATVariable_fst_eq_boundary_iff
    {Variable : Type*}
    (inputVariable : PlanarSATVariable Variable)
    (boundary : CrossingBoundary) :
    (normalizePlanarSATVariable inputVariable).1 = .boundary boundary ↔
      inputVariable = .inl (.carrier (.boundary boundary)) := by
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
    {Variable : Type*}
    (inputVariable : PlanarSATVariable Variable)
    (internal : CrossingRecord × CrossoverInternal) :
    (normalizePlanarSATVariable inputVariable).1 =
        .crossoverInternal internal ↔
      inputVariable = .inr internal := by
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

theorem drawingPeriodicPlanarSATFormula_boundary_count_le_eight
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (occurrences : formula.OccurrencesAtMost 3)
    (boundary : CrossingBoundary) :
    (drawingPeriodicPlanarSATFormula
      formula).variableOccurrences.count (.boundary boundary) ≤ 8 := by
  rw [drawingPeriodicPlanarSATFormula_variableOccurrences]
  rw [List.count_map_eq_count_of_fiber
    (embeddedVariableOccurrences
      (drawingPlanarSATFormula formula))
    (fun inputVariable =>
      (normalizePlanarSATVariable inputVariable).1)
    (.inl (.carrier (.boundary boundary)))
    (.boundary boundary)
    (fun inputVariable =>
      normalizePlanarSATVariable_fst_eq_boundary_iff
        inputVariable boundary)]
  exact drawingPlanarSATFormula_occurrencesAtMostEight
    formula occurrences (.inl (.carrier (.boundary boundary)))

theorem drawingPeriodicPlanarSATFormula_crossoverInternal_count_le_eight
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (occurrences : formula.OccurrencesAtMost 3)
    (internal : CrossingRecord × CrossoverInternal) :
    (drawingPeriodicPlanarSATFormula
      formula).variableOccurrences.count
        (.crossoverInternal internal) ≤ 8 := by
  rw [drawingPeriodicPlanarSATFormula_variableOccurrences]
  rw [List.count_map_eq_count_of_fiber
    (embeddedVariableOccurrences
      (drawingPlanarSATFormula formula))
    (fun inputVariable =>
      (normalizePlanarSATVariable inputVariable).1)
    (.inr internal)
    (.crossoverInternal internal)
    (fun inputVariable =>
      normalizePlanarSATVariable_fst_eq_crossoverInternal_iff
        inputVariable internal)]
  exact drawingPlanarSATFormula_occurrencesAtMostEight
    formula occurrences (.inr internal)

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

theorem
    deduplicatedWrappedDrawingPeriodicPlanarSATFormula_boundary_count_le_eight
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (occurrences : formula.OccurrencesAtMost 3)
    (boundary : CrossingBoundary) :
    (deduplicatedWrappedDrawingPeriodicPlanarSATFormula
      formula).variableOccurrences.count ⟨.boundary boundary⟩ ≤ 8 :=
  deduplicatedWrappedDrawingPeriodicPlanarSATFormula_count_le_of
    formula (.boundary boundary) 8
      (drawingPeriodicPlanarSATFormula_boundary_count_le_eight
        occurrences boundary)

theorem
    deduplicatedWrappedDrawingPeriodicPlanarSATFormula_crossoverInternal_count_le_eight
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (occurrences : formula.OccurrencesAtMost 3)
    (internal : CrossingRecord × CrossoverInternal) :
    (deduplicatedWrappedDrawingPeriodicPlanarSATFormula
      formula).variableOccurrences.count
        ⟨.crossoverInternal internal⟩ ≤ 8 :=
  deduplicatedWrappedDrawingPeriodicPlanarSATFormula_count_le_of
    formula (.crossoverInternal internal) 8
      (drawingPeriodicPlanarSATFormula_crossoverInternal_count_le_eight
        occurrences internal)

end PeriodicOrthocrossing
end LeanTrominoes
