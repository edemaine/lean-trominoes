import LeanTrominoes.PeriodicCNFPlanarSATDeduplication

/-!
# Wrapping and deduplicating the periodic planar SAT formula

Opaque wrapping commutes with clause-anchor normalization and deduplication.
This module exposes an unwrapped semantic formula for occurrence accounting
and proves exact correspondence of its occurrence counts with the wrapped
formula used by the later reduction.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

theorem wrapPeriodicPlanarSATLiteral_injective
    {Original : Type*} :
    Function.Injective
      (@wrapPeriodicPlanarSATLiteral Original) := by
  intro first second equal
  rcases first with ⟨firstAtom, firstOffset, firstValue⟩
  rcases second with ⟨secondAtom, secondOffset, secondValue⟩
  simp [wrapPeriodicPlanarSATLiteral] at equal ⊢
  exact equal

theorem wrapPeriodicPlanarSATClause_injective
    {Original : Type*} :
    Function.Injective
      (@wrapPeriodicPlanarSATClause Original) := by
  exact wrapPeriodicPlanarSATLiteral_injective.list_map

@[simp]
theorem wrapPeriodicPlanarSATClause_anchorNormalize
    {Original : Type*}
    (clause : PeriodicClause Original) :
    wrapPeriodicPlanarSATClause clause.anchorNormalize =
      (wrapPeriodicPlanarSATClause clause).anchorNormalize := by
  cases clause with
  | nil =>
      rfl
  | cons first rest =>
      rcases first with ⟨atom, ⟨offsetX, offsetY⟩, value⟩
      simp [wrapPeriodicPlanarSATClause,
        wrapPeriodicPlanarSATLiteral,
        PeriodicClause.anchorNormalize,
        PeriodicLiteral.anchorNormalize,
        PeriodicCNF.clauseAnchor,
        List.map_map, Function.comp_def]

/-- Unwrapped semantic formula obtained by anchor-normalizing and
deduplicating the routed periodic formula. -/
def deduplicatedDrawingPeriodicPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicCNF (PeriodicPlanarSATVariable Variable) :=
  (drawingPeriodicPlanarSATFormula formula).anchorNormalize.deduplicate

theorem wrapPeriodicPlanarSATFormula_anchorNormalize
    {Original : Type*}
    (source : PeriodicCNF Original) :
    wrapPeriodicPlanarSATFormula source.anchorNormalize =
      (wrapPeriodicPlanarSATFormula source).anchorNormalize := by
  apply PeriodicCNF.equivData.injective
  simp [wrapPeriodicPlanarSATFormula,
    PeriodicCNF.anchorNormalize,
    wrapPeriodicPlanarSATClause_anchorNormalize]

theorem wrapPeriodicPlanarSATFormula_deduplicate
    {Original : Type*} [DecidableEq Original]
    (source : PeriodicCNF Original) :
    wrapPeriodicPlanarSATFormula source.deduplicate =
      (wrapPeriodicPlanarSATFormula source).deduplicate := by
  apply PeriodicCNF.equivData.injective
  simp [wrapPeriodicPlanarSATFormula,
    PeriodicCNF.deduplicate,
    List.dedup_map_of_injective
      wrapPeriodicPlanarSATClause_injective]

theorem
    deduplicatedWrappedDrawingPeriodicPlanarSATFormula_eq_wrap
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    deduplicatedWrappedDrawingPeriodicPlanarSATFormula formula =
      wrapPeriodicPlanarSATFormula
        (deduplicatedDrawingPeriodicPlanarSATFormula formula) := by
  unfold deduplicatedWrappedDrawingPeriodicPlanarSATFormula
    wrappedDrawingPeriodicPlanarSATFormula
    deduplicatedDrawingPeriodicPlanarSATFormula
  rw [← wrapPeriodicPlanarSATFormula_anchorNormalize,
    ← wrapPeriodicPlanarSATFormula_deduplicate]

@[simp]
theorem
    deduplicatedWrappedDrawingPeriodicPlanarSATFormula_variableOccurrences
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (deduplicatedWrappedDrawingPeriodicPlanarSATFormula
      formula).variableOccurrences =
      (deduplicatedDrawingPeriodicPlanarSATFormula
        formula).variableOccurrences.map
          WrappedPeriodicVariable.mk := by
  rw [deduplicatedWrappedDrawingPeriodicPlanarSATFormula_eq_wrap,
    wrapPeriodicPlanarSATFormula_variableOccurrences]

theorem
    deduplicatedWrappedDrawingPeriodicPlanarSATFormula_count
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : PeriodicPlanarSATVariable Variable) :
    (deduplicatedWrappedDrawingPeriodicPlanarSATFormula
      formula).variableOccurrences.count ⟨atom⟩ =
      (deduplicatedDrawingPeriodicPlanarSATFormula
        formula).variableOccurrences.count atom := by
  rw [
    deduplicatedWrappedDrawingPeriodicPlanarSATFormula_variableOccurrences,
    List.count_map_of_injective
      (deduplicatedDrawingPeriodicPlanarSATFormula
        formula).variableOccurrences
      WrappedPeriodicVariable.mk
      (fun first second equal =>
        congrArg WrappedPeriodicVariable.original equal)
      atom]

end PeriodicOrthocrossing
end LeanTrominoes
