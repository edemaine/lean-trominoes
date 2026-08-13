/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedNormalizationDegree
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedNoncarrierClauseOrbits
import LeanTrominoes.EmbeddedCNFIncidenceDrawingRenaming

/-!
# Degree eight for the final gauged retained planar SAT formula

The component analysis bounds the globally deduplicated unwrapped retained
formula.  This file transports that bound through the three representation
changes used by the final positioned formula: opaque variable wrapping,
canonical per-variable gauging, and clause-anchor normalization.

The main bookkeeping point is that gauging followed by normalization is
injective on clauses that were already anchor-normalized.  Thus it commutes
with the finite first-occurrence deduplication used by the construction.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

namespace PeriodicClause

/-- Applying the pointwise negative gauge undoes a variable gauge exactly. -/
@[simp]
theorem variableGauge_inverse
    {Variable : Type*}
    (gauge : Variable → Cell)
  (clause : PeriodicClause Variable) :
    (clause.variableGauge gauge).variableGauge
        (fun atom => Cell.neg (gauge atom)) =
      clause := by
  induction clause with
  | nil =>
      rfl
  | cons literal rest induction =>
      simp only [PeriodicClause.variableGauge, List.map_cons]
      congr 1
      · rcases literal with ⟨atom, ⟨offsetX, offsetY⟩, value⟩
        rcases gauge atom with ⟨gaugeX, gaugeY⟩
        simp [PeriodicLiteral.variableGauge,
          Cell.add, Cell.neg, Cell.sub]

/-- Anchor normalization is idempotent. -/
@[simp]
theorem anchorNormalize_anchorNormalize
    {Variable : Type*}
    (clause : PeriodicClause Variable) :
    clause.anchorNormalize.anchorNormalize =
      clause.anchorNormalize := by
  cases clause with
  | nil =>
      rfl
  | cons first rest =>
      rcases first with ⟨atom, ⟨offsetX, offsetY⟩, value⟩
      simp [PeriodicClause.anchorNormalize, PeriodicCNF.clauseAnchor,
        PeriodicLiteral.anchorNormalize, List.map_map,
        Function.comp_def, Cell.sub]

end PeriodicClause

/-- Normalize a wrapped clause after applying an arbitrary variable gauge. -/
def gaugedWrappedNormalizedClause
    {Original : Type*}
    (gauge : WrappedPeriodicVariable Original → Cell)
    (clause : PeriodicClause Original) :
    PeriodicClause (WrappedPeriodicVariable Original) :=
  ((wrapPeriodicPlanarSATClause clause).variableGauge gauge).anchorNormalize

/-- Gauged wrapping cannot identify two clauses that were already
anchor-normalized. -/
theorem gaugedWrappedNormalizedClause_injective_of_normalized
    {Original : Type*}
    (gauge : WrappedPeriodicVariable Original → Cell)
    {first second : PeriodicClause Original}
    (firstNormalized : first.anchorNormalize = first)
    (secondNormalized : second.anchorNormalize = second)
    (equal :
      gaugedWrappedNormalizedClause gauge first =
        gaugedWrappedNormalizedClause gauge second) :
    first = second := by
  have inverseEqual :=
    variableGauge_anchorNormalize_eq_of_anchorNormalize_eq
      (fun atom => Cell.neg (gauge atom))
      equal
  simp only [PeriodicClause.variableGauge_inverse] at inverseEqual
  rw [← wrapPeriodicPlanarSATClause_anchorNormalize,
    ← wrapPeriodicPlanarSATClause_anchorNormalize,
    firstNormalized, secondNormalized] at inverseEqual
  exact wrapPeriodicPlanarSATClause_injective inverseEqual

/-- Normalizing after gauged wrapping depends only on the source clause's
anchor-normalized representative. -/
theorem gaugedWrappedNormalizedClause_anchorNormalize
    {Original : Type*}
    (gauge : WrappedPeriodicVariable Original → Cell)
    (clause : PeriodicClause Original) :
    gaugedWrappedNormalizedClause gauge clause.anchorNormalize =
      gaugedWrappedNormalizedClause gauge clause := by
  unfold gaugedWrappedNormalizedClause
  rw [wrapPeriodicPlanarSATClause_anchorNormalize]
  exact
    variableGauge_anchorNormalize_anchorNormalize
      gauge (wrapPeriodicPlanarSATClause clause)

/-- The gauged-wrapping map is injective on the finite list of normalized
source clauses. -/
theorem gaugedWrappedNormalizedClause_injectiveOn_anchorNormalize_clauses
    {Original : Type*}
    (source : PeriodicCNF Original)
    (gauge : WrappedPeriodicVariable Original → Cell) :
    ∀ first ∈ source.anchorNormalize.clauses,
      ∀ second ∈ source.anchorNormalize.clauses,
        gaugedWrappedNormalizedClause gauge first =
            gaugedWrappedNormalizedClause gauge second →
          first = second := by
  intro first firstMember second secondMember equal
  rcases List.mem_map.mp firstMember with
    ⟨firstSource, _firstSourceMember, firstEq⟩
  rcases List.mem_map.mp secondMember with
    ⟨secondSource, _secondSourceMember, secondEq⟩
  subst first
  subst second
  exact
    gaugedWrappedNormalizedClause_injective_of_normalized
      gauge
      (PeriodicClause.anchorNormalize_anchorNormalize firstSource)
      (PeriodicClause.anchorNormalize_anchorNormalize secondSource)
      equal

/-- The clause list obtained by wrapping, gauging, normalizing, and
deduplicating is the injective image of the unwrapped normalized,
deduplicated clause list. -/
theorem gaugedWrapped_deduplicate_clauses
    {Original : Type*} [DecidableEq Original]
    (source : PeriodicCNF Original)
    (gauge : WrappedPeriodicVariable Original → Cell) :
    (((wrapPeriodicPlanarSATFormula source).variableGauge
          gauge).anchorNormalize.deduplicate).clauses =
      source.anchorNormalize.deduplicate.clauses.map
        (gaugedWrappedNormalizedClause gauge) := by
  have beforeDeduplicate :
      (((wrapPeriodicPlanarSATFormula source).variableGauge
          gauge).anchorNormalize).clauses =
        source.anchorNormalize.clauses.map
          (gaugedWrappedNormalizedClause gauge) := by
    simp only [wrapPeriodicPlanarSATFormula,
      PeriodicCNF.variableGauge, PeriodicCNF.anchorNormalize,
      List.map_map]
    apply List.map_congr_left
    intro clause _clauseMember
    exact
      (gaugedWrappedNormalizedClause_anchorNormalize
        gauge clause).symm
  unfold PeriodicCNF.deduplicate
  rw [beforeDeduplicate]
  exact
    EmbeddedCNFIncidenceDrawing.dedup_map_of_injective_on
      (gaugedWrappedNormalizedClause gauge)
      source.anchorNormalize.clauses
      (gaugedWrappedNormalizedClause_injectiveOn_anchorNormalize_clauses
        source gauge)

/-- Gauged normalized wrapping changes only the type of each literal atom,
preserving clause and literal order. -/
@[simp]
theorem gaugedWrappedNormalizedClause_map_atom
    {Original : Type*}
    (gauge : WrappedPeriodicVariable Original → Cell)
    (clause : PeriodicClause Original) :
    (gaugedWrappedNormalizedClause gauge clause).map
        PeriodicLiteral.atom =
      (clause.map PeriodicLiteral.atom).map
        WrappedPeriodicVariable.mk := by
  simp [gaugedWrappedNormalizedClause,
    PeriodicClause.anchorNormalize,
    PeriodicClause.variableGauge,
    wrapPeriodicPlanarSATClause,
    wrapPeriodicPlanarSATLiteral,
    List.map_map, Function.comp_def]

/-- Wrapping, gauging, normalization, and deduplication preserve the ordered
occurrence list up to the opaque atom wrapper. -/
theorem gaugedWrapped_deduplicate_variableOccurrences
    {Original : Type*} [DecidableEq Original]
    (source : PeriodicCNF Original)
    (gauge : WrappedPeriodicVariable Original → Cell) :
    (((wrapPeriodicPlanarSATFormula source).variableGauge
          gauge).anchorNormalize.deduplicate).variableOccurrences =
      source.anchorNormalize.deduplicate.variableOccurrences.map
        WrappedPeriodicVariable.mk := by
  unfold PeriodicCNF.variableOccurrences
  rw [gaugedWrapped_deduplicate_clauses]
  simp [List.flatMap_map, List.map_flatMap]

/-- Erasing the final positioned retained formula exposes precisely the
semantic wrap-gauge-normalize-deduplicate pipeline. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).erase =
      (((wrapPeriodicPlanarSATFormula
          (retainedDrawingPeriodicPlanarSATFormula formula)).variableGauge
            (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
              formula)).anchorNormalize.deduplicate) := by
  rw [
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula,
    PositionedPeriodicCNF.erase_deduplicateByLiterals,
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula,
    PositionedPeriodicCNF.erase_anchorNormalize,
    retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula,
    PositionedPeriodicCNF.erase_variableGauge,
    retainedWrappedDrawingPositionedPeriodicPlanarSATFormula_erase]

/-- The final positioned formula has exactly the unwrapped normalized
occurrence list, with every atom placed behind the opaque wrapper. -/
@[simp]
theorem
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_variableOccurrences
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).erase.variableOccurrences =
      (retainedDeduplicatedDrawingPeriodicPlanarSATFormula
        formula).variableOccurrences.map
          WrappedPeriodicVariable.mk := by
  rw [
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_erase,
    gaugedWrapped_deduplicate_variableOccurrences]
  rfl

/-- Each wrapped atom has exactly the occurrence count of its unwrapped
routed-SAT prototype. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_count
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : PeriodicPlanarSATVariable Variable) :
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).erase.variableOccurrences.count ⟨atom⟩ =
      (retainedDeduplicatedDrawingPeriodicPlanarSATFormula
        formula).variableOccurrences.count atom := by
  rw [
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_variableOccurrences,
    List.count_map_of_injective
      (retainedDeduplicatedDrawingPeriodicPlanarSATFormula
        formula).variableOccurrences
      WrappedPeriodicVariable.mk
      (fun first second equal =>
        congrArg WrappedPeriodicVariable.original equal)
      atom]

/-- The final canonically gauged, anchor-normalized, and clause-deduplicated
retained planar-SAT formula has at most eight occurrences of every
protovariable. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_occurrencesAtMostEight
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (occurrences : formula.OccurrencesAtMost 3) :
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).erase.OccurrencesAtMost 8 := by
  rintro ⟨atom⟩
  rw [
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_count]
  exact
    retainedDeduplicatedDrawingPeriodicPlanarSATFormula_occurrencesAtMostEight
      wellFormed degree isLocal occurrences atom

end PeriodicOrthocrossing
end LeanTrominoes
