/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedFinalFlatAnchorNormalizedComponents

/-!
# Direct cases for anchor-normalized flat components

An oblique discarded terminal segment rules out the orthogonal bend family,
while the macrocell witness already rules out carriers.  Directness survives
the anchor-normalizing period translation, so the retained finite source
realizing the translated component must be a crossover, routed clause, or
routed variable.

The resulting source-level trichotomy keeps every constructor witness needed
by the finite retained-carrier proximity theorems.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Directness of a flat noncarrier component transfers to its retained
anchor-normalized source. -/
theorem
    FinalGaugedFlatNormalizedMacrocellSource.componentIsDirect
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {taggedRoute : List Cell × Nat}
    {macrocell :
      FinalGaugedFlatRouteMacrocellWitness
        formula taggedRoute}
    (normalized :
      FinalGaugedFlatNormalizedMacrocellSource
        formula macrocell)
    (direct :
      macrocell.routeWitness.metadata.source.component.IsDirect) :
    normalized.source.component.IsDirect := by
  rw [normalized.componentEq]
  exact
    (DrawingPlanarSATClauseSource.component_periodTranslate_isDirect_iff
      formula macrocell.routeWitness.metadata.source
      macrocell.routeWitness.physicalShift).mpr direct

/-- A direct normalized source is represented by exactly one of the three
two-point component constructors.  The source equality retains local clause
and routed-arm indices instead of forgetting them at component level. -/
theorem
    FinalGaugedFlatNormalizedMacrocellSource.directCases
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {taggedRoute : List Cell × Nat}
    {macrocell :
      FinalGaugedFlatRouteMacrocellWitness
        formula taggedRoute}
    (normalized :
      FinalGaugedFlatNormalizedMacrocellSource
        formula macrocell)
    (direct : normalized.source.component.IsDirect) :
    (∃ crossing localClauseIndex,
        normalized.source =
          .crossover crossing localClauseIndex) ∨
      (∃ site,
        normalized.source = .routedClause site) ∨
      (∃ site armIndex arm link localClauseIndex,
        normalized.source =
          .routedVariable
            site armIndex arm link localClauseIndex) := by
  cases sourceEq : normalized.source with
  | crossover crossing localClauseIndex =>
      exact Or.inl ⟨crossing, localClauseIndex, rfl⟩
  | carrier link localClauseIndex =>
      simp [sourceEq, DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.IsDirect] at direct
  | bend routeBend localClauseIndex =>
      simp [sourceEq, DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.IsDirect] at direct
  | routedClause site =>
      exact Or.inr (Or.inl ⟨site, rfl⟩)
  | routedVariable site armIndex arm link localClauseIndex =>
      exact Or.inr
        (Or.inr
          ⟨site, armIndex, arm, link,
            localClauseIndex, rfl⟩)

/-- An oblique final segment supplies the direct source-level trichotomy in
the anchor-normalized finite frame. -/
theorem
    FinalGaugedFlatNormalizedMacrocellSource.directCases_of_finalSegment_not_axisAligned
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {taggedRoute : List Cell × Nat}
    {macrocell :
      FinalGaugedFlatRouteMacrocellWitness
        formula taggedRoute}
    (normalized :
      FinalGaugedFlatNormalizedMacrocellSource
        formula macrocell)
    (routeLength : 2 ≤ taggedRoute.1.length)
    {target : Cell}
    (routeLast : taggedRoute.1.getLast? = some target)
    (finalSegmentNotAxisAligned :
      ¬(⟨polylineLastEntrance taggedRoute.1, target⟩ :
        GridSegment).IsAxisAligned) :
    (∃ crossing localClauseIndex,
        normalized.source =
          .crossover crossing localClauseIndex) ∨
      (∃ site,
        normalized.source = .routedClause site) ∨
      (∃ site armIndex arm link localClauseIndex,
        normalized.source =
          .routedVariable
            site armIndex arm link localClauseIndex) := by
  apply normalized.directCases
  apply normalized.componentIsDirect
  exact
    macrocell.component_isDirect_of_finalSegment_not_axisAligned
      formula wellFormed degree isLocal
      routeLength routeLast finalSegmentNotAxisAligned

end PeriodicOrthocrossing
end LeanTrominoes
