/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalFallbackMacrocellSeparation
import LeanTrominoes.RetainedFinalRouteMacrocellBounds

/-!
# Shape classification for arbitrary final macrocell occurrences

The earlier flat wrappers package the occurrence at external shift zero.
Periodic copied-source separation needs the same component classification at
an arbitrary relative shift.  This file records the shift-parametric wrapper,
transfers directness across equal physical macrocell centers, and rules out an
equal-center failed/successful selector pair.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- A final route occurrence, at an arbitrary quotient shift, whose physical
source component advertises a planar-SAT macrocell center. -/
structure FinalGaugedRouteMacrocellOccurrenceWitness
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (shift : Cell)
    extends
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex shift where
  center : Cell
  centerEq :
    toFinalGaugedRouteOccurrenceWitness.metadata.source.component.macrocellCenter
        formula =
      some center

/-- Every noncarrier final route occurrence has a macrocell package. -/
theorem
    FinalGaugedRouteOccurrenceWitness.exists_macrocellOccurrenceWitness_of_not_carrier
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex shift)
    (notCarrier :
      ¬∃ link,
        witness.metadata.source.component = .carrier link) :
    Nonempty
      (FinalGaugedRouteMacrocellOccurrenceWitness
        formula clauseIndex literalIndex shift) := by
  rcases
      witness.metadata.source.component
        |>.exists_macrocellCenter_of_not_carrier
          formula notCarrier with
    ⟨center, centerEq⟩
  exact ⟨{
    toFinalGaugedRouteOccurrenceWitness := witness
    center := center
    centerEq := centerEq
  }⟩

/-- Physical macrocell center of a shift-parametric final occurrence. -/
def FinalGaugedRouteMacrocellOccurrenceWitness.translatedCenter
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (witness :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula clauseIndex literalIndex shift) :
    Cell :=
  witness.toFinalGaugedRouteOccurrenceWitness
    |>.translatedMacrocellCenter witness.center

/-- Equal physical centers transfer direct-component classification between
arbitrarily shifted noncarrier occurrences. -/
theorem
    FinalGaugedRouteMacrocellOccurrenceWitness.first_component_isDirect_of_translatedCenters_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex : Nat}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula firstClauseIndex firstLiteralIndex firstShift)
    (second :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula secondClauseIndex secondLiteralIndex secondShift)
    (centersEqual :
      first.translatedCenter = second.translatedCenter)
    (secondDirect :
      second.metadata.source.component.IsDirect) :
    first.metadata.source.component.IsDirect := by
  let reindexShift :=
    Cell.sub first.physicalShift second.physicalShift
  have relativeCentersEqual :
      Cell.add first.center
          ((drawing formula.incidenceGraph).periodTranslation
            reindexShift) =
        second.center := by
    rcases firstCenterValue : first.center with
      ⟨firstX, firstY⟩
    rcases secondCenterValue : second.center with
      ⟨secondX, secondY⟩
    rcases firstShiftEq : first.physicalShift with
      ⟨firstShiftX, firstShiftY⟩
    rcases secondShiftEq : second.physicalShift with
      ⟨secondShiftX, secondShiftY⟩
    simp [FinalGaugedRouteMacrocellOccurrenceWitness.translatedCenter,
      FinalGaugedRouteOccurrenceWitness.translatedMacrocellCenter,
      reindexShift, PeriodicGridDrawing.periodTranslation,
      firstCenterValue, secondCenterValue,
      firstShiftEq, secondShiftEq,
      Cell.add, Cell.sub, Cell.scale] at centersEqual ⊢
    ring_nf at centersEqual ⊢
    omega
  have firstTranslatedCenterEq :
      ((first.metadata.source.periodTranslate
          formula reindexShift).component
        |>.macrocellCenter formula) =
        some second.center := by
    rw [DrawingPlanarSATClauseSource.component_periodTranslate,
      DrawingPlanarSATComponent.macrocellCenter_periodTranslate,
      first.centerEq]
    exact congrArg some relativeCentersEqual
  have classification :=
    retainedNoncarrierComponents_periodTranslate_eq_or_routedVariable_of_center_eq
      formula wellFormed degree isLocal
      first.metadata second.metadata
      first.metadata_retainedValid
      second.metadata_retainedValid
      reindexShift second.center
      firstTranslatedCenterEq second.centerEq
  have translatedDirect :
      (first.metadata.source.periodTranslate
        formula reindexShift).component.IsDirect := by
    rcases classification with componentAlignment | exception
    · rw [← componentAlignment]
      exact secondDirect
    · rcases exception with
        ⟨site, firstArm, firstLink, secondArm, secondLink,
          firstComponentEq, secondComponentEq⟩
      rw [firstComponentEq]
      trivial
  exact
    (DrawingPlanarSATClauseSource.component_periodTranslate_isDirect_iff
      formula first.metadata.source reindexShift).mp translatedDirect

/-- A failed selector cannot occupy the physical macrocell center of an
arbitrarily shifted occurrence already known to come from a direct family. -/
theorem
    FinalGaugedRouteMacrocellOccurrenceWitness.translatedCenter_ne_of_choice_none_of_second_component_isDirect
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {failedClauseIndex failedLiteralIndex
      referenceClauseIndex referenceLiteralIndex : Nat}
    {failedShift referenceShift : Cell}
    (failed :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula failedClauseIndex failedLiteralIndex failedShift)
    (reference :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula referenceClauseIndex referenceLiteralIndex referenceShift)
    (choiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula failedClauseIndex failedLiteralIndex = none)
    (referenceDirect :
      reference.metadata.source.component.IsDirect) :
    failed.translatedCenter ≠ reference.translatedCenter := by
  intro centersEqual
  have failedDirect :=
    failed.first_component_isDirect_of_translatedCenters_eq
      formula wellFormed degree isLocal
      reference centersEqual referenceDirect
  have directCases :
      (∃ crossing localClauseIndex,
          failed.metadata.source =
            .crossover crossing localClauseIndex) ∨
        (∃ site,
          failed.metadata.source = .routedClause site) ∨
        (∃ site armIndex arm link localClauseIndex,
          failed.metadata.source =
            .routedVariable
              site armIndex arm link localClauseIndex) := by
    cases sourceEq : failed.metadata.source with
    | crossover crossing localClauseIndex =>
        exact Or.inl ⟨crossing, localClauseIndex, rfl⟩
    | carrier link localClauseIndex =>
        rw [sourceEq] at failedDirect
        simp [DrawingPlanarSATClauseSource.component,
          DrawingPlanarSATComponent.IsDirect] at failedDirect
    | bend routeBend localClauseIndex =>
        rw [sourceEq] at failedDirect
        simp [DrawingPlanarSATClauseSource.component,
          DrawingPlanarSATComponent.IsDirect] at failedDirect
    | routedClause site =>
        exact Or.inr (Or.inl ⟨site, rfl⟩)
    | routedVariable site armIndex arm link localClauseIndex =>
        exact Or.inr (Or.inr
          ⟨site, armIndex, arm, link, localClauseIndex, rfl⟩)
  let failedWitness :=
    failed.toFinalGaugedRouteOccurrenceWitness
  have failedWitnessDirectCases :
      (∃ crossing localClauseIndex,
          failedWitness.metadata.source =
            .crossover crossing localClauseIndex) ∨
        (∃ site,
          failedWitness.metadata.source = .routedClause site) ∨
        (∃ site armIndex arm link localClauseIndex,
          failedWitness.metadata.source =
            .routedVariable
              site armIndex arm link localClauseIndex) := by
    simpa only [failedWitness] using directCases
  rcases
      exists_finalDirectSourceRouteChoice_of_witness_directCases
        formula failedWitness failedWitnessDirectCases with
    ⟨choice, choiceSome⟩
  rw [choiceNone] at choiceSome
  cases choiceSome

/-- In particular, a failed macrocell occurrence and a successfully selected
macrocell occurrence always have distinct physical centers. -/
theorem
    FinalGaugedRouteMacrocellOccurrenceWitness.translatedCenter_ne_of_choice_none_of_second_choice_some
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {failedClauseIndex failedLiteralIndex
      referenceClauseIndex referenceLiteralIndex : Nat}
    {failedShift referenceShift : Cell}
    (failed :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula failedClauseIndex failedLiteralIndex failedShift)
    (reference :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula referenceClauseIndex referenceLiteralIndex referenceShift)
    (choiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula failedClauseIndex failedLiteralIndex = none)
    (choice : RetainedDirectSourceRouteChoice)
    (choiceSome :
      retainedFinalDirectSourceRouteChoice?
          formula referenceClauseIndex referenceLiteralIndex = some choice) :
    failed.translatedCenter ≠ reference.translatedCenter := by
  exact
    failed.translatedCenter_ne_of_choice_none_of_second_component_isDirect
      formula wellFormed degree isLocal reference choiceNone
      (reference.toFinalGaugedRouteOccurrenceWitness
        |>.componentIsDirect_of_finalChoiceSome
          formula choice choiceSome)

end PeriodicOrthocrossing
end LeanTrominoes
