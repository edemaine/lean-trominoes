/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierAnchorGeometry

/-!
# Carrier ownership in the periodic reindexing API

The retained carrier family selects exactly one zero-owner link from each
periodic orbit.  This module exposes the resulting rigidity in the language
used by final segment reindexing: a selected carrier source satisfies its
retained-orbit condition exactly at translation zero.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- A selected carrier link can be translated to another selected carrier
link exactly by the zero lattice translation. -/
theorem carrierLinkPeriodTranslate_mem_iff_shift_eq_zero
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {link : EqualityLink CarrierNode}
    (linkMember :
      link ∈ retainedDrawingCompleteCarrierLinks graph)
    (shift : Cell) :
    carrierLinkPeriodTranslate graph link shift ∈
        retainedDrawingCompleteCarrierLinks graph ↔
      shift = (0, 0) := by
  constructor
  · intro translatedMember
    have sourceRepresentative :=
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        graph link).mp linkMember).2
    have targetRepresentative :=
      ((mem_retainedDrawingCompleteCarrierLinks_iff
        graph (carrierLinkPeriodTranslate graph link shift)).mp
          translatedMember).2
    change
      carrierLinkRepresentativeShift graph link = (0, 0)
      at sourceRepresentative
    change
      carrierLinkRepresentativeShift graph
          (carrierLinkPeriodTranslate graph link shift) =
        (0, 0)
      at targetRepresentative
    rw [carrierLinkRepresentativeShift_periodTranslate,
      sourceRepresentative] at targetRepresentative
    rcases shift with ⟨horizontal, vertical⟩
    simpa [Cell.add] using targetRepresentative
  · intro shiftEq
    subst shift
    rcases link with ⟨first, second, positions⟩
    rcases positions with ⟨⟨forwardX, forwardY⟩,
      ⟨backwardX, backwardY⟩⟩
    cases first <;> cases second <;>
      simpa [carrierLinkPeriodTranslate,
        CarrierNode.periodTranslate,
        CrossingBoundary.periodTranslate,
        CrossingRecord.periodTranslate,
        SegmentTerminal.periodTranslate,
        EqualityPositions.periodTranslate,
        carrierMacroPeriodTranslation, Cell.add,
        PeriodicGridDrawing.periodTranslation, Cell.scale] using
        linkMember

/-- A selected carrier source's family-specific orbit condition is exactly
the assertion that its translation is zero. -/
theorem carrierSource_retainedOrbitCondition_iff_shift_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode)
    (localClauseIndex : Nat)
    (linkMember :
      link ∈ retainedDrawingCompleteCarrierLinks
        formula.incidenceGraph)
    (shift : Cell) :
    DrawingPlanarSATClauseSource.RetainedOrbitCondition formula
        (.carrier link localClauseIndex) shift ↔
      shift = (0, 0) := by
  exact carrierLinkPeriodTranslate_mem_iff_shift_eq_zero
    linkMember shift

/-- Coordinatewise cell subtraction is zero exactly when its operands are
equal. -/
@[simp]
theorem Cell.sub_eq_zero_iff (first second : Cell) :
    Cell.sub first second = (0, 0) ↔ first = second := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [Cell.sub, Prod.mk.injEq]
  constructor
  · rintro ⟨horizontal, vertical⟩
    constructor <;> omega
  · rintro ⟨horizontal, vertical⟩
    subst firstX
    subst firstY
    norm_num

/-- For a final occurrence backed by a carrier component, the generic
first-source orbit condition is available exactly when its physical shift
already equals the desired common shift. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.carrier_retainedOrbitCondition_iff_physicalShift_eq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift : Cell}
    (witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift)
    (link : EqualityLink CarrierNode)
    (componentEq :
      witness.routeWitness.metadata.source.component = .carrier link)
    (targetPhysicalShift : Cell) :
    witness.routeWitness.metadata.source.RetainedOrbitCondition
          formula
          (Cell.sub witness.physicalShift targetPhysicalShift) ↔
      witness.physicalShift = targetPhysicalShift := by
  rcases
      witness.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq link componentEq with
    ⟨localClauseIndex, sourceEq⟩
  have sourceMember := witness.source_retainedComponentMember
  rw [sourceEq] at sourceMember
  rw [sourceEq,
    carrierSource_retainedOrbitCondition_iff_shift_eq_zero
      formula link localClauseIndex sourceMember,
    Cell.sub_eq_zero_iff]

end PeriodicOrthocrossing
end LeanTrominoes
