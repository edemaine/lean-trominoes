/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierNormalizationDegree

/-! # Injectivity of retained carrier normalization -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- A crossing boundary is recovered from its periodic prototype and the
extracted period shift. -/
private theorem CrossingBoundary.eq_of_periodNormalize_eq_of_shift_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {first second : CrossingBoundary}
    (normalizedEq : first.periodNormalize graph =
      second.periodNormalize graph)
    (shiftEq : crossingPeriodShift graph first.crossing =
      crossingPeriodShift graph second.crossing) :
    first = second := by
  have normalizedCrossingEq :
      first.crossing.periodNormalize graph =
        second.crossing.periodNormalize graph := by
    simpa [CrossingBoundary.periodNormalize] using
      congrArg CrossingBoundary.crossing normalizedEq
  have crossingEq : first.crossing = second.crossing := by
    calc
      first.crossing =
          (first.crossing.periodNormalize graph).periodTranslate graph
            (crossingPeriodShift graph first.crossing) :=
        (CrossingRecord.periodNormalize_periodTranslate_shift
          graph first.crossing).symm
      _ =
          (second.crossing.periodNormalize graph).periodTranslate graph
            (crossingPeriodShift graph second.crossing) := by
        rw [normalizedCrossingEq, shiftEq]
      _ = second.crossing :=
        CrossingRecord.periodNormalize_periodTranslate_shift
          graph second.crossing
  have sideEq : first.side = second.side := by
    simpa [CrossingBoundary.periodNormalize] using
      congrArg CrossingBoundary.side normalizedEq
  cases first
  cases second
  simp_all

/-- Periodic normalization forgets only a common translation.  The retained
zero-shift ownership condition fixes that translation, so two selected links
with the same normalized link are the same physical link. -/
theorem retainedDrawingCompleteCarrierLinks_normalizeLink_injective_on
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {first second : EqualityLink CarrierNode}
    (firstMem : first ∈ retainedDrawingCompleteCarrierLinks graph)
    (secondMem : second ∈ retainedDrawingCompleteCarrierLinks graph)
    (normalizedEq :
      PeriodicEquality.normalizeLink (normalizeCarrierNode graph) first =
        PeriodicEquality.normalizeLink (normalizeCarrierNode graph) second) :
    first = second := by
  have firstRepresentative : CarrierLinkIsRepresentative graph first :=
    (mem_retainedDrawingCompleteCarrierLinks_iff graph first).mp firstMem |>.2
  have secondRepresentative : CarrierLinkIsRepresentative graph second :=
    (mem_retainedDrawingCompleteCarrierLinks_iff graph second).mp secondMem |>.2
  apply retainedDrawingCompleteCarrierLinks_eq_of_second_eq
    firstMem secondMem
  rcases first with ⟨firstNode, firstTarget, firstPositions⟩
  rcases second with ⟨secondNode, secondTarget, secondPositions⟩
  cases firstNode <;> cases firstTarget <;>
    cases secondNode <;> cases secondTarget <;>
      simp [PeriodicEquality.normalizeLink, normalizeCarrierNode,
        CarrierLinkIsRepresentative, carrierLinkRepresentativeShift]
        at normalizedEq firstRepresentative secondRepresentative ⊢
  case boundary.boundary.boundary.boundary =>
    rcases normalizedEq with
      ⟨_firstPrototypeEq, secondPrototypeEq, offsetEq⟩
    apply CrossingBoundary.eq_of_periodNormalize_eq_of_shift_eq
      graph secondPrototypeEq
    rw [firstRepresentative, secondRepresentative] at offsetEq
    simpa [Cell.sub] using offsetEq
  case boundary.terminal.boundary.terminal =>
    rcases normalizedEq with
      ⟨_firstPrototypeEq, secondPrototypeEq, offsetEq⟩
    apply SegmentTerminal.eq_of_fields_eq
      secondPrototypeEq.1 _ secondPrototypeEq.2
    rw [firstRepresentative, secondRepresentative] at offsetEq
    simpa [Cell.sub] using offsetEq
  case terminal.boundary.terminal.boundary =>
    rcases normalizedEq with
      ⟨_firstPrototypeEq, secondPrototypeEq, _offsetEq⟩
    apply CrossingBoundary.eq_of_periodNormalize_eq_of_shift_eq
      graph secondPrototypeEq
    exact firstRepresentative.trans secondRepresentative.symm
  case terminal.terminal.terminal.terminal =>
    rcases normalizedEq with
      ⟨_firstPrototypeEq, secondPrototypeEq, offsetEq⟩
    apply SegmentTerminal.eq_of_fields_eq
      secondPrototypeEq.1 _ secondPrototypeEq.2
    rw [firstRepresentative, secondRepresentative] at offsetEq
    simpa [Cell.sub] using offsetEq

/-- Selected retained links remain duplicate-free after periodic
normalization. -/
theorem retainedDrawingCompleteCarrierLinks_normalizeLink_nodup
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    ((retainedDrawingCompleteCarrierLinks graph).map
      (PeriodicEquality.normalizeLink (normalizeCarrierNode graph))).Nodup := by
  apply (retainedDrawingCompleteCarrierLinks_nodup graph).map_on
  intro first firstMem second secondMem normalizedEq
  exact retainedDrawingCompleteCarrierLinks_normalizeLink_injective_on
    firstMem secondMem normalizedEq

/-- Consequently the two implication clauses for every retained carrier
link are already in the final deduplicated order. -/
theorem retainedDrawingCompleteCarrierLinks_normalizedFormulaClauses_nodup
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    (PeriodicEquality.normalizedFormulaClauses
      (normalizeCarrierNode graph)
      (retainedDrawingCompleteCarrierLinks graph)).Nodup := by
  rw [PeriodicEquality.normalizedFormulaClauses_eq]
  exact PeriodicEquality.normalizedClauses_nodup _
    (retainedDrawingCompleteCarrierLinks_normalizeLink_nodup graph)

end PeriodicOrthocrossing
end LeanTrominoes
