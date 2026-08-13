/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierTranslation

/-!
# Moving carrier links to their owned representatives

The representative correction is the negative of a link's selected owner
shift.  Translating by it sends that shift to zero, leaves the normalized
periodic equality link unchanged, and sends the selected crossing boundary
exactly to its canonical normalization.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- The inverse of a lattice translation. -/
def Cell.neg (cell : Cell) : Cell :=
  Cell.sub (0, 0) cell

@[simp]
theorem Cell.add_neg_self (cell : Cell) :
    Cell.add cell (Cell.neg cell) = (0, 0) := by
  rcases cell with ⟨horizontal, vertical⟩
  simp [Cell.neg, Cell.add, Cell.sub]

@[simp]
theorem Cell.add_zero (cell : Cell) :
    Cell.add cell (0, 0) = cell := by
  rcases cell with ⟨horizontal, vertical⟩
  simp [Cell.add]

/-- Translating a prospective carrier link adds the common shift to its
selected representative shift. -/
theorem carrierLinkRepresentativeShift_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (link : EqualityLink CarrierNode) (shift : Cell) :
    carrierLinkRepresentativeShift graph
        (carrierLinkPeriodTranslate graph link shift) =
      Cell.add (carrierLinkRepresentativeShift graph link) shift := by
  rcases link with ⟨first, second, positions⟩
  cases first with
  | boundary firstBoundary =>
      simp [carrierLinkPeriodTranslate,
        carrierLinkRepresentativeShift,
        CarrierNode.periodTranslate,
        CrossingBoundary.periodTranslate,
        crossingPeriodShift_periodTranslate]
  | terminal firstTerminal =>
      cases second with
      | boundary secondBoundary =>
          simp [carrierLinkPeriodTranslate,
            carrierLinkRepresentativeShift,
            CarrierNode.periodTranslate,
            CrossingBoundary.periodTranslate,
            crossingPeriodShift_periodTranslate]
      | terminal secondTerminal =>
          simp [carrierLinkPeriodTranslate,
            carrierLinkRepresentativeShift,
            CarrierNode.periodTranslate,
            SegmentTerminal.periodTranslate]

/-- The common translation that moves a link's selected owner to period
shift zero. -/
def carrierLinkRepresentativeCorrection
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (link : EqualityLink CarrierNode) : Cell :=
  Cell.neg (carrierLinkRepresentativeShift graph link)

/-- Applying the representative correction selects a zero-shift link. -/
theorem carrierLinkPeriodTranslate_correction_isRepresentative
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (link : EqualityLink CarrierNode) :
    CarrierLinkIsRepresentative graph
      (carrierLinkPeriodTranslate graph link
        (carrierLinkRepresentativeCorrection graph link)) := by
  unfold CarrierLinkIsRepresentative
  rw [carrierLinkRepresentativeShift_periodTranslate]
  exact Cell.add_neg_self _

/-- Correcting ownership does not change the normalized periodic equality
link. -/
@[simp]
theorem normalizeLink_carrierLinkRepresentativeCorrection
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (link : EqualityLink CarrierNode) :
    PeriodicEquality.normalizeLink (normalizeCarrierNode graph)
        (carrierLinkPeriodTranslate graph link
          (carrierLinkRepresentativeCorrection graph link)) =
      PeriodicEquality.normalizeLink (normalizeCarrierNode graph) link :=
  normalizeLink_carrierLinkPeriodTranslate graph link _

/-- Translating a crossing by the negative of its extracted period shift is
definitionally the same geometric operation as periodic normalization. -/
theorem CrossingRecord.periodTranslate_neg_shift_eq_periodNormalize
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (record : CrossingRecord) :
    record.periodTranslate graph
        (Cell.neg (crossingPeriodShift graph record)) =
      record.periodNormalize graph := by
  rcases record with
    ⟨first, ⟨firstX, firstY⟩,
      second, ⟨secondX, secondY⟩,
      ⟨pointX, pointY⟩⟩
  rcases shiftEq :
      crossingPeriodShift graph
        ({ first := first
           firstTranslate := (firstX, firstY)
           second := second
           secondTranslate := (secondX, secondY)
           point := (pointX, pointY) } : CrossingRecord) with
    ⟨shiftX, shiftY⟩
  simp [CrossingRecord.periodTranslate,
    CrossingRecord.periodNormalize, shiftEq,
    Cell.neg, Cell.add, Cell.sub,
    PeriodicGridDrawing.normalizePoint,
    PeriodicGridDrawing.periodTranslation, Cell.scale]
  simp [sub_eq_add_neg]

/-- The selected first boundary of a corrected link is exactly its canonical
boundary. -/
theorem carrierLinkRepresentativeCorrection_first_boundary
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {link : EqualityLink CarrierNode}
    {boundary : CrossingBoundary}
    (firstEq : link.first = .boundary boundary) :
    (carrierLinkPeriodTranslate graph link
      (carrierLinkRepresentativeCorrection graph link)).first =
        .boundary (boundary.periodNormalize graph) := by
  have correctionEq :
      carrierLinkRepresentativeCorrection graph link =
        Cell.neg (crossingPeriodShift graph boundary.crossing) := by
    simp [carrierLinkRepresentativeCorrection,
      carrierLinkRepresentativeShift, firstEq]
  rw [carrierLinkPeriodTranslate_first, firstEq, correctionEq]
  simp [CarrierNode.periodTranslate,
    CrossingBoundary.periodTranslate,
    CrossingRecord.periodTranslate_neg_shift_eq_periodNormalize,
    CrossingBoundary.periodNormalize]

/-- When a terminal precedes the selected boundary, correction sends that
second endpoint exactly to its canonical boundary. -/
theorem carrierLinkRepresentativeCorrection_terminal_boundary
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {link : EqualityLink CarrierNode}
    {terminal : SegmentTerminal}
    {boundary : CrossingBoundary}
    (firstEq : link.first = .terminal terminal)
    (secondEq : link.second = .boundary boundary) :
    (carrierLinkPeriodTranslate graph link
      (carrierLinkRepresentativeCorrection graph link)).second =
        .boundary (boundary.periodNormalize graph) := by
  have correctionEq :
      carrierLinkRepresentativeCorrection graph link =
        Cell.neg (crossingPeriodShift graph boundary.crossing) := by
    simp [carrierLinkRepresentativeCorrection,
      carrierLinkRepresentativeShift, firstEq, secondEq]
  rw [carrierLinkPeriodTranslate_second, secondEq, correctionEq]
  simp [CarrierNode.periodTranslate,
    CrossingBoundary.periodTranslate,
    CrossingRecord.periodTranslate_neg_shift_eq_periodNormalize,
    CrossingBoundary.periodNormalize]

/-- Correcting a direct terminal-to-terminal link sends its first terminal to
translation zero. -/
theorem carrierLinkRepresentativeCorrection_terminal_terminal
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {link : EqualityLink CarrierNode}
    {first second : SegmentTerminal}
    (firstEq : link.first = .terminal first)
    (secondEq : link.second = .terminal second) :
    (carrierLinkPeriodTranslate graph link
      (carrierLinkRepresentativeCorrection graph link)).first =
        .terminal
          ⟨first.indexed, (0, 0), first.endpoint⟩ := by
  have correctionEq :
      carrierLinkRepresentativeCorrection graph link =
        Cell.neg first.translate := by
    simp [carrierLinkRepresentativeCorrection,
      carrierLinkRepresentativeShift, firstEq, secondEq]
  rw [carrierLinkPeriodTranslate_first, firstEq, correctionEq]
  rcases first with ⟨indexed, translate, endpoint⟩
  simp [CarrierNode.periodTranslate,
    SegmentTerminal.periodTranslate]

end PeriodicOrthocrossing
end LeanTrominoes
