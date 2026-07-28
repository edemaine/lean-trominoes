import LeanTrominoes.PeriodicOrthocrossingPlanarTerminals

/-!
# Periodic ownership of retained carrier links

The crossing halo is an enumeration window: it contains physical translates
needed to see every local interaction, but its outer edge is not a boundary of
the infinite periodic carrier.  Consequently, simply replacing the canonical
crossing list in every finite carrier chain by the whole halo can create
truncation-edge links.

This file separates the two roles.  `retainedCrossingBoundaries` supplies the
physical split points, while `carrierLinkRepresentativeShift` chooses the
periodic cell that owns a prospective carrier link.  A link with a boundary is
owned by its first boundary along the carrier, or by its only boundary when a
terminal comes first.  A direct terminal-to-terminal link is owned by the
translation of its first terminal.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- All four physical boundary variables at every retained halo crossing. -/
def retainedCrossingBoundaries
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List CrossingBoundary :=
  (orientedCrossingHalo graph).flatMap fun crossing =>
    [⟨crossing, .left⟩, ⟨crossing, .right⟩,
      ⟨crossing, .top⟩, ⟨crossing, .bottom⟩]

/-- Every canonical crossing boundary is among the retained physical
boundaries. -/
theorem drawingCrossingBoundaries_subset_retainedCrossingBoundaries
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    drawingCrossingBoundaries graph ⊆
      retainedCrossingBoundaries graph := by
  intro boundary boundaryMem
  rcases List.mem_flatMap.mp boundaryMem with
    ⟨crossing, crossingMem, boundaryMem⟩
  apply List.mem_flatMap.mpr
  exact ⟨crossing,
    orientedCrossings_subset_orientedCrossingHalo graph crossingMem,
    boundaryMem⟩

/-- A retained physical boundary remembers a genuine halo crossing. -/
theorem retainedCrossingBoundary_crossing_mem
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {boundary : CrossingBoundary}
    (boundaryMem :
      boundary ∈ retainedCrossingBoundaries graph) :
    boundary.crossing ∈ orientedCrossingHalo graph := by
  rcases List.mem_flatMap.mp boundaryMem with
    ⟨crossing, crossingMem, boundaryMem⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at boundaryMem
  rcases boundaryMem with
    boundaryEq | boundaryEq | boundaryEq | boundaryEq <;>
      subst boundary <;> exact crossingMem

/-- Normalizing a retained physical boundary produces a listed canonical
boundary with the same port side. -/
theorem retainedCrossingBoundary_periodNormalize_mem
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {boundary : CrossingBoundary}
    (boundaryMem :
      boundary ∈ retainedCrossingBoundaries graph) :
    boundary.periodNormalize graph ∈
      drawingCrossingBoundaries graph := by
  have crossingMem :=
    retainedCrossingBoundary_crossing_mem graph boundaryMem
  have normalizedMem :=
    periodNormalize_mem_orientedCrossings
      wellFormed degree isLocal crossingMem
  rcases boundary with ⟨crossing, side⟩
  apply List.mem_flatMap.mpr
  refine ⟨crossing.periodNormalize graph, normalizedMem, ?_⟩
  cases side <;> simp [CrossingBoundary.periodNormalize]

/-- A crossing boundary whose physical crossing has zero period shift is
already its own canonical representative. -/
theorem CrossingBoundary.periodNormalize_eq_self_of_shift_eq_zero
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (boundary : CrossingBoundary)
    (shiftZero :
      crossingPeriodShift graph boundary.crossing = (0, 0)) :
    boundary.periodNormalize graph = boundary := by
  rcases boundary with ⟨crossing, side⟩
  simp [CrossingBoundary.periodNormalize,
    CrossingRecord.periodNormalize, shiftZero,
    PeriodicGridDrawing.normalizePoint, Cell.sub,
    PeriodicGridDrawing.periodTranslation, Cell.scale]

/-- The period shift used to select one finite representative of a prospective
retained carrier link. -/
def carrierLinkRepresentativeShift
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (link : EqualityLink CarrierNode) : Cell :=
  match link.first, link.second with
  | .boundary boundary, _ =>
      crossingPeriodShift graph boundary.crossing
  | .terminal _, .boundary boundary =>
      crossingPeriodShift graph boundary.crossing
  | .terminal terminal, .terminal _ =>
      terminal.translate

/-- A retained carrier link is owned by the zero-shift representative of its
periodic orbit. -/
def CarrierLinkIsRepresentative
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (link : EqualityLink CarrierNode) : Prop :=
  carrierLinkRepresentativeShift graph link = (0, 0)

instance carrierLinkIsRepresentativeDecidable
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (link : EqualityLink CarrierNode) :
    Decidable (CarrierLinkIsRepresentative graph link) := by
  unfold CarrierLinkIsRepresentative
  infer_instance

/-- The first boundary of a representative carrier link is canonical. -/
theorem carrierLinkRepresentative_first_boundary_normalizes_self
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {link : EqualityLink CarrierNode}
    {boundary : CrossingBoundary}
    (firstEq : link.first = .boundary boundary)
    (representative : CarrierLinkIsRepresentative graph link) :
    boundary.periodNormalize graph = boundary := by
  apply
    CrossingBoundary.periodNormalize_eq_self_of_shift_eq_zero
      graph boundary
  simpa [CarrierLinkIsRepresentative,
    carrierLinkRepresentativeShift, firstEq] using representative

/-- When a representative link starts at a terminal and ends at a boundary,
that boundary is canonical. -/
theorem carrierLinkRepresentative_terminal_boundary_normalizes_self
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {link : EqualityLink CarrierNode}
    {terminal : SegmentTerminal}
    {boundary : CrossingBoundary}
    (firstEq : link.first = .terminal terminal)
    (secondEq : link.second = .boundary boundary)
    (representative : CarrierLinkIsRepresentative graph link) :
    boundary.periodNormalize graph = boundary := by
  apply
    CrossingBoundary.periodNormalize_eq_self_of_shift_eq_zero
      graph boundary
  simpa [CarrierLinkIsRepresentative,
    carrierLinkRepresentativeShift, firstEq, secondEq] using
      representative

/-- A representative direct terminal link starts in translation zero. -/
theorem carrierLinkRepresentative_terminal_terminal_translate_eq_zero
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {link : EqualityLink CarrierNode}
    {first second : SegmentTerminal}
    (firstEq : link.first = .terminal first)
    (secondEq : link.second = .terminal second)
    (representative : CarrierLinkIsRepresentative graph link) :
    first.translate = (0, 0) := by
  simpa [CarrierLinkIsRepresentative,
    carrierLinkRepresentativeShift, firstEq, secondEq] using
      representative

end PeriodicOrthocrossing
end LeanTrominoes
