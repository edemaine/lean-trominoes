import LeanTrominoes.Gadget
import Lean.Elab.Tactic.Omega

/-!
# Extendable states of straight tromino wires

An isolated open gadget window admits transient boundary states that cannot be
continued through an infinite row of neighboring gadgets.  This file turns
the raw local tilings into a finite transfer relation and prunes states lacking
a predecessor or successor.  The resulting core is the correct object for the
two wire orientations used in the hardness reduction.
-/

namespace LeanTrominoes
namespace Gadget

/-- A geometric port state is a finite collection of occupied tromino
footprints, with representation-level symmetries forgotten. -/
abbrev PortState := Finset (Finset Cell)

/-- Translate every cell of a geometric tromino footprint. -/
def translateFootprint (offset : Cell) (footprint : Finset Cell) : Finset Cell :=
  footprint.image (Cell.add offset)

/-- Does a footprint cross the left side of a window based at `x = 0`? -/
def crossesLeft (footprint : Finset Cell) : Prop :=
  ∃ cell ∈ footprint, cell.1 < 0

/-- Does a footprint cross the right side of a width-`width` window? -/
def crossesRight (width : Nat) (footprint : Finset Cell) : Prop :=
  ∃ cell ∈ footprint, (width : Int) ≤ cell.1

instance (footprint : Finset Cell) : Decidable (crossesLeft footprint) := by
  unfold crossesLeft
  infer_instance

instance (width : Nat) (footprint : Finset Cell) :
    Decidable (crossesRight width footprint) := by
  unfold crossesRight
  infer_instance

/-- Boundary footprints crossing the left side, in coordinates relative to
the current gadget. -/
def leftPortState (signature : PortState) : PortState :=
  signature.filter crossesLeft

/-- Boundary footprints crossing the right side, translated back by one
window width so that they use the next gadget's left-boundary coordinates. -/
def rightPortState (width : Nat) (signature : PortState) : PortState :=
  (signature.filter (crossesRight width)).image fun footprint =>
    translateFootprint (-(width : Int), 0) footprint

/-- The normalized left and right port states induced by one local tiling. -/
def portTransition (tromino : Tromino) (gadget : Gadget)
    (placements : Finset (Placement Unit)) : PortState × PortState :=
  let signature := boundarySignature tromino gadget.window placements
  (leftPortState signature, rightPortState gadget.width signature)

/-- All local port transitions, computed by verified exact-cover search. -/
def exactPortTransitions (tromino : Tromino) (gadget : Gadget)
    (regionCells : List Cell) : Finset (PortState × PortState) :=
  ((exactWindowTilings tromino gadget regionCells).map
    (portTransition tromino gadget)).toFinset

/-- Keep only transitions having both some predecessor and some successor in
the current finite relation. -/
def pruneTransitions (transitions : Finset (PortState × PortState)) :
    Finset (PortState × PortState) :=
  transitions.filter fun transition =>
    (∃ previous ∈ transitions, previous.2 = transition.1) ∧
      ∃ next ∈ transitions, transition.2 = next.1

/-- Repeatedly prune a finite transition relation. -/
def pruneTransitionsN : Nat → Finset (PortState × PortState) →
    Finset (PortState × PortState)
  | 0, transitions => transitions
  | fuel + 1, transitions =>
      pruneTransitions (pruneTransitionsN fuel transitions)

/-- The extendable core; at most one edge disappears per nontrivial pruning
round, so the initial edge count is sufficient fuel. -/
def extendableTransitions (transitions : Finset (PortState × PortState)) :
    Finset (PortState × PortState) :=
  pruneTransitionsN transitions.card transitions

theorem pruneTransitions_subset (transitions : Finset (PortState × PortState)) :
    pruneTransitions transitions ⊆ transitions := by
  exact Finset.filter_subset _ _

theorem pruneTransitionsN_subset (fuel : Nat)
    (transitions : Finset (PortState × PortState)) :
    pruneTransitionsN fuel transitions ⊆ transitions := by
  induction fuel with
  | zero => exact Finset.Subset.rfl
  | succ fuel induction =>
      exact (pruneTransitions_subset _).trans induction

theorem extendableTransitions_subset
    (transitions : Finset (PortState × PortState)) :
    extendableTransitions transitions ⊆ transitions :=
  pruneTransitionsN_subset transitions.card transitions

/-- A transition occurs at the origin of a compatible bi-infinite sequence of
local transitions. -/
def IsBiInfiniteTransition
    (transitions : Finset (PortState × PortState))
    (transition : PortState × PortState) : Prop :=
  ∃ chain : Int → PortState × PortState,
    chain 0 = transition ∧
      ∀ index, chain index ∈ transitions ∧
        (chain index).2 = (chain (index + 1)).1

theorem biInfinite_mem_pruneTransitionsN
    (transitions : Finset (PortState × PortState))
    (chain : Int → PortState × PortState)
    (compatible : ∀ index, chain index ∈ transitions ∧
      (chain index).2 = (chain (index + 1)).1) :
    ∀ fuel index, chain index ∈ pruneTransitionsN fuel transitions := by
  intro fuel
  induction fuel with
  | zero => exact fun index => (compatible index).1
  | succ fuel induction =>
      intro index
      apply Finset.mem_filter.mpr
      refine ⟨induction index, ?_, ?_⟩
      · refine ⟨chain (index - 1), induction (index - 1), ?_⟩
        have previous := (compatible (index - 1)).2
        simpa only [sub_add_cancel] using previous
      · exact ⟨chain (index + 1), induction (index + 1),
          (compatible index).2⟩

/-- Every genuinely bi-infinite transition survives all finite pruning rounds. -/
theorem mem_extendableTransitions_of_biInfinite
    (transitions : Finset (PortState × PortState))
    (transition : PortState × PortState)
    (biInfinite : IsBiInfiniteTransition transitions transition) :
    transition ∈ extendableTransitions transitions := by
  obtain ⟨chain, origin, compatible⟩ := biInfinite
  rw [← origin]
  exact biInfinite_mem_pruneTransitionsN transitions chain compatible
    transitions.card 0

/-- Extendable transitions of the Figure 11 L wire. -/
def figure11RedWireTransitions : Finset (PortState × PortState) :=
  extendableTransitions
    (exactPortTransitions .L figure11RedWire figure11RedWireCells)

/-- Extendable transitions of the Figure 12 I wire. -/
def figure12RedWireTransitions : Finset (PortState × PortState) :=
  extendableTransitions
    (exactPortTransitions .I figure12RedWire figure12RedWireCells)

theorem figure11RedWireTransitions_card :
    figure11RedWireTransitions.card = 2 := by
  native_decide

theorem figure11RedWireTransitions_selfLoops :
    ∀ transition ∈ figure11RedWireTransitions,
      transition.1 = transition.2 := by
  native_decide

theorem figure12RedWireTransitions_card :
    figure12RedWireTransitions.card = 2 := by
  native_decide

theorem figure12RedWireTransitions_selfLoops :
    ∀ transition ∈ figure12RedWireTransitions,
      transition.1 = transition.2 := by
  native_decide

set_option maxRecDepth 2000 in
theorem figure11RedWire_biInfinite_iff
    (transition : PortState × PortState) :
    IsBiInfiniteTransition
      (exactPortTransitions .L figure11RedWire figure11RedWireCells) transition ↔
      transition ∈ figure11RedWireTransitions := by
  constructor
  · exact mem_extendableTransitions_of_biInfinite _ transition
  · intro member
    change transition ∈ extendableTransitions
      (exactPortTransitions .L figure11RedWire figure11RedWireCells) at member
    have rawMember : transition ∈
        exactPortTransitions .L figure11RedWire figure11RedWireCells :=
      extendableTransitions_subset _ member
    have selfLoop := figure11RedWireTransitions_selfLoops transition member
    refine ⟨fun _ => transition, rfl, fun _ => ⟨rawMember, ?_⟩⟩
    exact selfLoop.symm

set_option maxRecDepth 2000 in
theorem figure12RedWire_biInfinite_iff
    (transition : PortState × PortState) :
    IsBiInfiniteTransition
      (exactPortTransitions .I figure12RedWire figure12RedWireCells) transition ↔
      transition ∈ figure12RedWireTransitions := by
  constructor
  · exact mem_extendableTransitions_of_biInfinite _ transition
  · intro member
    change transition ∈ extendableTransitions
      (exactPortTransitions .I figure12RedWire figure12RedWireCells) at member
    have rawMember : transition ∈
        exactPortTransitions .I figure12RedWire figure12RedWireCells :=
      extendableTransitions_subset _ member
    have selfLoop := figure12RedWireTransitions_selfLoops transition member
    refine ⟨fun _ => transition, rfl, fun _ => ⟨rawMember, ?_⟩⟩
    exact selfLoop.symm

end Gadget
end LeanTrominoes
