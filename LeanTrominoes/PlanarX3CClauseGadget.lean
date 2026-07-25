import LeanTrominoes.PlanarThreeDMVariableGadget

/-!
# The Dyer--Frieze planar X3C clause core

Before coloring the reduction as a three-dimensional-matching instance,
Dyer and Frieze represent each clause by the nine-set planar X3C gadget in
Figure 5 of their planar-3DM reduction.

The gadget has three internal elements and three terminals, each consisting
of three elements.  Every internal element occurs in three sets and every
terminal element occurs in two.  A terminal Boolean records whether all
three of its elements are covered outside the gadget.  Exhaustive checking
below proves that the gadget can cover everything else exactly when exactly
one terminal is covered externally.

The names and coordinates follow the triangular layout of Figure 5.  Dashed
curves in that figure merely delimit terminals and are not incidences.
-/

namespace LeanTrominoes
namespace PlanarThreeDM

open Gadget

/-- The nine sets (future matching triples) in the clause core. -/
inductive X3CClauseSet
  | topLeftOuter
  | topLeftInner
  | topRightInner
  | topRightOuter
  | leftMiddle
  | rightMiddle
  | bottomLeft
  | bottomRight
  | bottom
  deriving DecidableEq, Repr, Fintype

/-- The three elements internal to the clause core. -/
inductive X3CClauseInternal
  | left
  | right
  | bottom
  deriving DecidableEq, Repr, Fintype

/-- The three three-element terminals of the clause core. -/
inductive X3CClauseTerminalGroup
  | top
  | left
  | right
  deriving DecidableEq, Repr, Fintype

/-- Positions within a three-element terminal, in boundary order. -/
inductive X3CClauseTerminalSlot
  | first
  | second
  | third
  deriving DecidableEq, Repr, Fintype

/-- A terminal element is identified by its terminal and its slot. -/
structure X3CClauseTerminal where
  group : X3CClauseTerminalGroup
  slot : X3CClauseTerminalSlot
  deriving DecidableEq, Repr

/-- All twelve elements of the uncolored X3C clause core. -/
inductive X3CClauseElement
  | internal (value : X3CClauseInternal)
  | terminal (value : X3CClauseTerminal)
  deriving DecidableEq, Repr

namespace X3CClauseSet

/-- The three elements contained in each set of Figure 5. -/
def references : X3CClauseSet → List X3CClauseElement
  | .topLeftOuter =>
      [.terminal ⟨.top, .first⟩,
        .terminal ⟨.left, .first⟩,
        .internal .left]
  | .topLeftInner =>
      [.terminal ⟨.top, .first⟩,
        .terminal ⟨.top, .second⟩,
        .internal .left]
  | .topRightInner =>
      [.terminal ⟨.top, .second⟩,
        .terminal ⟨.top, .third⟩,
        .internal .right]
  | .topRightOuter =>
      [.terminal ⟨.top, .third⟩,
        .terminal ⟨.right, .first⟩,
        .internal .right]
  | .leftMiddle =>
      [.terminal ⟨.left, .first⟩,
        .terminal ⟨.left, .second⟩,
        .internal .left]
  | .rightMiddle =>
      [.terminal ⟨.right, .first⟩,
        .terminal ⟨.right, .second⟩,
        .internal .right]
  | .bottomLeft =>
      [.terminal ⟨.left, .second⟩,
        .terminal ⟨.left, .third⟩,
        .internal .bottom]
  | .bottomRight =>
      [.terminal ⟨.right, .second⟩,
        .terminal ⟨.right, .third⟩,
        .internal .bottom]
  | .bottom =>
      [.terminal ⟨.left, .third⟩,
        .terminal ⟨.right, .third⟩,
        .internal .bottom]

/-- Integer coordinates preserving the triangular combinatorial layout of
Figure 5. -/
def position : X3CClauseSet → Cell
  | .topLeftOuter => (2, 3)
  | .topLeftInner => (4, 2)
  | .topRightInner => (6, 2)
  | .topRightOuter => (8, 3)
  | .leftMiddle => (2, 6)
  | .rightMiddle => (8, 6)
  | .bottomLeft => (4, 8)
  | .bottomRight => (6, 8)
  | .bottom => (5, 10)

end X3CClauseSet

namespace X3CClauseInternal

/-- The three sets incident to each internal element. -/
def neighbors : X3CClauseInternal → List X3CClauseSet
  | .left => [.topLeftOuter, .topLeftInner, .leftMiddle]
  | .right => [.topRightInner, .topRightOuter, .rightMiddle]
  | .bottom => [.bottomLeft, .bottomRight, .bottom]

/-- Integer coordinates for the three internal element vertices. -/
def position : X3CClauseInternal → Cell
  | .left => (3, 5)
  | .right => (7, 5)
  | .bottom => (5, 8)

/-- One of the six colorings of the clause core, modulo global color
permutation. -/
def color : X3CClauseInternal → WireColor
  | .left => .red
  | .right => .green
  | .bottom => .blue

end X3CClauseInternal

namespace X3CClauseTerminal

/-- The two sets incident to each terminal element. -/
def neighbors : X3CClauseTerminal → List X3CClauseSet
  | ⟨.top, .first⟩ => [.topLeftOuter, .topLeftInner]
  | ⟨.top, .second⟩ => [.topLeftInner, .topRightInner]
  | ⟨.top, .third⟩ => [.topRightInner, .topRightOuter]
  | ⟨.left, .first⟩ => [.topLeftOuter, .leftMiddle]
  | ⟨.left, .second⟩ => [.leftMiddle, .bottomLeft]
  | ⟨.left, .third⟩ => [.bottomLeft, .bottom]
  | ⟨.right, .first⟩ => [.topRightOuter, .rightMiddle]
  | ⟨.right, .second⟩ => [.rightMiddle, .bottomRight]
  | ⟨.right, .third⟩ => [.bottomRight, .bottom]

/-- Integer coordinates for the nine terminal element vertices. -/
def position : X3CClauseTerminal → Cell
  | ⟨.top, .first⟩ => (3, 0)
  | ⟨.top, .second⟩ => (5, 0)
  | ⟨.top, .third⟩ => (7, 0)
  | ⟨.left, .first⟩ => (0, 5)
  | ⟨.left, .second⟩ => (1, 7)
  | ⟨.left, .third⟩ => (3, 10)
  | ⟨.right, .first⟩ => (10, 5)
  | ⟨.right, .second⟩ => (9, 7)
  | ⟨.right, .third⟩ => (7, 10)

/-- The terminal part of the selected clause-core coloring. -/
def color : X3CClauseTerminal → WireColor
  | ⟨.top, .first⟩ => .green
  | ⟨.top, .second⟩ => .blue
  | ⟨.top, .third⟩ => .red
  | ⟨.left, .first⟩ => .blue
  | ⟨.left, .second⟩ => .green
  | ⟨.left, .third⟩ => .red
  | ⟨.right, .first⟩ => .blue
  | ⟨.right, .second⟩ => .red
  | ⟨.right, .third⟩ => .green

/-- Terminal order seen by a noncrossing three-strand attachment.  The top
and right sides are read in the reverse of their local boundary indexing,
while the left side is read forward. -/
def attachmentElement
    (group : X3CClauseTerminalGroup) :
    X3CClauseTerminalSlot → X3CClauseTerminal
  | .first =>
      match group with
      | .top => ⟨.top, .third⟩
      | .left => ⟨.left, .first⟩
      | .right => ⟨.right, .third⟩
  | .second => ⟨group, .second⟩
  | .third =>
      match group with
      | .top => ⟨.top, .first⟩
      | .left => ⟨.left, .third⟩
      | .right => ⟨.right, .first⟩

/-- Color occupying the fixed position of each terminal attachment. -/
def fixedAttachmentColor
    (group : X3CClauseTerminalGroup) : WireColor :=
  (attachmentElement group .first).color

end X3CClauseTerminal

namespace X3CClauseElement

/-- The incident sets of any element in the clause core. -/
def neighbors : X3CClauseElement → List X3CClauseSet
  | .internal value => value.neighbors
  | .terminal value => value.neighbors

/-- The color of every clause-core element. -/
def color : X3CClauseElement → WireColor
  | .internal value => value.color
  | .terminal value => value.color

end X3CClauseElement

/-- One explicitly colored red, green, and blue reference. -/
structure ColoredX3CClauseReferences where
  red : X3CClauseElement
  green : X3CClauseElement
  blue : X3CClauseElement
  deriving DecidableEq, Repr

namespace X3CClauseSet

/-- Reorder each uncolored three-set into its red, green, and blue
references. -/
def coloredReferences : X3CClauseSet → ColoredX3CClauseReferences
  | .topLeftOuter =>
      ⟨.internal .left,
        .terminal ⟨.top, .first⟩,
        .terminal ⟨.left, .first⟩⟩
  | .topLeftInner =>
      ⟨.internal .left,
        .terminal ⟨.top, .first⟩,
        .terminal ⟨.top, .second⟩⟩
  | .topRightInner =>
      ⟨.terminal ⟨.top, .third⟩,
        .internal .right,
        .terminal ⟨.top, .second⟩⟩
  | .topRightOuter =>
      ⟨.terminal ⟨.top, .third⟩,
        .internal .right,
        .terminal ⟨.right, .first⟩⟩
  | .leftMiddle =>
      ⟨.internal .left,
        .terminal ⟨.left, .second⟩,
        .terminal ⟨.left, .first⟩⟩
  | .rightMiddle =>
      ⟨.terminal ⟨.right, .second⟩,
        .internal .right,
        .terminal ⟨.right, .first⟩⟩
  | .bottomLeft =>
      ⟨.terminal ⟨.left, .third⟩,
        .terminal ⟨.left, .second⟩,
        .internal .bottom⟩
  | .bottomRight =>
      ⟨.terminal ⟨.right, .second⟩,
        .terminal ⟨.right, .third⟩,
        .internal .bottom⟩
  | .bottom =>
      ⟨.terminal ⟨.left, .third⟩,
        .terminal ⟨.right, .third⟩,
        .internal .bottom⟩

end X3CClauseSet

/-- The colored and uncolored descriptions contain exactly the same three
elements. -/
theorem x3cClause_coloredReferences_eq_references
    (set : X3CClauseSet) :
    ([set.coloredReferences.red, set.coloredReferences.green,
        set.coloredReferences.blue] : List X3CClauseElement).toFinset =
      set.references.toFinset := by
  cases set <;> native_decide

/-- The red field really is red in every clause-core set. -/
theorem x3cClause_coloredReferences_red
    (set : X3CClauseSet) :
    set.coloredReferences.red.color = .red := by
  cases set <;> rfl

/-- The green field really is green in every clause-core set. -/
theorem x3cClause_coloredReferences_green
    (set : X3CClauseSet) :
    set.coloredReferences.green.color = .green := by
  cases set <;> rfl

/-- The blue field really is blue in every clause-core set. -/
theorem x3cClause_coloredReferences_blue
    (set : X3CClauseSet) :
    set.coloredReferences.blue.color = .blue := by
  cases set <;> rfl

/-- Each three-element terminal contains one element of each color. -/
theorem x3cClause_terminal_colors
    (group : X3CClauseTerminalGroup) :
    (([X3CClauseTerminal.color ⟨group, .first⟩,
        X3CClauseTerminal.color ⟨group, .second⟩,
        X3CClauseTerminal.color ⟨group, .third⟩] :
          List WireColor).toFinset) =
      ([WireColor.red, .green, .blue] : List WireColor).toFinset := by
  cases group <;> native_decide

/-- In attachment order, the three terminals have the red-blue-green,
blue-green-red, and green-red-blue patterns described by Dyer and Frieze
(with green replacing their yellow). -/
theorem x3cClause_terminal_attachment_colors
    (group : X3CClauseTerminalGroup) :
    [X3CClauseTerminal.color
        (X3CClauseTerminal.attachmentElement group .first),
      X3CClauseTerminal.color
        (X3CClauseTerminal.attachmentElement group .second),
      X3CClauseTerminal.color
        (X3CClauseTerminal.attachmentElement group .third)] =
      match group with
      | .top => [.red, .blue, .green]
      | .left => [.blue, .green, .red]
      | .right => [.green, .red, .blue] := by
  cases group <;> native_decide

/-- The two incidence descriptions agree. -/
theorem x3cClause_mem_neighbors_iff_mem_references
    (set : X3CClauseSet) (element : X3CClauseElement) :
    set ∈ element.neighbors ↔ element ∈ set.references := by
  cases set <;>
    cases element with
    | internal value => cases value <;> native_decide
    | terminal value =>
        rcases value with ⟨group, slot⟩
        cases group <;> cases slot <;> native_decide

/-- Every set in the clause core contains exactly three elements. -/
theorem x3cClauseSet_reference_length (set : X3CClauseSet) :
    set.references.length = 3 := by
  cases set <;> rfl

/-- Every set in the clause core contains three distinct elements. -/
theorem x3cClauseSet_references_nodup (set : X3CClauseSet) :
    set.references.Nodup := by
  cases set <;> native_decide

/-- Every internal element has degree three. -/
theorem x3cClauseInternal_degree_three (element : X3CClauseInternal) :
    element.neighbors.length = 3 := by
  cases element <;> rfl

/-- Every open terminal element has degree two inside the clause core. -/
theorem x3cClauseTerminal_degree_two (element : X3CClauseTerminal) :
    element.neighbors.length = 2 := by
  rcases element with ⟨group, slot⟩
  cases group <;> cases slot <;> rfl

/-- A selected family of the nine sets is an exact cover relative to the
three all-or-none external terminal choices. -/
def X3CClauseCoreHolds
    (selected : X3CClauseSet → Bool)
    (external : X3CClauseTerminalGroup → Bool) : Prop :=
  (∀ element : X3CClauseInternal, PeriodicOneInThree.ExactlyOne
      (element.neighbors.map selected)) ∧
    ∀ group : X3CClauseTerminalGroup,
      ∀ slot : X3CClauseTerminalSlot,
        PeriodicOneInThree.ExactlyOne
          (external group ::
            (X3CClauseTerminal.neighbors ⟨group, slot⟩).map selected)

instance
    (selected : X3CClauseSet → Bool)
    (external : X3CClauseTerminalGroup → Bool) :
    Decidable (X3CClauseCoreHolds selected external) := by
  unfold X3CClauseCoreHolds
  infer_instance

/-- Package three Boolean terminal choices as a function. -/
def x3cClauseExternalAssignment
    (top left right : Bool) : X3CClauseTerminalGroup → Bool
  | .top => top
  | .left => left
  | .right => right

/-- A canonical cover of the clause core for each possible external
terminal.  In the lettering of Figure 5, the three covers are `EFI` when
the top terminal is external, `BDH` when the left terminal is external, and
`ACG` when the right terminal is external.  The all-false fallback is used
only when the external values do not satisfy exact-one. -/
def x3cClauseCoreSelection
    (top left right : Bool) : X3CClauseSet → Bool :=
  if top then
    fun set => set ∈
      ([.leftMiddle, .rightMiddle, .bottom] : List X3CClauseSet)
  else if left then
    fun set => set ∈
      ([.topLeftInner, .topRightOuter, .bottomRight] :
        List X3CClauseSet)
  else if right then
    fun set => set ∈
      ([.topLeftOuter, .topRightInner, .bottomLeft] :
        List X3CClauseSet)
  else
    fun _ => false

/-- The canonical three-set selection covers the clause core whenever its
external terminals satisfy exact-one. -/
theorem x3cClauseCoreSelection_holds
    (top left right : Bool)
    (exactlyOne :
      PeriodicOneInThree.ExactlyOne [top, left, right]) :
    X3CClauseCoreHolds
      (x3cClauseCoreSelection top left right)
      (x3cClauseExternalAssignment top left right) := by
  cases top <;> cases left <;> cases right
  all_goals
    simp [PeriodicOneInThree.ExactlyOne] at exactlyOne
  all_goals native_decide

/-- Exhaustive truth table for the nine-set core. -/
private theorem exists_x3cClauseCoreHolds_assignment_iff
    (top left right : Bool) :
    (∃ selected : X3CClauseSet → Bool,
        X3CClauseCoreHolds selected
          (x3cClauseExternalAssignment top left right)) ↔
      PeriodicOneInThree.ExactlyOne [top, left, right] := by
  cases top <;> cases left <;> cases right <;> native_decide

/-- The Figure 5 clause core admits an exact cover precisely when exactly one
of its three terminals is covered externally. -/
theorem exists_x3cClauseCoreHolds_iff
    (external : X3CClauseTerminalGroup → Bool) :
    (∃ selected, X3CClauseCoreHolds selected external) ↔
      PeriodicOneInThree.ExactlyOne
        [external .top, external .left, external .right] := by
  let assignment :=
    x3cClauseExternalAssignment
      (external .top) (external .left) (external .right)
  have externalEq : external = assignment := by
    funext group
    cases group <;> rfl
  rw [externalEq]
  exact exists_x3cClauseCoreHolds_assignment_iff _ _ _

end PlanarThreeDM
end LeanTrominoes
