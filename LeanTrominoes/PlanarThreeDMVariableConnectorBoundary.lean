import LeanTrominoes.PlanarThreeDMVariableOccurrenceGadget

/-!
# A common boundary contract for planar variable connectors

The fixed-red Figure 6 detour and the ordinary fixed-green/fixed-blue
occurrence modules have different internal graphs, but expose the same
logical interface after orienting their two red continuation ports
consistently:

* the continuation states are complementary; and
* all three RGB connector elements carry the first continuation state.

This file packages that interface and proves, by exhaustive checking of the
underlying finite gadgets, that all three connector kinds realize exactly
that relation.
-/

namespace LeanTrominoes
namespace PlanarThreeDM

/-- Which connector element occupies the fixed geometric position. -/
inductive VariableConnectorKind
  | fixedRed
  | fixedGreen
  | fixedBlue
  deriving DecidableEq, Repr, Fintype

namespace VariableConnectorKind

/-- Color occupying the fixed geometric position of this connector kind. -/
def fixedColor : VariableConnectorKind → Gadget.WireColor
  | .fixedRed => .red
  | .fixedGreen => .green
  | .fixedBlue => .blue

end VariableConnectorKind

/-- The three Boolean values visible at the boundary of one occurrence
module.  `first` and `second` are the two red cycle continuations;
`connector` is the common state of the RGB terminal. -/
structure VariableConnectorBoundary where
  first : Bool
  second : Bool
  connector : Bool
  deriving DecidableEq, Repr

/-- Realization by the corresponding finite colored gadget.

For Figure 6, `bottomLeft` is chosen as the first continuation so its state
agrees with the connector.  The other two kinds use the ordinary module's
`first` continuation directly. -/
def VariableConnectorBoundary.Realizable
    (kind : VariableConnectorKind)
    (boundary : VariableConnectorBoundary) : Prop :=
  match kind with
  | .fixedRed =>
      ∃ selected : FixedRedConnectorTriple → Bool,
        FixedRedConnectorHolds selected ∧
          boundary.first = selected .bottomLeft ∧
          boundary.second = selected .topLeft ∧
          boundary.connector = selected .auxiliary
  | .fixedGreen =>
      ∃ selected : VariableOccurrenceTriple → Bool,
        VariableOccurrenceHolds selected ∧
          boundary.first = selected .first ∧
          boundary.second = selected .second ∧
          boundary.connector = selected .auxiliary
  | .fixedBlue =>
      ∃ selected : VariableOccurrenceTriple → Bool,
        VariableOccurrenceHolds selected ∧
          boundary.first = selected .first ∧
          boundary.second = selected .second ∧
          boundary.connector = selected .auxiliary

instance
    (kind : VariableConnectorKind)
    (boundary : VariableConnectorBoundary) :
    Decidable (boundary.Realizable kind) := by
  unfold VariableConnectorBoundary.Realizable
  cases kind <;> infer_instance

/-- The canonical boundary with a specified connector signal. -/
def VariableConnectorBoundary.canonical
    (value : Bool) : VariableConnectorBoundary :=
  ⟨value, !value, value⟩

/-- All three finite gadgets realize exactly the same boundary relation. -/
theorem variableConnectorBoundary_realizable_iff
    (kind : VariableConnectorKind)
    (boundary : VariableConnectorBoundary) :
    boundary.Realizable kind ↔
      boundary.first = !boundary.second ∧
        boundary.connector = boundary.first := by
  rcases boundary with ⟨first, second, connector⟩
  cases kind <;> cases first <;> cases second <;> cases connector <;>
    native_decide

/-- Every connector kind realizes both canonical signal values. -/
theorem variableConnectorBoundary_canonical_realizable
    (kind : VariableConnectorKind) (value : Bool) :
    (VariableConnectorBoundary.canonical value).Realizable kind := by
  rw [variableConnectorBoundary_realizable_iff]
  cases value <;> native_decide

/-- A realizable connector has a unique boundary once its common RGB signal
is known. -/
theorem variableConnectorBoundary_eq_canonical
    {kind : VariableConnectorKind}
    {boundary : VariableConnectorBoundary}
    (realizable : boundary.Realizable kind) :
    boundary =
      VariableConnectorBoundary.canonical boundary.connector := by
  have relation :=
    (variableConnectorBoundary_realizable_iff kind boundary).mp realizable
  rcases boundary with ⟨first, second, connector⟩
  cases first <;> cases second <;> cases connector <;>
    simp_all [VariableConnectorBoundary.canonical]

/-- Exchange the two red continuation ports without changing the RGB
terminal.  This is the reflected attachment used for a negated occurrence in
Dyer--Frieze Figure 4(b). -/
def VariableConnectorBoundary.swapContinuations
    (boundary : VariableConnectorBoundary) :
    VariableConnectorBoundary :=
  ⟨boundary.second, boundary.first, boundary.connector⟩

/-- Realize a positive occurrence directly and a negative occurrence after
exchanging its continuation ports. -/
def VariableConnectorBoundary.RealizableFor
    (kind : VariableConnectorKind) (polarity : Bool)
    (boundary : VariableConnectorBoundary) : Prop :=
  if polarity then
    boundary.Realizable kind
  else
    boundary.swapContinuations.Realizable kind

instance
    (kind : VariableConnectorKind) (polarity : Bool)
    (boundary : VariableConnectorBoundary) :
    Decidable (boundary.RealizableFor kind polarity) := by
  unfold VariableConnectorBoundary.RealizableFor
  infer_instance

/-- Truth value carried from a variable-cycle phase to a signed literal
occurrence. -/
def variableConnectorLiteralSignal
    (variableValue polarity : Bool) : Bool :=
  variableValue == polarity

/-- A signed connector still has complementary continuation states, while
its RGB signal is the value of the represented signed literal. -/
theorem variableConnectorBoundary_realizableFor_iff
    (kind : VariableConnectorKind) (polarity : Bool)
    (boundary : VariableConnectorBoundary) :
    boundary.RealizableFor kind polarity ↔
      boundary.first = !boundary.second ∧
        boundary.connector =
          variableConnectorLiteralSignal boundary.first polarity := by
  rcases boundary with ⟨first, second, connector⟩
  cases kind <;> cases polarity <;> cases first <;> cases second <;>
    cases connector <;> native_decide

/-- Canonical signed boundary at one variable-cycle phase. -/
def VariableConnectorBoundary.canonicalFor
    (variableValue polarity : Bool) : VariableConnectorBoundary :=
  ⟨variableValue, !variableValue,
    variableConnectorLiteralSignal variableValue polarity⟩

/-- Every connector kind realizes the canonical boundary for either
polarity and either variable value. -/
theorem variableConnectorBoundary_canonicalFor_realizable
    (kind : VariableConnectorKind)
    (variableValue polarity : Bool) :
    (VariableConnectorBoundary.canonicalFor
      variableValue polarity).RealizableFor kind polarity := by
  rw [variableConnectorBoundary_realizableFor_iff]
  cases variableValue <;> cases polarity <;> native_decide

end PlanarThreeDM
end LeanTrominoes
