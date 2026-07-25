import LeanTrominoes.PlanarThreeDMVariableCycle

/-!
# Composed semantics of the planar 3DM gadgets

This file connects the physical terminal order of the colored clause core to
the three variable-connector kinds, and packages the clause core's external
boundary relation.  It then states the exact local semantics used by the
planar reduction:

* a three-port clause is realizable exactly when exactly one port is true;
* a two-port clause has the same relation when the unused third terminal is
  left unconnected; and
* substituting signed variable signals recovers the source exact-one literal
  clause verbatim.
-/

namespace LeanTrominoes
namespace PlanarThreeDM

/-- Connector kind whose fixed element matches one physical clause
terminal. -/
def variableConnectorKindForTerminal :
    X3CClauseTerminalGroup → VariableConnectorKind
  | .top => .fixedRed
  | .left => .fixedBlue
  | .right => .fixedGreen

/-- The connector selected for each terminal has exactly its fixed attachment
color. -/
theorem variableConnectorKindForTerminal_fixedColor
    (group : X3CClauseTerminalGroup) :
    (variableConnectorKindForTerminal group).fixedColor =
      X3CClauseTerminal.fixedAttachmentColor group := by
  cases group <;> rfl

/-- Exact-cover realizability of a clause core with three external terminal
signals. -/
def X3CClauseCoreRealizable
    (top left right : Bool) : Prop :=
  ∃ selected : X3CClauseSet → Bool,
    X3CClauseCoreHolds selected
      (x3cClauseExternalAssignment top left right)

/-- The three-terminal clause core implements exact-one. -/
theorem x3cClauseCoreRealizable_iff
    (top left right : Bool) :
    X3CClauseCoreRealizable top left right ↔
      PeriodicOneInThree.ExactlyOne [top, left, right] := by
  unfold X3CClauseCoreRealizable
  rw [exists_x3cClauseCoreHolds_iff]
  rfl

/-- Leaving the right terminal unconnected gives the required two-literal
exact-one relation.  Its three elements retain their two internal
incidences, so this introduces no degree-one element. -/
theorem x3cTwoClauseCoreRealizable_iff
    (first second : Bool) :
    X3CClauseCoreRealizable first second false ↔
      PeriodicOneInThree.ExactlyOne [first, second] := by
  rw [x3cClauseCoreRealizable_iff]
  cases first <;> cases second <;> native_decide

/-- Clause-core realizability after substituting the truth values of three
signed source literals. -/
def ThreeSignedLiteralClauseRealizable
    (firstValue secondValue thirdValue : Bool)
    (firstPolarity secondPolarity thirdPolarity : Bool) : Prop :=
  X3CClauseCoreRealizable
    (variableConnectorLiteralSignal firstValue firstPolarity)
    (variableConnectorLiteralSignal secondValue secondPolarity)
    (variableConnectorLiteralSignal thirdValue thirdPolarity)

/-- The composed three-literal gadget has exactly the source exact-one
semantics. -/
theorem threeSignedLiteralClauseRealizable_iff
    (firstValue secondValue thirdValue : Bool)
    (firstPolarity secondPolarity thirdPolarity : Bool) :
    ThreeSignedLiteralClauseRealizable
        firstValue secondValue thirdValue
        firstPolarity secondPolarity thirdPolarity ↔
      PeriodicOneInThree.ExactlyOne
        [variableConnectorLiteralSignal firstValue firstPolarity,
          variableConnectorLiteralSignal secondValue secondPolarity,
          variableConnectorLiteralSignal thirdValue thirdPolarity] := by
  exact x3cClauseCoreRealizable_iff _ _ _

/-- Clause-core realizability after substituting two signed source literals
and leaving the third terminal unconnected. -/
def TwoSignedLiteralClauseRealizable
    (firstValue secondValue : Bool)
    (firstPolarity secondPolarity : Bool) : Prop :=
  X3CClauseCoreRealizable
    (variableConnectorLiteralSignal firstValue firstPolarity)
    (variableConnectorLiteralSignal secondValue secondPolarity)
    false

/-- The composed two-literal gadget has exactly the source exact-one
semantics. -/
theorem twoSignedLiteralClauseRealizable_iff
    (firstValue secondValue : Bool)
    (firstPolarity secondPolarity : Bool) :
    TwoSignedLiteralClauseRealizable
        firstValue secondValue firstPolarity secondPolarity ↔
      PeriodicOneInThree.ExactlyOne
        [variableConnectorLiteralSignal firstValue firstPolarity,
          variableConnectorLiteralSignal secondValue secondPolarity] := by
  exact x3cTwoClauseCoreRealizable_iff _ _

end PlanarThreeDM
end LeanTrominoes
