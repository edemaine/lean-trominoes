import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMClauseTerminalIncidences
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMThreeStrandRouting

/-!
# Physical ribbon lanes for the planar 3DM reduction

The three colors of a 3DM occurrence are semantic element colors, whereas
the three parallel tracks in a thickened source incidence are physical
lanes.  These orders cannot be identified uniformly.  The three clause
terminals expose the cyclic color orders red-blue-green, blue-green-red, and
green-red-blue, and the matching variable connector kinds have the same
three rotations.

This file records the required permutation explicitly.  Physical lanes are
still named by `WireColor`: red, green, and blue mean the standard distances
40, 44, and 48.  `ribbonLaneForColor` maps a semantic color to one of those
three physical tracks.  It is a permutation for every connector kind, and
the fixed connector color always occupies the outermost blue lane.
-/

namespace LeanTrominoes
namespace PlanarThreeDM

open Gadget

namespace VariableConnectorKind

/-- Physical ribbon lane occupied by one semantic element color.

The fixed-blue connector uses the identity order.  The fixed-red and
fixed-green connectors use the two nontrivial cyclic rotations. -/
def ribbonLaneForColor :
    VariableConnectorKind → WireColor → WireColor
  | .fixedRed, .red => .blue
  | .fixedRed, .green => .red
  | .fixedRed, .blue => .green
  | .fixedGreen, .red => .green
  | .fixedGreen, .green => .blue
  | .fixedGreen, .blue => .red
  | .fixedBlue, color => color

/-- Semantic color occupying one named physical ribbon lane. -/
def colorForRibbonLane :
    VariableConnectorKind → WireColor → WireColor
  | .fixedRed, .red => .green
  | .fixedRed, .green => .blue
  | .fixedRed, .blue => .red
  | .fixedGreen, .red => .blue
  | .fixedGreen, .green => .red
  | .fixedGreen, .blue => .green
  | .fixedBlue, lane => lane

@[simp]
theorem colorForRibbonLane_ribbonLaneForColor
    (kind : VariableConnectorKind) (color : WireColor) :
    kind.colorForRibbonLane (kind.ribbonLaneForColor color) = color := by
  cases kind <;> cases color <;> rfl

@[simp]
theorem ribbonLaneForColor_colorForRibbonLane
    (kind : VariableConnectorKind) (lane : WireColor) :
    kind.ribbonLaneForColor (kind.colorForRibbonLane lane) = lane := by
  cases kind <;> cases lane <;> rfl

/-- Each connector kind assigns distinct semantic colors to distinct
physical tracks. -/
theorem ribbonLaneForColor_injective
    (kind : VariableConnectorKind) :
    Function.Injective kind.ribbonLaneForColor := by
  intro first second equal
  have := congrArg kind.colorForRibbonLane equal
  simpa using this

@[simp]
theorem ribbonLaneForColor_eq_iff
    (kind : VariableConnectorKind)
    (first second : WireColor) :
    kind.ribbonLaneForColor first =
        kind.ribbonLaneForColor second ↔
      first = second :=
  kind.ribbonLaneForColor_injective.eq_iff

/-- The color fixed geometrically by every connector kind occupies the
outermost of the three standard physical lanes. -/
@[simp]
theorem ribbonLaneForColor_fixedColor
    (kind : VariableConnectorKind) :
    kind.ribbonLaneForColor kind.fixedColor = .blue := by
  cases kind <;> rfl

end VariableConnectorKind
end PlanarThreeDM

namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

/-- Physical lane assignment at one clause terminal group. -/
def clauseRibbonLaneForColor
    (group : X3CClauseTerminalGroup)
    (color : WireColor) : WireColor :=
  (variableConnectorKindForTerminal group).ribbonLaneForColor color

/-- Reading a clause terminal in its advertised attachment order encounters
the physical lanes from outermost to innermost.  Thus the three different
semantic RGB rotations all meet one uniform ribbon interface. -/
theorem clauseAttachment_ribbonLaneOrder
    (group : X3CClauseTerminalGroup) :
    [clauseRibbonLaneForColor group
        (X3CClauseTerminal.attachmentElement group .first).color,
      clauseRibbonLaneForColor group
        (X3CClauseTerminal.attachmentElement group .second).color,
      clauseRibbonLaneForColor group
        (X3CClauseTerminal.attachmentElement group .third).color] =
      [.blue, .green, .red] := by
  cases group <;> rfl

/-- The explicit terminal chosen for a semantic color uses the same
group-dependent physical lane assignment. -/
theorem terminalElementForColor_ribbonLane
    (group : X3CClauseTerminalGroup)
    (color : WireColor) :
    clauseRibbonLaneForColor group
        (terminalElementForColor color group).color =
      clauseRibbonLaneForColor group color := by
  cases group <;> cases color <;> rfl

/-- Physical lane assignment selected by one source occurrence. -/
def occurrenceRibbonLaneForColor
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (color : WireColor) : WireColor :=
  (occurrenceConnectorKind source atom slot).ribbonLaneForColor color

/-- The occurrence-side definition is exactly the clause-terminal
assignment selected by that occurrence's literal position. -/
theorem occurrenceRibbonLaneForColor_eq_clause
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (color : WireColor) :
    occurrenceRibbonLaneForColor source atom slot color =
      clauseRibbonLaneForColor
        (terminalGroupOfLiteralIndex
          (occurrenceLiteralIndex source atom slot))
        color := by
  rfl

/-- For a fixed source occurrence, semantic colors remain distinct after
assignment to physical lanes. -/
theorem occurrenceRibbonLaneForColor_injective
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot) :
    Function.Injective
      (occurrenceRibbonLaneForColor source atom slot) :=
  (occurrenceConnectorKind source atom slot).ribbonLaneForColor_injective

/-- Physical lane selected by one packaged active occurrence strand. -/
def routedRibbonLane
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (entry : ActiveOccurrenceEntry source)
    (color : WireColor) : WireColor :=
  occurrenceRibbonLaneForColor
    source entry.1.1 entry.1.2 color

/-- Semantic colors remain distinct within a packaged occurrence. -/
theorem routedRibbonLane_injective
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (entry : ActiveOccurrenceEntry source) :
    Function.Injective (routedRibbonLane source entry) :=
  occurrenceRibbonLaneForColor_injective
    source entry.1.1 entry.1.2

@[simp]
theorem routedRibbonLane_eq_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (entry : ActiveOccurrenceEntry source)
    (first second : WireColor) :
    routedRibbonLane source entry first =
        routedRibbonLane source entry second ↔
      first = second :=
  (routedRibbonLane_injective source entry).eq_iff

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
