/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEnumeration

/-! # Structural numeric names for the actual typed 3DM elements -/

namespace LeanTrominoes.PeriodicCNFStripReduction.TypedElementCode

open Gadget PlanarThreeDM PeriodicPlanarOneInThreeToThreeDM

variable {Variable : Type*}

/-- The compiler reserves disjoint finite tags for the three colors. -/
def variableBlock (key : Nat) (color : WireColor) (kind : VariableConnectorKind) : List Nat :=
  let tag := match color with | .red => 0 | .green => 4 | .blue => 8
  match kind with
  | .fixedRed => [key * 32 + tag, key * 32 + (1 + tag), key * 32 + (2 + tag)]
  | .fixedGreen | .fixedBlue => [key * 32 + tag]

/-- Internal, top, left, and right clause elements occupy four further tags. -/
def clauseBlock (index : Nat) (color : WireColor) : List Nat :=
  let tag := match color with | .red => 16 | .green => 20 | .blue => 24
  [index * 32 + tag, index * 32 + (1 + tag),
    index * 32 + (2 + tag), index * 32 + (3 + tag)]

def red (key : Variable × OccurrenceSlot → Nat) : RedElement Variable → Nat
  | .cycleLink atom slot => key (atom, slot) * 32
  | .fixedRedInternal atom slot .middleRung => key (atom, slot) * 32 + 1
  | .fixedRedInternal atom slot .topAuxiliary => key (atom, slot) * 32 + 2
  | .clauseInternal index => index * 32 + 16
  | .clauseTerminal index .top => index * 32 + 17
  | .clauseTerminal index .left => index * 32 + 18
  | .clauseTerminal index .right => index * 32 + 19

def green (key : Variable × OccurrenceSlot → Nat) : GreenElement Variable → Nat
  | .ordinaryInternal atom slot _ => key (atom, slot) * 32 + 4
  | .fixedRedInternal atom slot .leftRung => key (atom, slot) * 32 + 4
  | .fixedRedInternal atom slot .topRightLink => key (atom, slot) * 32 + 5
  | .fixedRedInternal atom slot .bottomRightLink => key (atom, slot) * 32 + 6
  | .clauseInternal index => index * 32 + 20
  | .clauseTerminal index .top => index * 32 + 21
  | .clauseTerminal index .left => index * 32 + 22
  | .clauseTerminal index .right => index * 32 + 23

def blue (key : Variable × OccurrenceSlot → Nat) : BlueElement Variable → Nat
  | .ordinaryInternal atom slot _ => key (atom, slot) * 32 + 8
  | .fixedRedInternal atom slot .topLeftLink => key (atom, slot) * 32 + 8
  | .fixedRedInternal atom slot .bottomLeftLink => key (atom, slot) * 32 + 9
  | .fixedRedInternal atom slot .rightRung => key (atom, slot) * 32 + 10
  | .clauseInternal index => index * 32 + 24
  | .clauseTerminal index .top => index * 32 + 25
  | .clauseTerminal index .left => index * 32 + 26
  | .clauseTerminal index .right => index * 32 + 27

variable [DecidableEq Variable]

/-- All actual red local elements have precisely the compiler's structural tags. -/
theorem map_occurrenceRedElements (source : PeriodicCNF Variable)
    (key : Variable × OccurrenceSlot → Nat) (atom : Variable) (slot : OccurrenceSlot) :
    (occurrenceRedElements source atom slot).map (red key) =
      variableBlock (key (atom, slot)) .red (occurrenceConnectorKind source atom slot) := by
  cases kind : occurrenceConnectorKind source atom slot <;>
    simp [occurrenceRedElements, red, variableBlock, kind]

theorem map_occurrenceGreenElements (source : PeriodicCNF Variable)
    (key : Variable × OccurrenceSlot → Nat) (atom : Variable) (slot : OccurrenceSlot) :
    (occurrenceGreenElements source atom slot).map (green key) =
      variableBlock (key (atom, slot)) .green (occurrenceConnectorKind source atom slot) := by
  cases kind : occurrenceConnectorKind source atom slot <;>
    simp [occurrenceGreenElements, green, variableBlock, kind]

theorem map_occurrenceBlueElements (source : PeriodicCNF Variable)
    (key : Variable × OccurrenceSlot → Nat) (atom : Variable) (slot : OccurrenceSlot) :
    (occurrenceBlueElements source atom slot).map (blue key) =
      variableBlock (key (atom, slot)) .blue (occurrenceConnectorKind source atom slot) := by
  cases kind : occurrenceConnectorKind source atom slot <;>
    simp [occurrenceBlueElements, blue, variableBlock, kind]

/-- The typed red enumeration retains the complete variable-prefix and clause-suffix order. -/
theorem map_redElements (source : PeriodicCNF Variable)
    (key : Variable × OccurrenceSlot → Nat) :
    (redElements source).map (red key) =
      (occurrenceEntries source).flatMap (fun entry =>
        variableBlock (key entry) .red (occurrenceConnectorKind source entry.1 entry.2)) ++
      (List.range source.clauses.length).flatMap (fun index => clauseBlock index .red) := by
  simp only [redElements, List.map_append, List.map_flatMap, map_occurrenceRedElements,
    occurrenceEntries, List.flatMap_assoc, List.flatMap_map]
  rfl

theorem map_greenElements (source : PeriodicCNF Variable)
    (key : Variable × OccurrenceSlot → Nat) :
    (greenElements source).map (green key) =
      (occurrenceEntries source).flatMap (fun entry =>
        variableBlock (key entry) .green (occurrenceConnectorKind source entry.1 entry.2)) ++
      (List.range source.clauses.length).flatMap (fun index => clauseBlock index .green) := by
  simp only [greenElements, List.map_append, List.map_flatMap, map_occurrenceGreenElements,
    occurrenceEntries, List.flatMap_assoc, List.flatMap_map]
  rfl

theorem map_blueElements (source : PeriodicCNF Variable)
    (key : Variable × OccurrenceSlot → Nat) :
    (blueElements source).map (blue key) =
      (occurrenceEntries source).flatMap (fun entry =>
        variableBlock (key entry) .blue (occurrenceConnectorKind source entry.1 entry.2)) ++
      (List.range source.clauses.length).flatMap (fun index => clauseBlock index .blue) := by
  simp only [blueElements, List.map_append, List.map_flatMap, map_occurrenceBlueElements,
    occurrenceEntries, List.flatMap_assoc, List.flatMap_map]
  rfl


/-- Structural names in the actual one-color element enumeration. -/
def elements (source : PeriodicCNF Variable) (key : Variable × OccurrenceSlot → Nat)
    (color : WireColor) : List Nat :=
  match color with
  | .red => (redElements source).map (red key)
  | .green => (greenElements source).map (green key)
  | .blue => (blueElements source).map (blue key)

/-- Every color uses the same occurrence-entry and clause order. -/
theorem elements_eq_blocks (source : PeriodicCNF Variable)
    (key : Variable × OccurrenceSlot → Nat) (color : WireColor) :
    elements source key color =
      (occurrenceEntries source).flatMap (fun entry =>
        variableBlock (key entry) color (occurrenceConnectorKind source entry.1 entry.2)) ++
      (List.range source.clauses.length).flatMap (fun index => clauseBlock index color) := by
  cases color with
  | red => exact map_redElements source key
  | green => exact map_greenElements source key
  | blue => exact map_blueElements source key

end LeanTrominoes.PeriodicCNFStripReduction.TypedElementCode
