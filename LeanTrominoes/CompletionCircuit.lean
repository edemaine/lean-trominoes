/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionSquareNetwork

/-! # Finite Boolean circuits for normalized orientation cells

The nine circuit kinds forget wire colors, which do not affect the local
orientation relation. West and south signals are complemented when read as
inward orientations, so adjacent circuit signals agree.
-/

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks

inductive CircuitKind
  | blank | horizontal | vertical | northwest | southeast | northeast | southwest | copy | exactone
  deriving DecidableEq, Fintype, Repr

def CircuitKind.portEnabled (kind : CircuitKind) (p : Fin 4) : Bool :=
  match kind with
  | .blank => false
  | .horizontal => p.val = 1 || p.val = 2
  | .vertical => p.val = 0 || p.val = 3
  | .northwest => p.val = 0 || p.val = 2
  | .southeast => p.val = 1 || p.val = 3
  | .northeast => p.val = 0 || p.val = 1
  | .southwest => p.val = 2 || p.val = 3
  | .copy | .exactone => p.val < 3

def CircuitKind.SourceRelation (kind : CircuitKind) (external : Fin 4 → Bool) : Prop :=
  (∀ p, kind.portEnabled p = false → external p = false) ∧
  match kind with
  | .blank => True
  | .horizontal => external 1 = external 2
  | .vertical => external 0 = external 3
  | .northwest => external 0 = external 2
  | .southeast => external 1 = external 3
  | .northeast => external 0 ≠ external 1
  | .southwest => external 2 ≠ external 3
  | .copy => !(external 2) = external 0 ∧ external 0 = external 1
  | .exactone => [!(external 2),external 0,external 1].count true = 1

instance (kind : CircuitKind) (external : Fin 4 → Bool) : Decidable (kind.SourceRelation external) := by
  unfold CircuitKind.SourceRelation
  split <;> infer_instance

abbrev CircuitSignal := Option (Fin 4)

def CircuitSignal.eval (signal : CircuitSignal) (value : Fin 4 → Bool) : Bool :=
  match signal with | none => false | some k => value k

structure CircuitNode where
  position : Cell
  label : Fin 24
  signals : List CircuitSignal
  wire : Option (Fin 4)
  parent : Option Nat
  parentPort : Fin 4
  readPort : Fin 4
  deriving DecidableEq, Repr

def CircuitNode.signal (node : CircuitNode) (p : Fin 4) : CircuitSignal :=
  (node.signals[p.val]?).getD none

def CircuitNode.values (node : CircuitNode) (value : Fin 4 → Bool) (p : Fin 4) : Bool :=
  (node.signal p).eval value

structure Circuit where
  nodes : List CircuitNode
  clauseCount : Nat
  anchors : List Nat
  terminals : List CircuitSignal
  deriving DecidableEq, Repr

namespace Circuit

def size : Nat := 64

def Inside (c : Cell) : Prop := 0 ≤ c.1 ∧ c.1 < size ∧ 0 ≤ c.2 ∧ c.2 < size
instance (c : Cell) : Decidable (Inside c) := by unfold Inside; infer_instance

def terminalPoint (p : Fin 4) : Cell :=
  match p.val with
  | 0 => (32,0)
  | 1 => (63,32)
  | 2 => (0,32)
  | _ => (32,63)

def lookup (circuit : Circuit) (c : Cell) : Option CircuitNode :=
  circuit.nodes.find? fun node => node.position == c

def labelAt (circuit : Circuit) (c : Cell) : Fin 24 :=
  ((circuit.lookup c).map CircuitNode.label).getD 0

def signalAt (circuit : Circuit) (c : Cell) (p : Fin 4) : CircuitSignal :=
  ((circuit.lookup c).map (fun node => node.signal p)).getD none

def terminal (circuit : Circuit) (p : Fin 4) : CircuitSignal :=
  (circuit.terminals[p.val]?).getD none

def Formula (circuit : Circuit) (value : Fin 4 → Bool) : Prop :=
  ∀ node ∈ circuit.nodes.take circuit.clauseCount, Network node.label (node.values value)

instance (circuit : Circuit) (value : Fin 4 → Bool) : Decidable (circuit.Formula value) := by
  unfold Formula
  infer_instance

def TerminalRelation (circuit : Circuit) (external value : Fin 4 → Bool) : Prop :=
  ∀ p, external p = (circuit.terminal p).eval value

instance (circuit : Circuit) (external value : Fin 4 → Bool) : Decidable (circuit.TerminalRelation external value) := by
  unfold TerminalRelation
  infer_instance

def TruthTableCorrect (circuit : Circuit) (kind : CircuitKind) : Prop :=
  ∀ external : Fin 4 → Bool, kind.SourceRelation external ↔
    ∃ value : Fin 4 → Bool, circuit.Formula value ∧ circuit.TerminalRelation external value

instance (circuit : Circuit) (kind : CircuitKind) : Decidable (circuit.TruthTableCorrect kind) := by
  unfold TruthTableCorrect
  infer_instance

end Circuit
end LeanTrominoes.CompletionPattern.LBricks
