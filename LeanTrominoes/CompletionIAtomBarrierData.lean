/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIBricks
import LeanTrominoes.CompletionConflictBarrier

/-! # Boundary barriers for guarded I-tromino subbricks -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

set_option maxRecDepth 16384
set_option maxHeartbeats 0

def Atom.fixedList : Atom → List Cell
  | .equal => IGuardedEqBoundary.fixedCells
  | .negate => IGuardedNegBoundary.fixedCells
  | .plugTop => IGuardedPlugTopBoundary.fixedCells
  | .plugBottom => IGuardedPlugBotBoundary.fixedCells
  | .copy => IGuardedDup.fixedCells
  | .clause => IGuardedTftsat.fixedCells

def Atom.fixed (a : Atom) : Finset Cell :=
  ⟨(↑a.fixedList : Multiset Cell),CompletionCellOrder.nodup _ (by cases a <;> decide +kernel)⟩

def Atom.boundary : Atom → Finset Cell
  | .copy => {(5,0),(14,0),(23,0),(32,0),(5,54),(14,54),(23,54),(32,54)}
  | .clause => {(5,0),(14,0),(23,0),(32,0),(5,27),(14,27),(23,27),(32,27)}
  | _ => {(5,0),(14,0),(5,27),(14,27)}

def Atom.available : Atom → Finset Cell
  | .copy => {(5,2),(5,52),(14,2),(14,52),(23,2),(23,52),(32,2),(32,52)}
  | .clause => {(5,2),(5,25),(14,2),(14,25),(23,2),(23,25),(32,2),(32,25)}
  | _ => {(5,2),(5,25),(14,2),(14,25)}

def Atom.core (a : Atom) : Finset Cell := (a.pattern.region \ a.fixed) \ a.boundary

end LeanTrominoes.CompletionPattern.IBricks
