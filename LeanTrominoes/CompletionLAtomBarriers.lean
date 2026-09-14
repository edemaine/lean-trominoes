/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionLBricks
import LeanTrominoes.CompletionBarrier

/-! # Six local barrier checks for the L subbricks

Only a few cells supplied by adjacent subbricks are needed in addition to
the atom's own prefill. These additional cells lie on its boundary rows.
-/

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks

set_option maxRecDepth 16384
set_option maxHeartbeats 0

def Atom.fixedList : Atom → List Cell
  | .equal => LEqBoundary.fixedCells
  | .negate => LNegBoundary.fixedCells
  | .plugTop => LPlugTopBoundary.fixedCells
  | .plugBottom => LPlugBotBoundary.fixedCells
  | .copy => LDup.fixedCells
  | .clause => L3Sat.fixedCells

def Atom.fixed (a : Atom) : Finset Cell :=
  ⟨(↑a.fixedList : Multiset Cell),by cases a <;> decide +kernel⟩

theorem Atom.fixed_eq (a : Atom) : a.fixed = a.pattern.fixedRegion := by
  cases a <;> decide +kernel

def Atom.boundary : Atom → Finset Cell
  | .copy => {(2,0),(8,0),(14,0),(20,0),(2,12),(8,12),(14,12),(20,12)}
  | .clause => {(2,0),(8,0),(14,0),(20,0),(2,6),(8,6),(14,6),(20,6)}
  | _ => {(2,0),(8,0),(2,6),(8,6)}

def Atom.extraBarrier : Atom → Finset Cell
  | .equal => {(0,0),(1,0),(3,0),(6,6),(7,6),(9,6)}
  | .negate => {(1,0),(3,0),(6,6),(7,6),(9,6)}
  | .plugTop => {(6,6),(7,6),(9,6)}
  | .plugBottom => {(0,0),(1,0),(3,0),(4,0),(5,0)}
  | .copy => {(0,0),(1,0),(3,0),(6,12),(7,12),(9,12),(10,12),(11,12),
      (12,0),(13,0),(15,0),(18,12),(19,12),(21,12)}
  | .clause => {(1,0),(3,0),(4,0),(5,0),(6,6),(7,6),(9,6),(10,6),
      (12,0),(13,0),(15,0),(16,0),(17,0)}

def Atom.core (a : Atom) : Finset Cell := (a.pattern.region \ a.fixed) \ a.boundary

/-- With the listed neighboring cells filled, every new L tromino meeting
the atom's interior is contained in its region. -/
theorem Atom.avoidance (a : Atom) :
    CompletionBarrier.AvoidanceCheck .L a.core a.pattern.region (a.fixed ∪ a.extraBarrier) := by
  cases a <;> decide +kernel

/-- Cells supplied by the rows of bricks immediately above and below. -/
def externalSkin : Finset Cell :=
  {(0,0),(1,0),(3,0),(4,0),(5,0),(12,0),(13,0),(15,0),(16,0),(17,0),
   (6,36),(7,36),(9,36),(10,36),(11,36),(18,36),(19,36),(21,36),(22,36),(23,36)}

end LeanTrominoes.CompletionPattern.LBricks
