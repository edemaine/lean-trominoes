/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIGuardedEqBoundaryData
import LeanTrominoes.CompletionIGuardedNegBoundaryData
import LeanTrominoes.CompletionIGuardedPlugTopBoundaryData
import LeanTrominoes.CompletionIGuardedPlugBotBoundaryData
import LeanTrominoes.CompletionIGuardedDupData
import LeanTrominoes.CompletionIGuardedTftsatData
import LeanTrominoes.TilingTranslation

/-! # A fixed-size guarded I-tromino brick palette

Bricks have width 36 and height 162, with the shared connector cells on
rows 0 and 162. Outer not gadgets enforce Boolean connectors. The inner
minor gadgets choose clause signs. Plugs terminate unused copy ports.
-/

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

inductive Atom | equal | negate | plugTop | plugBottom | copy | clause
  deriving DecidableEq, Repr

def Atom.pattern : Atom → Pattern
  | .equal => IGuardedEqBoundary.pattern
  | .negate => IGuardedNegBoundary.pattern
  | .plugTop => IGuardedPlugTopBoundary.pattern
  | .plugBottom => IGuardedPlugBotBoundary.pattern
  | .copy => IGuardedDup.pattern
  | .clause => IGuardedTftsat.pattern

def Atom.motif : Atom → List (Placement Unit)
  | .equal => IGuardedEqBoundary.prefillList
  | .negate => IGuardedNegBoundary.prefillList
  | .plugTop => IGuardedPlugTopBoundary.prefillList
  | .plugBottom => IGuardedPlugBotBoundary.prefillList
  | .copy => IGuardedDup.prefillList
  | .clause => IGuardedTftsat.prefillList

/-- A palette index below 16 selects which copy ports are active. Indices
16 through 23 select the signs of a three-input clause. -/
def bit (n weight : Nat) : Bool := n / weight % 2 == 1

def active (i : Fin 24) (port : Fin 4) : Bool :=
  if i.val < 16 then bit i.val (2 ^ (3 - port.val)) else port.val < 3

/-- A true sign makes the corresponding external clause literal positive. -/
def positive (i : Fin 24) (port : Fin 4) : Bool :=
  if i.val < 16 || port.val == 3 then false
  else bit (i.val - 16) (2 ^ (2 - port.val))

def upperOuter (i : Fin 24) (port : Fin 4) : Atom :=
  if active i port then .negate else .plugTop

def lowerOuter (i : Fin 24) (port : Fin 4) : Atom :=
  if active i port then .negate else .plugBottom

def inner (i : Fin 24) (port : Fin 4) : Atom :=
  if positive i port != (i.val ≥ 16 && port.val == 1) then .negate else .equal

/-- The I clause has a negated middle input; the inner minor corrects its sign.
Each entry gives the subbrick type and the offset of its upper left corner. -/
def layout (i : Fin 24) : List (Atom × Cell) :=
  [(upperOuter i 0,(0,0)),(upperOuter i 1,(18,0)),
   (inner i 0,(0,27)),(inner i 1,(18,27))] ++
  (if i.val < 16 then [(.copy,(0,54))]
   else [(.equal,(0,54)),(.equal,(18,54)),(.clause,(0,81))]) ++
  [(inner i 2,(0,108)),(inner i 3,(18,108)),
   (lowerOuter i 2,(0,135)),(lowerOuter i 3,(18,135))]

def atomRegion (entry : Atom × Cell) : Finset Cell :=
  entry.1.pattern.region.image (Cell.add entry.2)

def atomMotif (entry : Atom × Cell) : List (Placement Unit) :=
  entry.1.motif.map fun p => p.shift entry.2

def motif (i : Fin 24) : List (Placement Unit) := (layout i).flatMap atomMotif

def region (i : Fin 24) : Finset Cell :=
  ((layout i).map atomRegion).foldr (· ∪ ·) ∅

def pattern (i : Fin 24) : Pattern := ⟨.I,region i,(motif i).toFinset⟩

/-- The two cells of each of the four external connectors. -/
def boundary : Finset Cell :=
  {(5,0),(14,0),(23,0),(32,0),(5,162),(14,162),(23,162),(32,162)}

end LeanTrominoes.CompletionPattern.IBricks
