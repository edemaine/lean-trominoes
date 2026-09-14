/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionLEqBoundaryData
import LeanTrominoes.CompletionLNegBoundaryData
import LeanTrominoes.CompletionLPlugTopBoundaryData
import LeanTrominoes.CompletionLPlugBotBoundaryData
import LeanTrominoes.CompletionLDupData
import LeanTrominoes.CompletionL3SatData
import LeanTrominoes.TilingTranslation

/-! # A fixed-size L-tromino brick palette

Bricks have width 24 and height 36, with the shared connector cells on
rows 0 and 36. Outer not gadgets enforce Boolean connectors. The inner
minor gadgets choose clause signs. Plugs terminate unused copy ports.
-/

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks

inductive Atom | equal | negate | plugTop | plugBottom | copy | clause
  deriving DecidableEq, Repr

def Atom.pattern : Atom → Pattern
  | .equal => LEqBoundary.pattern
  | .negate => LNegBoundary.pattern
  | .plugTop => LPlugTopBoundary.pattern
  | .plugBottom => LPlugBotBoundary.pattern
  | .copy => LDup.pattern
  | .clause => L3Sat.pattern

def Atom.motif : Atom → List (Placement Unit)
  | .equal => LEqBoundary.prefillList
  | .negate => LNegBoundary.prefillList
  | .plugTop => LPlugTopBoundary.prefillList
  | .plugBottom => LPlugBotBoundary.prefillList
  | .copy => LDup.prefillList
  | .clause => L3Sat.prefillList

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
  if positive i port then .negate else .equal

/-- Each entry gives the subbrick type and the offset of its upper left corner. -/
def layout (i : Fin 24) : List (Atom × Cell) :=
  [(upperOuter i 0,(0,0)),(upperOuter i 1,(12,0)),
   (inner i 0,(0,6)),(inner i 1,(12,6))] ++
  (if i.val < 16 then [(.copy,(0,12))]
   else [(.equal,(0,12)),(.equal,(12,12)),(.clause,(0,18))]) ++
  [(inner i 2,(0,24)),(inner i 3,(12,24)),
   (lowerOuter i 2,(0,30)),(lowerOuter i 3,(12,30))]

def atomRegion (entry : Atom × Cell) : Finset Cell :=
  entry.1.pattern.region.image (Cell.add entry.2)

def atomMotif (entry : Atom × Cell) : List (Placement Unit) :=
  entry.1.motif.map fun p => p.shift entry.2

def motif (i : Fin 24) : List (Placement Unit) := (layout i).flatMap atomMotif

def region (i : Fin 24) : Finset Cell :=
  ((layout i).map atomRegion).foldr (· ∪ ·) ∅

def pattern (i : Fin 24) : Pattern := ⟨.L,region i,(motif i).toFinset⟩

/-- The two cells of each of the four external connectors. -/
def boundary : Finset Cell :=
  {(2,0),(8,0),(14,0),(20,0),(2,36),(8,36),(14,36),(20,36)}

end LeanTrominoes.CompletionPattern.LBricks
