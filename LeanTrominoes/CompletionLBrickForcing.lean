/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionLMinorForcing

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks

set_option maxHeartbeats 0
set_option maxRecDepth 16384

def ForcingNetwork (i : Fin 24) (proper : Cell → Prop) : Prop :=
  ∀ entry ∈ layout i, entry.1.PortForcing
    (proper (Cell.add (entryMicroOffset entry) (0,0)))
    (proper (Cell.add (entryMicroOffset entry) (0,1)))

def ForcingPorts (i : Fin 24) (proper : Cell → Prop) : Prop :=
  ∀ entry ∈ layout i, ∀ p ∈ entry.1.portCells, proper (Cell.add (entryMicroOffset entry) p)

/-- The outer not/plug rows force Booleanity, the inner rows propagate it,
and clause padding propagates it once more to the major subbrick. -/
theorem forcing_all_ports (i : Fin 24) (proper : Cell → Prop)
    (h : ForcingNetwork i proper) : ForcingPorts i proper := by
  have enumerated : ∀ j : Fin 24, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 := by decide +kernel
  rcases enumerated i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [ForcingNetwork,ForcingPorts,layout,upperOuter,lowerOuter,inner,
      active,positive,bit,entryMicroOffset,Atom.portCells,Atom.PortForcing,Cell.add] at h ⊢
    aesop

/-- Every connector used by a subbrick of a completed plane is Boolean. -/
theorem all_canonical_ports_proper {palette : Cell → Fin 24} {completed : Set (Finset Cell)}
    (h : Tromino.L.IsFootprintTiling Set.univ completed) (retained : globalPrescribed palette ⊆ completed)
    (location : Cell) : ∀ entry ∈ layout (palette location), ∀ p ∈ entry.1.portCells,
      ProperConnector palette completed (Cell.add (atomMicroOffset location entry) p) := by
  let proper : Cell → Prop := fun p => ProperConnector palette completed (Cell.add (brickMicroOrigin location) p)
  have associate (entry : Atom × Cell) (p : Cell) :
      Cell.add (atomMicroOffset location entry) p =
        Cell.add (brickMicroOrigin location) (Cell.add (entryMicroOffset entry) p) := by
    apply Prod.ext <;> dsimp [atomMicroOffset,Cell.add] <;> omega
  have forcing : ForcingNetwork (palette location) proper := by
    intro entry he
    have supplied := canonical_minor_forcing h retained (Occurrence.mk location entry he)
    dsimp only at supplied
    rw [associate entry (0,0),associate entry (0,1)] at supplied
    exact supplied
  intro entry he p hp
  rw [associate]
  exact forcing_all_ports (palette location) proper forcing entry he p hp

end LeanTrominoes.CompletionPattern.LBricks
