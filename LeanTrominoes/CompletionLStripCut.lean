/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionLStripExterior
import LeanTrominoes.CompletionLBrickEquivalence

/-! # Cutting a blank-padded plane construction to its finite brick core -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks

set_option maxHeartbeats 2000000

theorem table_row_false (tables : Cell → BrickValues) (row : Int)
    (zero : ∀ location, location.2 = row → ∀ x : Fin 2, tables location x 0 = false) (x : Int) :
    globalTableValue tables (x,6*row) = false := by
  let location : Cell := ((x-row)/2,row)
  let i : Fin 2 := ⟨((x-row)%2).toNat,by omega⟩
  have eq : Cell.add (brickMicroOrigin location) ((i.val : Int),0) = (x,6*row) := by
    apply Prod.ext <;> dsimp [location,i,Cell.add,brickMicroOrigin] <;> omega
  have window := global_table_interior tables location ((i.val : Int),0)
    (by dsimp; omega)
  rw [eq] at window
  rw [window]
  simpa [tableValue,Nat.mod_eq_of_lt i.isLt] using zero location rfl i

theorem network_zero_values (v : Fin 4 → Bool) (h : Network 0 v) : ∀ p, v p = false := by
  have checked : ∀ v : Fin 4 → Bool, Network 0 v → ∀ p, v p = false := by decide +kernel
  exact checked v h

theorem core_completion_of_network (palette : Cell → Fin 24) (external : Cell → Fin 4 → Bool)
    (seams : ExternalSeams external) (valid : ∀ location, Network (palette location) (external location))
    (count : Int) (hn : 0 < count)
    (blankTop : ∀ location, location.2 = 0 → palette location = 0)
    (blankBottom : ∀ location, location.2 = count → palette location = 0) :
    Tromino.L.Completable (StripCaps.coreBand .L (36*count)) (bandPrescribed palette count) := by
  have original := valid
  choose core coreValid using valid
  let tables : Cell → BrickValues := fun location => witnessTable (palette location) (external location) (core location)
  have tableSeams : TableSeams tables := by
    intro location x
    change witnessTable _ _ _ x 6 = witnessTable _ _ _ (oppositeColumn x) 0
    rw [witness_table_bottom,witness_table_top]
    exact seams location x
  have realized : ∀ location, BrickBooleanRelation (palette location) (tables location) :=
    fun location => witness_table_valid _ _ _ (coreValid location)
  have rowFalse (row : Int) (blank : ∀ location, location.2 = row → palette location = 0) (x : Int) :
      globalTableValue tables (x,6*row) = false := by
    apply table_row_false tables row _ x
    intro location hy i
    have allFalse := network_zero_values (external location) (by simpa [blank location hy] using original location)
    change witnessTable _ _ _ i 0 = false
    rw [witness_table_top]
    exact allFalse _
  apply band_completion_of_states palette (globalTableValue tables) count hn
    (by simpa using rowFalse 0 blankTop) (rowFalse count blankBottom)
  intro o _
  rw [boolean_outside_local,Atom.boolean_completion_iff]
  exact global_entry_relation palette tables tableSeams realized o

theorem core_completion_iff_plane (palette : Cell → Fin 24) (count : Int) (hn : 0 < count)
    (blank : ∀ location, location.2 ≤ 0 ∨ count ≤ location.2 → palette location = 0) :
    Tromino.L.Completable (StripCaps.coreBand .L (36*count)) (bandPrescribed palette count) ↔
      Tromino.L.Completable Set.univ (globalPrescribed palette) := by
  constructor
  · exact plane_completion_of_core palette count hn (fun location outside => blank location (by
      unfold InBand at outside; omega))
  · intro completed
    obtain ⟨external,seams,valid⟩ := (completion_iff_brick_network palette).mp completed
    exact core_completion_of_network palette external seams valid count hn
      (fun location hy => blank location (by omega)) (fun location hy => blank location (by omega))

end LeanTrominoes.CompletionPattern.LBricks
