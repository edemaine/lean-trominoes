/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeTiling
import LeanTrominoes.PlusRefinement
import Mathlib.Data.Finset.Prod

/-! # Extruded and capped planar tiles -/

namespace LeanTrominoes.Polycube

/-- Extrude a planar shape through an explicit finite set of layers. -/
def extrude (shape : Polyomino) (layers : Finset Int) : Polycube := shape ×ˢ layers

@[simp] theorem mem_extrude (shape : Polyomino) (layers : Finset Int) (c : Voxel) :
    c ∈ extrude shape layers ↔ c.1 ∈ shape ∧ c.2 ∈ layers := Finset.mem_product

theorem extrude_card (shape : Polyomino) (layers : Finset Int) :
    (extrude shape layers).card = shape.card * layers.card := Finset.card_product _ _

/-- Add a cap to the extruded background; connectivity is proved separately. -/
def capped (shape cap : Polyomino) (layers : Finset Int) (capHeight : Int) : Polycube :=
  extrude shape layers ∪ extrude cap {capHeight}

@[simp] theorem mem_capped (shape cap : Polyomino) (layers : Finset Int)
    (capHeight : Int) (c : Voxel) :
    c ∈ capped shape cap layers capHeight ↔
      (c.1 ∈ shape ∧ c.2 ∈ layers) ∨ (c.1 ∈ cap ∧ c.2 = capHeight) := by
  simp [capped]

/-- The fixed 45-cube tile for full 3D, translated to layers 0, 1, 2. -/
def bumpyThree : Polycube := extrude PlusRefinement.bumpy {0, 1, 2}

theorem bumpyThree_card : bumpyThree.card = 45 := by decide

/-- The fixed 15-cube tile for the height-2 slab. -/
def bumpyOne : Polycube := extrude PlusRefinement.bumpy {0}

theorem bumpyOne_card : bumpyOne.card = 15 := by decide

end LeanTrominoes.Polycube
