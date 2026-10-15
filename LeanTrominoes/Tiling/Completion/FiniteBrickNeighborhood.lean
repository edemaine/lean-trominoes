/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.CellData

/-! # Finite neighborhoods in the brick index lattice -/
namespace LeanTrominoes.CompletionPattern

def BrickNear (radius : Int) (center other : Cell) : Prop :=
  center.1-radius≤other.1 ∧ other.1≤center.1+radius ∧
    center.2-radius≤other.2 ∧ other.2≤center.2+radius
end LeanTrominoes.CompletionPattern
