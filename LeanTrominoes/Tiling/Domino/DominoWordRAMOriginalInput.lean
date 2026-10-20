/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalGeometry
import LeanTrominoes.Tiling.Domino.DominoWordRAMEmpty

/-! # Original valid binary presentations at a fixed dimension -/
namespace LeanTrominoes.Domino.WordRAM

/-- The promise requires a nonsingular period basis and distinct represented
lattice sites. The encoded words contain only the raw presentation. -/
abbrev Input (d : ℕ) := (n : ℕ) × {B : BasisData n d // B.Valid}

def encode {d : ℕ} (input : Input d) : List ℤ := words input.2.val

def inputSize {d : ℕ} (input : Input d) : ℕ := size input.2.val

def predicate {d : ℕ} (input : Input d) : Prop := Tileable (input.2.val.chart input.2.property).region

end LeanTrominoes.Domino.WordRAM
