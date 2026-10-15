/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Tromino.Finite.FiniteTrominoVerifierBackend

/-! # Regression checks for whole-footprint certificate verification -/
namespace LeanTrominoes.FiniteExactCoverVerifier.Examples

/-- Empty regions and empty certificates are allowed. -/
example : check true ⟨[],[],[],[]⟩=true := by decide +kernel

/-- An empty word is a cell name, not an empty footprint. -/
example : check true ⟨[[]],[[[]]],[],[true]⟩=true := by decide +kernel

/-- Repeated region descriptions do not require covering a cell twice. -/
example : check true ⟨[[],[]],[[[]]],[],[true]⟩=true := by decide +kernel

/-- Overlapping selected tiles are rejected. -/
example : check false ⟨[[]],[[[]],[[]]],[],[true,true]⟩=false := by decide +kernel

/-- A repeated cell within one purported footprint is rejected too. -/
example : check false ⟨[[]],[[[],[]]],[],[true]⟩=false := by decide +kernel

/-- A short certificate cannot silently cover an unselected cell. -/
example : check true ⟨[[],[true]],[[[]],[[true]]],[],[true]⟩=false := by decide +kernel

/-- Completion permits protrusions beyond the covered region. -/
example : check false ⟨[[]],[[[],[true]]],[],[true]⟩=true := by decide +kernel

/-- Finite-region tiling rejects the same protruding footprint. -/
example : check true ⟨[[]],[[[],[true]]],[],[true]⟩=false := by decide +kernel

/-- Covering a prefilled tile's cells with different tiles does not retain it. -/
example : check false ⟨[[],[true]],[[[]],[[true]]],[[[],[true]]],[true,true]⟩=false := by decide +kernel

/-- Extra unused certificate bits do not change the selected footprints. -/
example : check true ⟨[[]],[[[]]],[],[true,false,true]⟩=true := by decide +kernel

end LeanTrominoes.FiniteExactCoverVerifier.Examples

namespace LeanTrominoes.Tromino.FiniteVerifier.Examples

def bitsFor (t : Tromino) (cells : List Cell) (tiles : Finset (Finset Cell)) : List Bool :=
  (candidateTiles t cells).map fun tile => decide (tile∈tiles)

def iCells : List Cell := [(0,0),(1,0),(2,0)]
def lCells : List Cell := [(-2,3),(-1,3),(-2,4)]

#guard check true .I iCells [] (bitsFor .I iCells {iCells.toFinset})
#guard check true .L lCells [] (bitsFor .L lCells {lCells.toFinset})
#guard check true .I ((0,0)::iCells) []
  (bitsFor .I ((0,0)::iCells) {iCells.toFinset})
#guard !check true .I iCells [] []
#guard check false .I [(0,0)] [iCells.toFinset]
  (bitsFor .I [(0,0)] {iCells.toFinset})
#guard !check true .I [(0,0)] [] (bitsFor .I [(0,0)] {iCells.toFinset})
#guard !check false .I iCells [{(0,0)}] (bitsFor .I iCells {iCells.toFinset})

end LeanTrominoes.Tromino.FiniteVerifier.Examples
