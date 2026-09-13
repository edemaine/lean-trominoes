/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripSearchSetup
import LeanTrominoes.TranslationStripCycleSearch

/-! # Orientation-restricted strip SearchSetup certificates

The input adapters and relation-independent bounds reuse the existing strip solver.
-/

namespace LeanTrominoes.TranslationStrip.Savitch
open PolyominoStripWindow PolyominoStripWindow.Savitch

open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits FiniteState
open BoundedArithmetic BoundedArithmetic.Expr

def searchCode : Code := cycleCode.comp searchInputCode

def searchBudget (height bound space : Nat) : Nat :=
  cycleBudget (stateBits Bool height bound) space+
    searchInputCoefficient*(space+stateBits Bool height bound+2)

theorem search_eval (cells : Bool → List Cell) (height bound : Nat) (bounded : Bounded (Raw.tiles cells) bound) :
    searchCode.eval (suffix cells height bound) = pure [(TranslationStrip.tilingCheck cells height bound).toNat] := by
  have run := cycle_eval cells height bound (stateBits Bool height bound) bounded
  simpa [searchCode,searchInput_eval,Part.bind_eq_bind,TranslationStrip.tilingCheck] using run

theorem search_fits (cells : Bool → List Cell) (height bound : Nat) (bounded : Bounded (Raw.tiles cells) bound) :
    EvaluatorCodeFits searchCode (suffix cells height bound) [(TranslationStrip.tilingCheck cells height bound).toNat]
      (searchBudget height bound (encodedListSpace (suffix cells height bound))) := by
  exact comp (cycle_fits cells height bound (stateBits Bool height bound) bounded) (searchInput_fits cells height bound)

end LeanTrominoes.TranslationStrip.Savitch
