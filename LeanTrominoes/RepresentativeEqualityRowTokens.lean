/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RepresentativeEqualityRows

/-! # Encoded stable representative rows -/

namespace LeanTrominoes
namespace RepresentativeEqualityRowTokens

def tokensAux (rowIndex : Nat) (rows : List (List Bool)) :
    List DelimitedBinaryWords.Token :=
  DelimitedBinaryWords.encode
    ⟨RepresentativeEqualityRows.rowsAux rowIndex rows⟩

@[simp] theorem tokensAux_nil (rowIndex : Nat) :
    tokensAux rowIndex [] = [] := by
  simp [tokensAux, DelimitedBinaryWords.encode]

theorem tokensAux_cons_selected (rowIndex : Nat) (row : List Bool)
    (rows : List (List Bool))
    (isSelected : RepresentativeEqualityRows.selected rowIndex row = true) :
    tokensAux rowIndex (row :: rows) =
      DelimitedBinaryWords.wordTokens row ++
        tokensAux (rowIndex + 1) rows := by
  simp [tokensAux, RepresentativeEqualityRows.rowsAux, isSelected,
    DelimitedBinaryWords.encode]

theorem tokensAux_cons_rejected (rowIndex : Nat) (row : List Bool)
    (rows : List (List Bool))
    (isRejected : RepresentativeEqualityRows.selected rowIndex row = false) :
    tokensAux rowIndex (row :: rows) = tokensAux (rowIndex + 1) rows := by
  simp [tokensAux, RepresentativeEqualityRows.rowsAux, isRejected,
    DelimitedBinaryWords.encode]

end RepresentativeEqualityRowTokens
end LeanTrominoes
