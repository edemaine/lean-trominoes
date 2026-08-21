/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RepresentativeEqualityRowsListExecution
import LeanTrominoes.RepresentativeEqualityRowsLocalTimeBounds

/-! # Clock bound for processing a list of representative rows -/

namespace LeanTrominoes
namespace RepresentativeEqualityRowsMachine

theorem rowsTime_le (rowIndex : Nat) (rows : List (List Bool)) :
    rowsTime rowIndex rows ≤
      5 * rows.length *
        (rowIndex + (DelimitedBinaryWords.encode ⟨rows⟩).length + 1) := by
  induction rows generalizing rowIndex with
  | nil => simp [rowsTime, DelimitedBinaryWords.encode]
  | cons row rows induction =>
      let rowLength := (DelimitedBinaryWords.wordTokens row).length
      let tailLength := (DelimitedBinaryWords.encode ⟨rows⟩).length
      let budget := rowIndex + (rowLength + tailLength) + 1
      have encodedLength :
          (DelimitedBinaryWords.encode ⟨row :: rows⟩).length =
            rowLength + tailLength := by
        simp [rowLength, tailLength, DelimitedBinaryWords.encode]
      have tailBudget :
          rowIndex + 1 + tailLength + 1 ≤ budget := by
        have rowLengthMin : 2 ≤ rowLength := by
          simp [rowLength]
        simp [budget]
        omega
      have tailBound := induction (rowIndex + 1)
      have tailBound' :
          rowsTime (rowIndex + 1) rows ≤
            5 * rows.length * budget :=
        tailBound.trans
          (Nat.mul_le_mul_left (5 * rows.length) tailBudget)
      have rowBound := oneRowTime_le rowIndex row
      have rowBound' : oneRowTime rowIndex row ≤ 5 * budget := by
        have rowLengthMin : 2 ≤ rowLength := by
          simp [rowLength]
        have rowBoundSimple :
            oneRowTime rowIndex row ≤
              3 * (rowIndex + (row.length + 2)) + 6 := by
          simpa using rowBound
        simp [budget, rowLength]
        omega
      calc
        rowsTime rowIndex (row :: rows) =
            rowsTime (rowIndex + 1) rows + oneRowTime rowIndex row := rfl
        _ ≤ 5 * rows.length * budget + 5 * budget :=
          Nat.add_le_add tailBound' rowBound'
        _ = 5 * (row :: rows).length * budget := by
          simp only [List.length_cons]
          ring
        _ = 5 * (row :: rows).length *
            (rowIndex +
              (DelimitedBinaryWords.encode ⟨row :: rows⟩).length + 1) := by
          rw [encodedLength]

end RepresentativeEqualityRowsMachine
end LeanTrominoes
