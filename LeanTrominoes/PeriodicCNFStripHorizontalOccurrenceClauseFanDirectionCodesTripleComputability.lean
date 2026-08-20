/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseFanData

/-! # Computability of clause direction-code list decoding -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseDirectionCodesTriple_primrec :
    Primrec horizontalOccurrenceClauseDirectionCodesTriple := by
  have codeAt (index : Nat) : Primrec fun codes : List (Fin 5) =>
      codes.getD index 0 :=
    Primrec.list_getD (0 : Fin 5) |>.comp
      Primrec.id (Primrec.const index)
  exact Primrec.pair (codeAt 0)
    (Primrec.pair (codeAt 1) (codeAt 2))

end PeriodicCNFStripReduction
end LeanTrominoes
