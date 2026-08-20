/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PolylineDefaultEndpoints
import LeanTrominoes.Computability

/-! # Computability of total polyline endpoint projections -/

noncomputable section

namespace LeanTrominoes

theorem polylineHeadD_primrec : Primrec polylineHeadD := by
  exact (Primrec.option_getD.comp Primrec.list_head?
    (Primrec.const ((0, 0) : Cell))).of_eq fun _ => rfl

theorem polylineLastD_primrec : Primrec polylineLastD := by
  have last : Primrec fun route : List Cell => route.reverse.head? :=
    Primrec.list_head?.comp (Primrec.list_reverse.comp Primrec.id)
  exact (Primrec.option_getD.comp last
    (Primrec.const ((0, 0) : Cell))).of_eq fun route => by
      simp [polylineLastD, List.getLastD_eq_getLast?]

end LeanTrominoes
