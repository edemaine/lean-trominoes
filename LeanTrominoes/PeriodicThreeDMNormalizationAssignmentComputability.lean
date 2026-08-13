/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationRasterLocationComputability

/-!
# Primitive-recursive normalized cell assignments

This module turns each internal point of a normalized route into its finite-
torus location and local routing-cell type.
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

abbrev RouteInteriorAssignmentsInput :=
  (Nat × WireColor) × List Cell

theorem routeInteriorAssignments_primrec :
    Primrec fun input : RouteInteriorAssignmentsInput =>
      routeInteriorAssignments input.1.1 input.1.2 input.2 := by
  have step : Primrec₂ fun (parameters : Nat × WireColor)
      (state : Cell × List Cell × List NormalizedCellAssignment) =>
      if 2 ≤ state.2.1.length then
        (rasterLocation parameters.1 (state.2.1.getD 0 (0, 0)),
          routingCellTypeAt state.1
            (state.2.1.getD 0 (0, 0))
            (state.2.1.getD 1 (0, 0)) parameters.2) ::
          state.2.2
      else [] := by
    change Primrec fun combined :
        (Nat × WireColor) ×
          (Cell × List Cell × List NormalizedCellAssignment) =>
      if 2 ≤ combined.2.2.1.length then
        (rasterLocation combined.1.1
            (combined.2.2.1.getD 0 (0, 0)),
          routingCellTypeAt combined.2.1
            (combined.2.2.1.getD 0 (0, 0))
            (combined.2.2.1.getD 1 (0, 0)) combined.1.2) ::
          combined.2.2.2
      else []
    have tail : Primrec fun combined :
        (Nat × WireColor) ×
          (Cell × List Cell × List NormalizedCellAssignment) =>
        combined.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have enough : PrimrecPred fun combined :
        (Nat × WireColor) ×
          (Cell × List Cell × List NormalizedCellAssignment) =>
        2 ≤ combined.2.2.1.length :=
      Primrec.nat_le.comp (Primrec.const 2)
        (Primrec.list_length.comp tail)
    let itemAt (index : Nat) : Primrec fun combined :
        (Nat × WireColor) ×
          (Cell × List Cell × List NormalizedCellAssignment) =>
        combined.2.2.1.getD index (0, 0) :=
      (Primrec.list_getD (0, 0)).comp tail (Primrec.const index)
    have location : Primrec fun combined :
        (Nat × WireColor) ×
          (Cell × List Cell × List NormalizedCellAssignment) =>
        rasterLocation combined.1.1
          (combined.2.2.1.getD 0 (0, 0)) :=
      rasterLocation_primrec.comp
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst) (itemAt 0))
    have cellType : Primrec fun combined :
        (Nat × WireColor) ×
          (Cell × List Cell × List NormalizedCellAssignment) =>
        routingCellTypeAt combined.2.1
          (combined.2.2.1.getD 0 (0, 0))
          (combined.2.2.1.getD 1 (0, 0)) combined.1.2 :=
      routingCellTypeAt_primrec.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp Primrec.snd)
            (Primrec.pair (itemAt 0) (itemAt 1)))
          (Primrec.snd.comp Primrec.fst))
    have assignment : Primrec fun combined :
        (Nat × WireColor) ×
          (Cell × List Cell × List NormalizedCellAssignment) =>
        (rasterLocation combined.1.1
            (combined.2.2.1.getD 0 (0, 0)),
          routingCellTypeAt combined.2.1
            (combined.2.2.1.getD 0 (0, 0))
            (combined.2.2.1.getD 1 (0, 0)) combined.1.2) :=
      Primrec.pair location cellType
    exact Primrec.ite enough
      (Primrec.list_cons.comp assignment
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.const [])
  have recursion := Primrec.list_rec
    (f := fun input : RouteInteriorAssignmentsInput => input.2)
    (g := fun _ => ([] : List NormalizedCellAssignment))
    (h := fun input state =>
      if 2 ≤ state.2.1.length then
        (rasterLocation input.1.1 (state.2.1.getD 0 (0, 0)),
          routingCellTypeAt state.1
            (state.2.1.getD 0 (0, 0))
            (state.2.1.getD 1 (0, 0)) input.1.2) ::
          state.2.2
      else [])
    Primrec.snd (Primrec.const [])
      (step.comp
        (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)
  exact recursion.of_eq fun input => by
    fun_induction routeInteriorAssignments input.1.1 input.1.2 input.2 with
    | case1 before current after rest induction =>
        change
          (rasterLocation input.1.1 current,
            routingCellTypeAt before current after input.1.2) :: _ =
          (rasterLocation input.1.1 current,
            routingCellTypeAt before current after input.1.2) :: _
        exact congrArg
          (List.cons
            (rasterLocation input.1.1 current,
              routingCellTypeAt before current after input.1.2))
          induction
    | case2 points noTriple =>
        cases points with
        | nil => rfl
        | cons before tail =>
            cases tail with
            | nil => rfl
            | cons current tail =>
                cases tail with
                | nil => rfl
                | cons after rest =>
                    exact (noTriple before current after rest rfl).elim

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
