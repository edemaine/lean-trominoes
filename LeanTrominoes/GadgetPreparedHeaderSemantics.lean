/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetPreparedHeaderData

/-! # Exact semantics of the prepared strip-header stream -/

namespace LeanTrominoes
namespace GadgetPreparedHeaderEmitter

open GadgetPixelFiniteTokens

theorem flatMap_replicate_const {Source Target : Type}
    (source : Source) (count : Nat) (target : List Target) :
    (List.replicate count source).flatMap (fun _ => target) =
      (List.replicate count target).flatten := by
  induction count with
  | zero => simp
  | succ count induction => simp [List.replicate_succ, induction]

theorem flatMap_units {Target : Type} (units : List Unit)
    (target : List Target) :
    units.flatMap (fun _ => target) =
      (List.replicate units.length target).flatten := by
  induction units with
  | nil => simp
  | cons item units induction =>
      simp only [List.flatMap_cons, induction, List.length_cons]
      rw [List.replicate_succ, List.flatten_cons]

theorem flatMap_replicate_apply {Source Target : Type}
    (source : Source) (count : Nat) (function : Source → List Target) :
    (List.replicate count source).flatMap function =
      (List.replicate count (function source)).flatten := by
  induction count with
  | zero => simp
  | succ count induction => simp [List.replicate_succ, induction]

theorem replicate_flatten_replicate {Target : Type}
    (outer inner : Nat) (target : Target) :
    (List.replicate outer (List.replicate inner target)).flatten =
      List.replicate (outer * inner) target := by
  induction outer with
  | zero => simp
  | succ outer induction =>
      rw [List.replicate_succ, List.flatten_cons, induction,
        ← List.replicate_add]
      congr 1
      ring

theorem flatten_replicate_singleton {Target : Type}
    (count : Nat) (target : Target) :
    (List.replicate count [target]).flatten =
      List.replicate count target := by
  induction count with
  | zero => simp
  | succ count induction => simp [List.replicate_succ, induction]

/-- The emitted stream is exactly the height and width header for
`P = factor * grid.length`. -/
@[simp] theorem preparedHeader_eq (factor : Nat) (grid : List Unit) :
    preparedHeader factor grid =
      headerField (3 * (factor * grid.length) + 1) ++
        headerField (factor * grid.length) := by
  unfold preparedHeader
  rw [addEnd_eq, addPeriod_addSentinel_eq, addSentinel_eq]
  simp only [List.flatMap_append, List.flatMap_map, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, block]
  rw [flatMap_units, replicate_flatten_replicate,
    flatMap_replicate_apply]
  simp only
  rw [flatten_replicate_singleton]
  rw [show grid.length * (3 * factor) =
      3 * (factor * grid.length) by ring]
  unfold headerField
  rw [List.replicate_add]
  simp [List.append_assoc]

end GadgetPreparedHeaderEmitter
end LeanTrominoes
