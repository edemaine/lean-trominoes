/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionTranslation

/-! # Joining unit-subdivision direction words -/

namespace LeanTrominoes
namespace Gadget

open PeriodicOrthocrossing

private theorem unitSubdivisionDirections_append_tail_aux
    (first second : Cell) (rest target : List Cell)
    (boundary :
      (first :: second :: rest).getLast? = target.head?) :
    unitSubdivisionDirections
        ((first :: second :: rest) ++ target.tail) =
      unitSubdivisionDirections (first :: second :: rest) ++
        unitSubdivisionDirections target := by
  induction rest generalizing first second with
  | nil =>
      cases target with
      | nil => simp at boundary
      | cons targetFirst targetRest =>
          have pointEq : second = targetFirst := by
            simpa using boundary
          subst targetFirst
          simp [unitSubdivisionDirections]
  | cons third rest induction =>
      have tailBoundary :
          (second :: third :: rest).getLast? = target.head? := by
        simpa using boundary
      have tail := induction second third tailBoundary
      simp only [List.cons_append] at tail
      simp only [List.cons_append]
      rw [unitSubdivisionDirections]
      conv_rhs => rw [unitSubdivisionDirections]
      rw [tail]
      simp only [List.append_assoc]

/-- Joining two polylines at their common boundary concatenates their exact
segment-major direction words. -/
theorem unitSubdivisionDirections_joinPolylines
    {first second : List Cell}
    (firstLength : 2 ≤ first.length)
    (boundary : first.getLast? = second.head?) :
    unitSubdivisionDirections (joinPolylines first second) =
      unitSubdivisionDirections first ++
        unitSubdivisionDirections second := by
  cases first with
  | nil => simp at firstLength
  | cons first rest =>
      cases rest with
      | nil => simp at firstLength
      | cons next rest =>
          exact unitSubdivisionDirections_append_tail_aux
            first next rest second boundary

end Gadget
end LeanTrominoes
