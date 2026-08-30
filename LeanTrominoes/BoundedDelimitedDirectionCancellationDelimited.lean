/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoundedDelimitedDirectionCancellationData
import LeanTrominoes.DelimitedRouteJoinSemantics
import LeanTrominoes.FiniteStateTransducerSemantics

/-! # Composition over route-delimited direction batches -/

namespace LeanTrominoes
namespace BoundedDelimitedDirectionCancellation

/-- A complete delimited direction word always resets the cancellation
control state to empty. -/
theorem scan_delimited_fst (directions : List AxisDirection) :
    (FiniteStateTransducer.scan transition .empty
      (DelimitedRouteJoin.delimited directions)).1 = .empty := by
  unfold DelimitedRouteJoin.delimited
  rw [FiniteStateTransducer.scan_append]
  cases FiniteStateTransducer.scan transition .empty
      (directions.map fun direction =>
        (.direction direction : Token)) with
  | mk control emitted =>
      cases control <;>
        simp [FiniteStateTransducer.scan, transition]

/-- The scan of a complete delimited word records its complete output and
returns to the initial control state. -/
theorem scan_delimited (directions : List AxisDirection) :
    FiniteStateTransducer.scan transition .empty
        (DelimitedRouteJoin.delimited directions) =
      (.empty, output (DelimitedRouteJoin.delimited directions)) := by
  let scanned := FiniteStateTransducer.scan transition .empty
    (DelimitedRouteJoin.delimited directions)
  have control : scanned.1 = .empty :=
    scan_delimited_fst directions
  have outputEq :
      output (DelimitedRouteJoin.delimited directions) = scanned.2 := by
    unfold output FiniteStateTransducer.output
    change scanned.2 ++ finish scanned.1 = scanned.2
    rw [control]
    simp [finish]
  apply Prod.ext
  · exact control
  · simpa using outputEq.symm

/-- A completed route delimiter makes cancellation independent of every
following token. -/
theorem output_delimited_append
    (directions : List AxisDirection) (tokens : List Token) :
    output (DelimitedRouteJoin.delimited directions ++ tokens) =
      output (DelimitedRouteJoin.delimited directions) ++ output tokens := by
  unfold output FiniteStateTransducer.output
  rw [FiniteStateTransducer.scan_append, scan_delimited]
  simp [finish, List.append_assoc]

/-- Bounded cancellation acts route-by-route on a flat delimited batch. -/
theorem output_flatMap_delimited {α : Type}
    (values : List α) (directions : α → List AxisDirection) :
    output (values.flatMap fun value =>
        DelimitedRouteJoin.delimited (directions value)) =
      values.flatMap fun value =>
        output (DelimitedRouteJoin.delimited (directions value)) := by
  induction values with
  | nil =>
      simp [output, FiniteStateTransducer.output,
        FiniteStateTransducer.scan, finish]
  | cons value values induction =>
      simp only [List.flatMap_cons, output_delimited_append, induction]

end BoundedDelimitedDirectionCancellation
end LeanTrominoes
