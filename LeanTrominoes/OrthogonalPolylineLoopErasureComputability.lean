import LeanTrominoes.OrthogonalPolylineLoopErasure
import LeanTrominoes.PeriodicGridDrawingGeometryComputability
import LeanTrominoes.PeriodicThreeDMNormalizationGeometryComputability

/-!
# Computability of orthogonal-polyline loop erasure

`SimpleGraph.Walk.bypass` is phrased using dependent walks.  For executable
route construction, this module gives the equivalent proof-free list
algorithm: recursively erase the tail, then either prepend the new head or,
if it already occurs, drop everything before its first retained occurrence.
This identifies the list algorithm with `Walk.bypass.support` and proves that
the total orthogonal-polyline normalizer is primitive recursive.
-/

noncomputable section

namespace LeanTrominoes
namespace Computability

set_option maxHeartbeats 400000

/-- Proof-free loop erasure on a vertex list, with the same right-to-left
choice of retained path as `SimpleGraph.Walk.bypass`. -/
def listLoopErase {Vertex : Type*} [DecidableEq Vertex] :
    List Vertex → List Vertex
  | [] => []
  | head :: tail =>
      let erased := listLoopErase tail
      if head ∈ erased then
        erased.drop (erased.idxOf head)
      else
        head :: erased

/-- Proof-free list loop erasure is primitive recursive. -/
theorem listLoopErase_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (@listLoopErase Vertex _) := by
  have step : Primrec₂ fun (_input : List Vertex)
      (state : Vertex × List Vertex × List Vertex) =>
      if state.1 ∈ state.2.2 then
        state.2.2.drop (state.2.2.idxOf state.1)
      else
        state.1 :: state.2.2 := by
    change Primrec fun combined : List Vertex ×
        (Vertex × List Vertex × List Vertex) =>
      if combined.2.1 ∈ combined.2.2.2 then
        combined.2.2.2.drop
          (combined.2.2.2.idxOf combined.2.1)
      else
        combined.2.1 :: combined.2.2.2
    have head : Primrec fun combined : List Vertex ×
        (Vertex × List Vertex × List Vertex) =>
        combined.2.1 :=
      Primrec.fst.comp Primrec.snd
    have erased : Primrec fun combined : List Vertex ×
        (Vertex × List Vertex × List Vertex) =>
        combined.2.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have index : Primrec fun combined : List Vertex ×
        (Vertex × List Vertex × List Vertex) =>
        combined.2.2.2.idxOf combined.2.1 :=
      Primrec.list_idxOf.comp head erased
    have member : PrimrecPred fun combined : List Vertex ×
        (Vertex × List Vertex × List Vertex) =>
        combined.2.1 ∈ combined.2.2.2 := by
      exact (Primrec.nat_lt.comp index
        (Primrec.list_length.comp erased)).of_eq fun combined =>
          List.idxOf_lt_length_iff
    exact Primrec.ite member
      (Primrec.list_drop.comp index erased)
      (Primrec.list_cons.comp head erased)
  refine (Primrec.list_rec Primrec.id (Primrec.const []) step).of_eq ?_
  intro points
  change (List.recOn points [] fun head _tail erased =>
      if head ∈ erased then
        erased.drop (erased.idxOf head)
      else
        head :: erased) = listLoopErase points
  induction points with
  | nil => rfl
  | cons head tail induction =>
      simp [listLoopErase, induction]

/-- The list algorithm computes exactly the support selected by
`SimpleGraph.Walk.bypass`. -/
theorem listLoopErase_support_eq_bypass_support
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : SimpleGraph Vertex} {source target : Vertex}
    (walk : graph.Walk source target) :
    listLoopErase walk.support = walk.bypass.support := by
  induction walk with
  | nil => simp [listLoopErase, SimpleGraph.Walk.bypass]
  | @cons source next target adjacent tail induction =>
      simp only [SimpleGraph.Walk.support_cons, listLoopErase, induction,
        SimpleGraph.Walk.bypass]
      split_ifs with member
      · rw [SimpleGraph.Walk.dropUntil_eq_drop,
          SimpleGraph.Walk.support_copy,
          SimpleGraph.Walk.drop_support_eq_support_drop_min]
        have indexLe :
            tail.bypass.support.idxOf source ≤ tail.bypass.length := by
          rw [← Nat.lt_succ_iff]
          simpa only [SimpleGraph.Walk.length_support] using
            List.idxOf_lt_length_of_mem member
        rw [Nat.min_eq_left indexLe]
      · rfl

end Computability

namespace PeriodicOrthocrossing

/-- Orthogonality of an integer-grid polyline is primitive recursive. -/
theorem orthogonalPolyline_primrec :
    PrimrecPred OrthogonalPolyline := by
  have allAligned : PrimrecPred fun segments : List GridSegment =>
      ∀ segment ∈ segments, segment.IsAxisAligned :=
    GridSegment.isAxisAligned_primrec.forall_mem_list
  exact (allAligned.comp gridPolylineSegments_primrec).of_eq fun points =>
    orthogonalPolyline_iff_segments points |>.symm

end PeriodicOrthocrossing

namespace AxisDirection

/-- Certified walk loop erasure agrees with the proof-free list algorithm. -/
theorem eraseOrthogonalLoops_eq_listLoopErase
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    eraseOrthogonalLoops points nonempty orthogonal =
      Computability.listLoopErase (unitSubdividePolyline points) := by
  unfold eraseOrthogonalLoops
  rw [← Computability.listLoopErase_support_eq_bypass_support]
  simp only [orthogonalUnitWalk,
    SimpleGraph.Walk.support_ofSupport]

/-- The total loop-erasing orthogonal-polyline normalizer is primitive
recursive. -/
theorem normalizeOrthogonalPolyline_primrec :
    Primrec normalizeOrthogonalPolyline := by
  have nonempty : PrimrecPred fun points : List Cell => points ≠ [] :=
    (Primrec.eq.comp Primrec.id (Primrec.const [])).not
  have loopErased : Primrec fun points : List Cell =>
      Computability.listLoopErase (unitSubdividePolyline points) :=
    Computability.listLoopErase_primrec.comp
      PeriodicThreeDM.NormalizationCompiler.unitSubdividePolyline_primrec
  have algorithm := Primrec.ite nonempty
    (Primrec.ite PeriodicOrthocrossing.orthogonalPolyline_primrec
      loopErased Primrec.id)
    (Primrec.const [])
  refine algorithm.of_eq ?_
  intro points
  by_cases pointsNonempty : points ≠ []
  · by_cases orthogonal :
        PeriodicOrthocrossing.OrthogonalPolyline points
    · simp only [normalizeOrthogonalPolyline,
          dif_pos pointsNonempty, dif_pos orthogonal,
          if_pos pointsNonempty, if_pos orthogonal]
      exact (eraseOrthogonalLoops_eq_listLoopErase
        pointsNonempty orthogonal).symm
    · simp [normalizeOrthogonalPolyline, pointsNonempty, orthogonal]
  · simp [normalizeOrthogonalPolyline, pointsNonempty]

end AxisDirection
end LeanTrominoes
