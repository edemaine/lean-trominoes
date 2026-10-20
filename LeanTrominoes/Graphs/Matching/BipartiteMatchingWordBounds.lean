/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingBreadthExpand
import LeanTrominoes.Computation.RAM.WordBounds

/-! # Value bounds for the matching solver's breadth-first labels

Label values are bounded by the search fuel, independently of input offsets.
Partner and vertex arrays already have finite index types. Ghost cost counters
are excluded: they are proof instrumentation, not algorithm registers.
-/
namespace LeanTrominoes.BipartiteMatching.BreadthSearch
variable {L R : Type*} [DecidableEq L] [DecidableEq R]

def LabelsBound (bound : ℕ) (distance : L → Option ℕ) : Prop :=
  ∀ l j, distance l=some j → j≤bound

theorem expand_labels_bound (buckets : L → List R) (matching : State L R) (depth : ℕ)
    (frontier : List L) (s : Wave L) (h : LabelsBound depth s.distance) :
    LabelsBound (depth+1) (expand buckets matching depth frontier s).distance := by
  intro l j marked
  rcases (expand_distance buckets matching depth frontier s l j).mp marked with old | fresh
  · exact (h l j old).trans (Nat.le_succ _)
  · omega

def Outcome.Bounded (bound : ℕ) : Outcome L → Prop
  | .layers distance depth _ => depth≤bound ∧ LabelsBound bound distance
  | .deficient distance depth _ => depth≤bound ∧ LabelsBound bound distance
  | .exhausted _ => True

theorem run_labels_bound (buckets : L → List R) (matching : State L R) (freeCount fuel depth : ℕ)
    (frontier : List L) (distance : L → Option ℕ) (h : LabelsBound depth distance) :
    Outcome.Bounded (depth+fuel) (run buckets matching freeCount fuel depth frontier distance) := by
  induction fuel generalizing depth frontier distance with
  | zero => trivial
  | succ fuel ih =>
    have waveBound := expand_labels_bound buckets matching depth frontier
      (⟨distance,[],false,0⟩ : Wave L) h
    simp only [run]
    split
    · exact ⟨by omega,fun l j marked => (waveBound l j marked).trans (by omega)⟩
    · split
      · exact ⟨by omega,fun l j marked => (waveBound l j marked).trans (by omega)⟩
      · have later := ih (depth+1) (expand buckets matching depth frontier ⟨distance,[],false,0⟩).next _ waveBound
        cases result : run buckets matching freeCount fuel (depth+1)
            (expand buckets matching depth frontier ⟨distance,[],false,0⟩).next
            (expand buckets matching depth frontier ⟨distance,[],false,0⟩).distance <;>
          first | trivial | simpa only [result,Outcome.Bounded,Nat.add_right_comm,Nat.add_assoc] using later

/-- All returned search depths and stored distance labels are at most the
number of indexed left vertices. This bound needs no matching correctness assumptions. -/
theorem search_labels_bound (vertices : List L) (buckets : L → List R) (matching : State L R) :
    Outcome.Bounded vertices.length (search vertices buckets matching) := by
  have initial : LabelsBound 0 (initialDistance matching) := by
    intro l j marked
    unfold initialDistance at marked
    split at marked <;> simp_all
  simpa only [search,Nat.zero_add] using run_labels_bound buckets matching (freeVertices vertices matching).length vertices.length 0
    (freeVertices vertices matching) (initialDistance matching) initial

/-- Returned labels fit every word size above the binary length of the vertex count. -/
theorem search_labels_fit (vertices : List L) (buckets : L → List R) (matching : State L R)
    (w : ℕ) (width : WordBounds.bits vertices.length≤w) (distance : L → Option ℕ) (depth cost : ℕ)
    (result : search vertices buckets matching = .layers distance depth cost ∨
      search vertices buckets matching = .deficient distance depth cost) :
    ComplexityAbstract.RAM.Fits w (depth : ℤ) ∧
      ∀ l j, distance l=some j → ComplexityAbstract.RAM.Fits w (j : ℤ) := by
  have bounded := search_labels_bound vertices buckets matching
  have labels : depth≤vertices.length ∧ LabelsBound vertices.length distance := by
    rcases result with result | result <;> simpa only [result,Outcome.Bounded] using bounded
  constructor
  · apply WordBounds.fits_mono width (WordBounds.fits_of_natAbs_le _ _ ?_)
    simpa using labels.1
  · intro l j marked
    apply WordBounds.fits_mono width (WordBounds.fits_of_natAbs_le _ _ ?_)
    simpa using labels.2 l j marked

end LeanTrominoes.BipartiteMatching.BreadthSearch
