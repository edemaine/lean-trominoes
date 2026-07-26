import LeanTrominoes.OrthogonalPolylineJoin

/-!
# One-bend orthogonal polylines

Endpoint fans inside a fixed refinement block should not use the generic
fresh-coordinate detour, which deliberately leaves the coordinate box of
its endpoints.  These two elbow routes instead use at most one bend.  They
remove the bend when the endpoints are already aligned and remove the whole
segment when the endpoints coincide, so every emitted segment remains
nondegenerate.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Join two points by moving horizontally first and then vertically. -/
def horizontalFirstElbow (source target : Cell) : List Cell :=
  if source = target then
    [source]
  else if source.1 = target.1 ∨ source.2 = target.2 then
    [source, target]
  else
    [source, (target.1, source.2), target]

/-- Join two points by moving vertically first and then horizontally. -/
def verticalFirstElbow (source target : Cell) : List Cell :=
  if source = target then
    [source]
  else if source.1 = target.1 ∨ source.2 = target.2 then
    [source, target]
  else
    [source, (source.1, target.2), target]

@[simp]
theorem horizontalFirstElbow_head? (source target : Cell) :
    (horizontalFirstElbow source target).head? = some source := by
  unfold horizontalFirstElbow
  split
  · rfl
  · split <;> rfl

@[simp]
theorem horizontalFirstElbow_getLast? (source target : Cell) :
    (horizontalFirstElbow source target).getLast? = some target := by
  by_cases same : source = target
  · subst target
    simp [horizontalFirstElbow]
  · unfold horizontalFirstElbow
    rw [if_neg same]
    split <;> simp

@[simp]
theorem verticalFirstElbow_head? (source target : Cell) :
    (verticalFirstElbow source target).head? = some source := by
  unfold verticalFirstElbow
  split
  · rfl
  · split <;> rfl

@[simp]
theorem verticalFirstElbow_getLast? (source target : Cell) :
    (verticalFirstElbow source target).getLast? = some target := by
  by_cases same : source = target
  · subst target
    simp [verticalFirstElbow]
  · unfold verticalFirstElbow
    rw [if_neg same]
    split <;> simp

/-- A horizontal-first elbow is always an orthogonal polyline. -/
theorem horizontalFirstElbow_orthogonal (source target : Cell) :
    OrthogonalPolyline (horizontalFirstElbow source target) := by
  rcases source with ⟨sourceX, sourceY⟩
  rcases target with ⟨targetX, targetY⟩
  simp only [horizontalFirstElbow]
  split_ifs with same aligned
  · simp [OrthogonalPolyline]
  · simp only [Prod.mk.injEq] at same
    simp only [OrthogonalPolyline, List.isChain_cons_cons,
      List.isChain_singleton]
    refine ⟨?_, trivial⟩
    rcases aligned with sameX | sameY
    · apply Or.inr
      exact ⟨sameX, by
        intro sameY
        exact same ⟨sameX, sameY⟩⟩
    · apply Or.inl
      exact ⟨sameY, by
        intro sameX
        exact same ⟨sameX, sameY⟩⟩
  · simp only [not_or] at aligned
    simp only [OrthogonalPolyline, List.isChain_cons_cons,
      List.isChain_singleton]
    exact
      ⟨Or.inl ⟨rfl, aligned.1⟩,
        Or.inr ⟨rfl, aligned.2⟩, trivial⟩

/-- A vertical-first elbow is always an orthogonal polyline. -/
theorem verticalFirstElbow_orthogonal (source target : Cell) :
    OrthogonalPolyline (verticalFirstElbow source target) := by
  rcases source with ⟨sourceX, sourceY⟩
  rcases target with ⟨targetX, targetY⟩
  simp only [verticalFirstElbow]
  split_ifs with same aligned
  · simp [OrthogonalPolyline]
  · simp only [Prod.mk.injEq] at same
    simp only [OrthogonalPolyline, List.isChain_cons_cons,
      List.isChain_singleton]
    refine ⟨?_, trivial⟩
    rcases aligned with sameX | sameY
    · apply Or.inr
      exact ⟨sameX, by
        intro sameY
        exact same ⟨sameX, sameY⟩⟩
    · apply Or.inl
      exact ⟨sameY, by
        intro sameX
        exact same ⟨sameX, sameY⟩⟩
  · simp only [not_or] at aligned
    simp only [OrthogonalPolyline, List.isChain_cons_cons,
      List.isChain_singleton]
    exact
      ⟨Or.inr ⟨rfl, aligned.2⟩,
        Or.inl ⟨rfl, aligned.1⟩, trivial⟩

/-- Every horizontal-first point is an endpoint or the one possible bend. -/
theorem mem_horizontalFirstElbow
    {source target point : Cell}
    (member : point ∈ horizontalFirstElbow source target) :
    point = source ∨ point = target ∨
      point = (target.1, source.2) := by
  unfold horizontalFirstElbow at member
  split at member
  · simp at member
    exact Or.inl member
  · split at member
    · simp at member
      rcases member with sourceEq | targetEq
      · exact Or.inl sourceEq
      · exact Or.inr (Or.inl targetEq)
    · simp at member
      rcases member with sourceEq | bendEq | targetEq
      · exact Or.inl sourceEq
      · exact Or.inr (Or.inr bendEq)
      · exact Or.inr (Or.inl targetEq)

/-- Every vertical-first point is an endpoint or the one possible bend. -/
theorem mem_verticalFirstElbow
    {source target point : Cell}
    (member : point ∈ verticalFirstElbow source target) :
    point = source ∨ point = target ∨
      point = (source.1, target.2) := by
  unfold verticalFirstElbow at member
  split at member
  · simp at member
    exact Or.inl member
  · split at member
    · simp at member
      rcases member with sourceEq | targetEq
      · exact Or.inl sourceEq
      · exact Or.inr (Or.inl targetEq)
    · simp at member
      rcases member with sourceEq | bendEq | targetEq
      · exact Or.inl sourceEq
      · exact Or.inr (Or.inr bendEq)
      · exact Or.inr (Or.inl targetEq)

end PeriodicOrthocrossing
end LeanTrominoes
