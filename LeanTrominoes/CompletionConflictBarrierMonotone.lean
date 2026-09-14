import LeanTrominoes.CompletionConflictBarrier

namespace LeanTrominoes.CompletionBarrier

theorem not_disjoint_mono {f small large : Finset Cell} (subset : small ⊆ large)
    (h : ¬ Disjoint f small) : ¬ Disjoint f large := by
  intro disjoint
  apply h
  exact Finset.disjoint_left.mpr fun c hc hs => Finset.disjoint_left.mp disjoint hc (subset hs)

theorem guarded_mono_blocked (t : Tromino) (core region small large available : Finset Cell)
    (subset : small ⊆ large) (checked : GuardedCheck t core region small available) :
    GuardedCheck t core region large available := by
  intro c hc p hp
  rcases checked c hc p hp with inside | blocked | conflict
  · exact Or.inl inside
  · exact Or.inr (Or.inl (not_disjoint_mono subset blocked))
  · obtain ⟨d,hd,absent,conflict⟩ := conflict
    exact Or.inr (Or.inr ⟨d,hd,absent,fun q hq =>
      (conflict q hq).imp (not_disjoint_mono subset) id⟩)

end LeanTrominoes.CompletionBarrier
