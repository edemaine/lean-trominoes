import LeanTrominoes.CompletionConflictBarrier

namespace LeanTrominoes.CompletionBarrier

/-- Exhaustive finite chunks certify the same global boundary condition. -/
theorem guarded_of_chunks (t : Tromino) (core region blocked available : Finset Cell)
    (chunks : List (Finset Cell))
    (covers : ∀ c ∈ core, ∃ chunk ∈ chunks, c ∈ chunk)
    (checked : ∀ chunk ∈ chunks, GuardedCheck t chunk region blocked available) :
    GuardedCheck t core region blocked available := by
  intro c hc p hp
  obtain ⟨chunk,member,inside⟩ := covers c hc
  exact checked chunk member c inside p hp

end LeanTrominoes.CompletionBarrier
