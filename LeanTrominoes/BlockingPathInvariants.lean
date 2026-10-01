/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BlockingPathSearch

/-! # Primitive invariants for blocking-path search -/
namespace LeanTrominoes.BlockingPath
variable {V T : Type*} [DecidableEq V] [DecidableEq T]

 theorem closed_mono (buckets : Buckets V T) {s t : State V T} (extension : Extends s t)
    (v : V) (closed : ClosedAt buckets s v) : ClosedAt buckets t v := by
  intro arc member
  have old := closed arc member
  cases next : arc.2 with
  | none => exact extension.2.2 arc.1 (by simpa [next] using old)
  | some w => exact extension.1 w (by simpa [next] using old)

theorem enter_extends (s : State V T) (v : V) : Extends s (enter s v) := by
  refine ⟨?_,?_,fun _ h => h⟩ <;> intro w h <;>
    by_cases eq : w=v <;> simp [enter,eq,h]

theorem enter_valid (s : State V T) (valid : Valid s) (v : V) : Valid (enter s v) := by
  intro w h
  by_cases eq : w=v
  · simp [enter,eq]
  · exact (enter_extends s v).1 w (valid w (by simpa [enter,eq] using h))

theorem enter_trap (buckets : Buckets V T) (s : State V T) (trap : Trap buckets s) (v : V) :
    Trap buckets (enter s v) := by
  intro w blocked unused
  by_cases eq : w=v
  · simp [enter,eq] at unused
  · apply closed_mono buckets (enter_extends s v)
    exact trap w (by simpa [enter,eq] using blocked) (by simpa [enter,eq] using unused)

theorem reserve_extends (s : State V T) (t : T) : Extends s (reserve s t) := by
  refine ⟨fun _ h => h,fun _ h => h,?_⟩
  intro r h
  by_cases eq : r=t <;> simp [reserve,eq,h]

theorem reserve_valid (s : State V T) (valid : Valid s) (t : T) : Valid (reserve s t) := valid

theorem reserve_trap (buckets : Buckets V T) (s : State V T) (trap : Trap buckets s) (t : T) :
    Trap buckets (reserve s t) := by
  intro v blocked unused
  exact closed_mono buckets (reserve_extends s t) v (trap v blocked unused)

theorem retire_valid (s : State V T) (valid : Valid s) (v : V) : Valid (retire s v) := by
  intro w used
  by_cases eq : w=v
  · simp [retire,eq] at used
  · exact valid w (by simpa [retire,eq] using used)

theorem retire_trap (buckets : Buckets V T) (s : State V T) (trap : Trap buckets s) (v : V)
    (closed : ClosedAt buckets s v) : Trap buckets (retire s v) := by
  intro w blocked unused
  by_cases eq : w=v
  · subst w
    exact closed
  · exact trap w blocked (by simpa [retire,eq] using unused)

variable [Fintype V]
def remaining (s : State V T) : Nat := (Finset.univ.filter (fun v => s.blocked v=false)).card

theorem remaining_mono {s t : State V T} (extension : Extends s t) : remaining t ≤ remaining s := by
  apply Finset.card_le_card
  intro v hv
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at *
  cases old : s.blocked v
  · rfl
  · have := extension.1 v old
    simp_all

theorem remaining_enter (s : State V T) (v : V) (fresh : s.blocked v=false) :
    remaining (enter s v)+1=remaining s := by
  have eq : (Finset.univ.filter (fun w => (enter s v).blocked w=false))=
      (Finset.univ.filter (fun w => s.blocked w=false)).erase v := by
    ext w
    by_cases equal : w=v <;> simp [enter,equal]
  have member : v ∈ Finset.univ.filter (fun w => s.blocked w=false) := by simp [fresh]
  rw [remaining,eq,Finset.card_erase_of_mem member]
  have positive := Finset.card_pos.mpr ⟨v,member⟩
  unfold remaining
  omega

end LeanTrominoes.BlockingPath
