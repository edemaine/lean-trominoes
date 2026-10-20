/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.RAM.NaturalEmbedding

/-! # Register-only argument setup for arithmetic calls -/
namespace LeanTrominoes.Domino.WordRAM.Assignments
open ComplexityAbstract.RAM
variable {r : ℕ}

def code (finish anchor : Fin r) : List (Fin r × Fin r) → Structured.Code r
  | [] => .atom (.copy finish anchor)
  | (dst,src)::rest => .seq (.atom (.copy dst src)) (code finish anchor rest)

def state (finish anchor : Fin r) (moves : List (Fin r × Fin r)) (data : NaturalData r) : NaturalData r :=
  let moved := moves.foldl (fun d p => d.set p.1 (d.1 p.2)) data
  moved.set finish (moved.1 anchor)

/-- Every source register and the anchor are left untouched by earlier
assignments. The final copy writes one callee-local argument register. -/
theorem exec {w : ℕ} (data : NaturalData r) (finish anchor : Fin r) (moves : List (Fin r × Fin r))
    (anchorFits : Fits w (data.1 anchor)) (sourceFits : ∀ p∈moves, Fits w (data.1 p.2))
    (separate : ∀ p∈moves, ∀ q∈moves, p.1≠q.2) (anchorSeparate : ∀ p∈moves, p.1≠anchor) :
    NaturalData.Exec w (code finish anchor moves) data (state finish anchor moves data) (moves.length+1) := by
  induction moves generalizing data with
  | nil => exact NaturalData.copy_exec data finish anchor anchorFits
  | cons p rest ih =>
    have current := NaturalData.copy_exec data p.1 p.2 (sourceFits p List.mem_cons_self)
    have next := ih (data.set p.1 (data.1 p.2))
      (by simpa [NaturalData.set,Function.update_of_ne (anchorSeparate p List.mem_cons_self).symm] using anchorFits)
      (fun q hq => by
        have different := (separate p List.mem_cons_self q (List.mem_cons_of_mem _ hq)).symm
        simpa [NaturalData.set,Function.update_of_ne different] using sourceFits q (List.mem_cons_of_mem _ hq))
      (fun q hq t ht => separate q (List.mem_cons_of_mem _ hq) t (List.mem_cons_of_mem _ ht))
      (fun q hq => anchorSeparate q (List.mem_cons_of_mem _ hq))
    simpa [code,state,Nat.add_comm,Nat.add_assoc,Nat.add_left_comm] using current.seq next

theorem state_memory (finish anchor : Fin r) (moves : List (Fin r × Fin r)) (data : NaturalData r) :
    (state finish anchor moves data).2=data.2 := by
  induction moves generalizing data with
  | nil => rfl
  | cons p rest ih => simpa [state,NaturalData.set] using ih (data.set p.1 (data.1 p.2))

end LeanTrominoes.Domino.WordRAM.Assignments
