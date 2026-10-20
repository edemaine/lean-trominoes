/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalState
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalOrder

/-! # Counter updates preserve the graph and original-data invariants -/
namespace LeanTrominoes.Domino.WordRAM.Driver
open ComplexityAbstract.RAM
open Binary
local notation "Data" => NaturalData 128

theorem GraphState.set_counter {n d base total : ℕ} {B : BasisData n d} {words : List (ℕ×ℕ)} {data : Data}
    (h : GraphState B base total words data) (index : Fin 128) (counter : index=64 ∨ index=65) (value : ℕ) :
    GraphState B base total words (data.set index value) := by
  obtain ⟨u,v,frame⟩ := h.frame
  have persistent (reg : Fin 128) (member : reg∈Candidate.persistentHeaders) : reg≠index := by
    simp only [Candidate.persistentHeaders,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases counter with rfl | rfl <;> rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have newFrame : Candidate.Frame B u v (data.set index value) := frame.transport
    (by intro reg member; exact Function.update_of_ne (persistent reg member) _ _)
    (by rcases counter with rfl | rfl <;> simp [NaturalData.set,Reserve.frontier])
    (fun _ _ => rfl)
  refine ⟨⟨u,v,newFrame⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals rcases counter with rfl | rfl
  all_goals first | exact h.endpoints | simpa [NaturalData.set] using h.vertices | simpa [NaturalData.set] using h.unit |
    simpa [NaturalData.set] using h.count | simpa [NaturalData.set] using h.left |
    simpa [NaturalData.set] using h.right | simpa [NaturalData.set] using h.parities |
    simpa [NaturalData.set] using h.tables | simpa [NaturalData.set] using h.cursor

end LeanTrominoes.Domino.WordRAM.Driver
