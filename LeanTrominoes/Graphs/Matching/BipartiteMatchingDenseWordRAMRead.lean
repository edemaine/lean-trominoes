/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMExecutionFrame

/-! # Array reads preserve the graph and matching representation -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM

theorem read_preserves_layout (base index dst : Fin 64) (large : 16≤dst.val) : PreservesLayout (read base index dst) := by
  have notDst (i : Fin 64) (small : i.val<16) : i≠dst := by intro same; have := congrArg Fin.val same; omega
  have notScratch (i : Fin 64) (small : i.val<16) : i≠Reg.scratch := by
    intro same; have h := congrArg Fin.val same; simp [Reg.scratch] at h; omega
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro slot
    have small : (pointer slot).val<16 := by dsimp [pointer]; have := slot.isLt; omega
    exact ⟨notScratch _ small,notDst _ small⟩
  · exact ⟨notScratch _ (by decide),notDst _ (by decide)⟩
  · exact ⟨notScratch _ (by decide),notDst _ (by decide)⟩
  · exact ⟨notScratch _ (by decide),notDst _ (by decide)⟩
  · exact ⟨notScratch _ (by decide),notDst _ (by decide)⟩
  · exact ⟨notScratch _ (by decide),notDst _ (by decide)⟩

theorem read_slot {B : Nat} (input : Input)
    (matching : State (Fin input.1) (Fin input.2.1)) (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d) (bounded : NaturalData.Bounded B d) (room : (Layout.ofInput input).frontier≤B)
    (slot : Slot) (i : Nat) (within : i<(Layout.ofInput input).length slot)
    (index dst : Fin 64) (idx : d.1 index=i) (large : 16≤dst.val) :
    Natural.Exec B (read (pointer slot) index dst) d (readState d (pointer slot) index dst) 2 ∧
      Representation input matching paths (readState d (pointer slot) index dst) ∧
      NaturalData.Bounded B (readState d (pointer slot) index dst) := by
  have execution := native_read d (pointer slot) index dst
    (by rw [rep.pointers slot,idx]; exact ((Layout.ofInput input).address_bound slot i within).le.trans room)
    (bounded.2 _)
  exact ⟨execution,rep.of_execution input matching matching paths paths d _ execution (read_preserves_layout _ _ _ large) rep.memory,
    execution.bounded bounded⟩

theorem read_slot_value (input : Input)
    (matching : State (Fin input.1) (Fin input.2.1)) (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d) (slot : Slot) (i : Nat) (index dst : Fin 64) (idx : d.1 index=i) :
    (readState d (pointer slot) index dst).1 dst=d.2 ((Layout.ofInput input).base slot+i) := by
  simp [readState,NaturalData.set,rep.pointers slot,idx]

theorem native_skip {B : Nat} (d : Data) (bounded : NaturalData.Bounded B d) : Natural.Exec B skip d d 1 := by
  have trace := Natural.Exec.atom (Natural.Step.copy d Reg.zero Reg.zero (bounded.1 Reg.zero))
  simpa [skip,copy,NaturalData.set] using trace

end LeanTrominoes.BipartiteMatching.DenseWordRAM
