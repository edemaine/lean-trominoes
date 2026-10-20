/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMEndpointWriter
import LeanTrominoes.Computation.RAM.NaturalEmbedding

/-! # The padded candidate writer as a bounded-word subroutine -/
namespace LeanTrominoes.Domino.WordRAM.EndpointWriter
open ComplexityAbstract.RAM

/-- The arithmetic probe's register file survives the endpoint writer exactly. -/
theorem Output.probe_registers {words : List (Nat × Nat)} {before after : Data}
    (h : Output words before after) :
    (NaturalData.lower (r:=64) (s:=64) after).1=(NaturalData.lower (r:=64) (s:=64) before).1 := by
  funext reg
  apply h.fixed (reg.castAdd 64) (by have := reg.isLt; simpa only [Fin.val_castAdd] using (show reg.val<96 by omega))
  intro same
  have equal := congrArg Fin.val same
  have := reg.isLt
  change reg.val=69 at equal
  omega

theorem appendMemory_frame (memory : Nat → Nat) (left right index : Nat) (words : List (Nat × Nat))
    (address : Nat)
    (leftOutside : address<left+index ∨ left+index+words.length≤address)
    (rightOutside : address<right+index ∨ right+index+words.length≤address) :
    appendMemory memory left right index words address=memory address := by
  induction words generalizing memory index with
  | nil => rfl
  | cons pair rest ih =>
    have leftNe : address≠left+index := by simp only [List.length_cons] at leftOutside; omega
    have rightNe : address≠right+index := by simp only [List.length_cons] at rightOutside; omega
    rw [appendMemory,ih]
    · simp only [writeMemory,Function.update_of_ne leftNe,Function.update_of_ne rightNe]
    · simp only [List.length_cons] at leftOutside
      omega
    · simp only [List.length_cons] at rightOutside
      omega

theorem Output.frame {words : List (Nat × Nat)} {before after : Data} (h : Output words before after)
    (address : Nat)
    (leftOutside : address<before.1 H.left+before.1 H.index ∨ before.1 H.left+before.1 H.index+words.length≤address)
    (rightOutside : address<before.1 H.right+before.1 H.index ∨ before.1 H.right+before.1 H.index+words.length≤address) :
    after.2 address=before.2 address := by
  rw [h.memory]
  exact appendMemory_frame _ _ _ _ _ _ leftOutside rightOutside

/-- From the computed flags and parity digits to the original graph's exact
candidate records, using actual bounded-word instructions throughout. -/
theorem candidate_exec {bound w n d : Nat} (B : BasisData n d) (u : Fin n) (direction : Fin d) (v : Fin n)
    (phase : PeriodicLatticeGraph.DoubleCover.Phase d) (bits : Fin d → Nat) (data : Data)
    (width : Fits w bound) (bounds : Bounds bound d n data)
    (uInput : data.1 H.u=u.val) (vInput : data.1 H.v=v.val) (nInput : data.1 H.n=n)
    (bitBound : ∀ i, bits i≤1) (known : ∀ i, data.2 (data.1 H.parities+i.val)=bits i)
    (valid : data.1 H.active≠0 ↔ PaddedGraph.Active B u direction v)
    (parities : PaddedGraph.Active B u direction v → ∀ i,
      bits i=(PaddedGraph.coordinates B u direction v i%2).toNat) :
    ∃ result, NaturalData.Exec w (program phase) data result (9*d+25) ∧
      Output (candidateWords B (u,direction,v,phase)) data result := by
  obtain ⟨result,run,correct⟩ := program_exec phase bits data u v bounds uInput vInput nInput bitBound known
  refine ⟨result,run.compiles width,?_⟩
  rw [←emittedWords_candidate B u direction v phase bits (data.1 H.active) valid parities]
  exact correct

end LeanTrominoes.Domino.WordRAM.EndpointWriter
