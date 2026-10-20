/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMEndpointCandidate

/-! # The leading forced dummy edge in the padded endpoint table -/
namespace LeanTrominoes.Domino.WordRAM.EndpointWriter
open ComplexityAbstract.RAM

def dummyProgram (d : Nat) : Code := .seq (constant R.capacity (2^d)) <|
  .seq (mul R.dummy H.n R.capacity) <| .seq (constant R.one 1) (writePair R.dummy R.dummy)

def dummyPrepared (data : Data) (d : Nat) :=
  ((data.set R.capacity (2^d)).set R.dummy (data.1 H.n*2^d)).set R.one 1

attribute [local simp] H.n H.index H.left H.right R.capacity R.dummy R.one R.storeAddress
  NaturalData.set dummyPrepared constant mul

theorem dummy_exec {B n d : Nat} (data : Data) (bounds : Bounds B d n data) (vertices : data.1 H.n=n) :
    ∃ result, Natural.Exec B (dummyProgram d) data result 8 ∧ Output [(n*2^d,n*2^d)] data result := by
  have first := Natural.Exec.atom (Natural.Step.constant data R.capacity (2^d) bounds.capacity)
  have second : Natural.Exec B (mul R.dummy H.n R.capacity) (data.set R.capacity (2^d))
      ((data.set R.capacity (2^d)).set R.dummy (data.1 H.n*2^d)) 1 := by
    simpa using Natural.Exec.atom (Natural.Step.mul (bound:=B) (data.set R.capacity (2^d)) R.dummy H.n R.capacity
      (by simpa [vertices] using bounds.vertices))
  have third := Natural.Exec.atom (Natural.Step.constant ((data.set R.capacity (2^d)).set R.dummy (data.1 H.n*2^d)) R.one 1 (show 1≤B by have := bounds.small; omega))
  have readyFixed (reg : Fin 128) (low : reg.val<96) : (dummyPrepared data d).1 reg=data.1 reg := by
    have capNe : reg≠R.capacity := by intro same; have := congrArg Fin.val same; simp at this; omega
    have dummyNe : reg≠R.dummy := by intro same; have := congrArg Fin.val same; simp at this; omega
    have oneNe : reg≠R.one := by intro same; have := congrArg Fin.val same; simp at this; omega
    simp only [dummyPrepared,NaturalData.set,Function.update_of_ne capNe,Function.update_of_ne dummyNe,Function.update_of_ne oneNe]
  have last := writePair_exec (B:=B) (dummyPrepared data d) R.dummy R.dummy (by decide) (by decide)
    (by rw [readyFixed H.left (by decide),readyFixed H.index (by decide)]; have := bounds.left; omega)
    (by rw [readyFixed H.right (by decide),readyFixed H.index (by decide)]; have := bounds.right; omega)
    (by simpa [vertices] using bounds.vertices) (by simpa [vertices] using bounds.vertices)
    (by simp only [readyFixed H.index (by decide)]; simp; have room : data.1 (69 : Fin 128)+2≤B := bounds.cursor; omega)
  have full := first.seq (second.seq (third.seq last))
  refine ⟨writeState (dummyPrepared data d) R.dummy R.dummy,full,?_,?_,?_⟩
  · rw [writeState_memory,readyFixed H.left (by decide),readyFixed H.right (by decide),readyFixed H.index (by decide)]
    simp [appendMemory,writeMemory,vertices]
  · rw [writeState_index,readyFixed H.index (by decide)]
    simp
  · intro reg low different
    have scratchNe : reg≠R.storeAddress := by intro same; have := congrArg Fin.val same; simp at this; omega
    exact (writeState_fixed _ R.dummy R.dummy reg ⟨scratchNe,different⟩).trans (readyFixed reg low)

end LeanTrominoes.Domino.WordRAM.EndpointWriter
