/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMEndpointChoice

/-! # Two actual endpoint pairs and their exact memory update -/
namespace LeanTrominoes.Domino.WordRAM.EndpointWriter
open ComplexityAbstract.RAM

def appendMemory (memory : Nat → Nat) (left right index : Nat) : List (Nat × Nat) → (Nat → Nat)
  | [] => memory
  | pair::rest => appendMemory (writeMemory memory left right index pair.1 pair.2) left right (index+1) rest

structure BothResult (before after : Data) : Prop where
  memory : after.2=appendMemory before.2 (before.1 H.left) (before.1 H.right) (before.1 H.index)
    [(before.1 R.source,before.1 R.target),(before.1 R.target,before.1 R.source)]
  index : after.1 H.index=before.1 H.index+2
  fixed : ∀ reg : Fin 128, reg≠R.storeAddress → reg≠H.index → after.1 reg=before.1 reg

theorem both_exec {B : Nat} (data : Data) (one : data.1 R.one=1)
    (source : data.1 R.source≤B) (target : data.1 R.target≤B)
    (left : data.1 H.left+data.1 H.index+1≤B) (right : data.1 H.right+data.1 H.index+1≤B)
    (cursor : data.1 H.index+2≤B) :
    ∃ result, Natural.Exec B (.seq (writePair R.source R.target) (writePair R.target R.source)) data result 10 ∧ BothResult data result := by
  have first := writePair_exec data R.source R.target (by decide) (by decide) (by omega) (by omega) source target (by rw [one]; omega)
  let middle := writeState data R.source R.target
  have middleOne : middle.1 R.one=1 := (writeState_fixed data R.source R.target R.one (by decide)).trans one
  have middleIndex : middle.1 H.index=data.1 H.index+1 := by rw [writeState_index,one]
  have middleSource : middle.1 R.source=data.1 R.source := writeState_fixed data R.source R.target R.source (by decide)
  have middleTarget : middle.1 R.target=data.1 R.target := writeState_fixed data R.source R.target R.target (by decide)
  have middleLeft : middle.1 H.left=data.1 H.left := writeState_fixed data R.source R.target H.left (by decide)
  have middleRight : middle.1 H.right=data.1 H.right := writeState_fixed data R.source R.target H.right (by decide)
  have second := writePair_exec middle R.target R.source (by decide) (by decide)
    (by rw [middleLeft,middleIndex]; omega) (by rw [middleRight,middleIndex]; omega)
    (middleTarget ▸ target) (middleSource ▸ source) (by rw [middleIndex,middleOne]; omega)
  refine ⟨writeState middle R.target R.source,first.seq second,?_,?_,?_⟩
  · rw [writeState_memory,middleLeft,middleRight,middleIndex,middleTarget,middleSource]
    change writeMemory (writeMemory data.2 (data.1 H.left) (data.1 H.right) (data.1 H.index) (data.1 R.source) (data.1 R.target))
      (data.1 H.left) (data.1 H.right) (data.1 H.index+1) (data.1 R.target) (data.1 R.source)=_
    rfl
  · rw [writeState_index,middleIndex,middleOne]
  · intro reg scratch index
    exact (writeState_fixed middle R.target R.source reg ⟨scratch,index⟩).trans (writeState_fixed data R.source R.target reg ⟨scratch,index⟩)

end LeanTrominoes.Domino.WordRAM.EndpointWriter
