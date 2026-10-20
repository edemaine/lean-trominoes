/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMEndpointBoth

/-! # Complete active/dummy selection and both endpoint writes -/
namespace LeanTrominoes.Domino.WordRAM.EndpointWriter
open ComplexityAbstract.RAM

def selectedSource (data : Data) : Nat := if data.1 H.active=0 then data.1 R.dummy else data.1 R.source
def selectedTarget (data : Data) : Nat := if data.1 H.active=0 then data.1 R.dummy else data.1 R.target
def selectedWords (data : Data) : List (Nat × Nat) :=
  [(selectedSource data,selectedTarget data),(selectedTarget data,selectedSource data)]

structure FooterResult (before after : Data) : Prop where
  memory : after.2=appendMemory before.2 (before.1 H.left) (before.1 H.right) (before.1 H.index) (selectedWords before)
  index : after.1 H.index=before.1 H.index+2
  fixed : ∀ reg : Fin 128, reg.val<96 → reg≠H.index → after.1 reg=before.1 reg

theorem footer_exec {B : Nat} (data : Data) (one : data.1 R.one=1)
    (source : data.1 R.source≤B) (target : data.1 R.target≤B) (dummy : data.1 R.dummy≤B)
    (scratch : data.1 R.constant≤B)
    (left : data.1 H.left+data.1 H.index+1≤B) (right : data.1 H.right+data.1 H.index+1≤B)
    (cursor : data.1 H.index+2≤B) :
    ∃ result, Natural.Exec B footer data result 14 ∧ FooterResult data result := by
  let ready := data.set R.phase 0
  have first : Natural.Exec B (constant R.phase 0) data ready 1 := Natural.Exec.atom (Natural.Step.constant _ _ _ (Nat.zero_le B))
  have readyFixed (reg : Fin 128) (different : reg≠R.phase) : ready.1 reg=data.1 reg := by
    simp only [ready,NaturalData.set,Function.update_of_ne different]
  obtain ⟨chosen,choice,correct⟩ := choose_exec (B:=B) ready (by simp [ready,NaturalData.set])
    (by rw [readyFixed R.dummy (by decide)]; exact dummy) (by rw [readyFixed R.constant (by decide)]; exact scratch)
  have chosenFixed (reg : Fin 128) (lower : reg.val<96) : chosen.1 reg=data.1 reg := by
    apply (correct.fixed reg (Or.inl (by omega))).trans
    apply readyFixed
    intro same; have := congrArg Fin.val same; simp only [R.phase] at this; omega
  have chosenOne : chosen.1 R.one=1 := (correct.fixed R.one (by decide)).trans ((readyFixed R.one (by decide)).trans one)
  have chosenSource : chosen.1 R.source=selectedSource data := by
    simpa only [ready,NaturalData.set,H.active,R.source,R.dummy,R.phase,selectedSource,Function.update_of_ne (by decide : (68 : Fin 128)≠105),
      Function.update_of_ne (by decide : (106 : Fin 128)≠105),Function.update_of_ne (by decide : (109 : Fin 128)≠105)] using correct.source
  have chosenTarget : chosen.1 R.target=selectedTarget data := by
    simpa only [ready,NaturalData.set,H.active,R.target,R.dummy,R.phase,selectedTarget,Function.update_of_ne (by decide : (68 : Fin 128)≠105),
      Function.update_of_ne (by decide : (107 : Fin 128)≠105),Function.update_of_ne (by decide : (109 : Fin 128)≠105)] using correct.target
  have chosenMemory : chosen.2=data.2 := correct.memory
  obtain ⟨result,writes,stored⟩ := both_exec (B:=B) chosen chosenOne
    (by rw [chosenSource]; unfold selectedSource; split <;> assumption)
    (by rw [chosenTarget]; unfold selectedTarget; split <;> assumption)
    (by rw [chosenFixed H.left (by decide),chosenFixed H.index (by decide)]; exact left)
    (by rw [chosenFixed H.right (by decide),chosenFixed H.index (by decide)]; exact right)
    (by rw [chosenFixed H.index (by decide)]; exact cursor)
  refine ⟨result,first.seq (choice.seq writes),?_,?_,?_⟩
  · simpa only [chosenMemory,chosenSource,chosenTarget,chosenFixed H.left (by decide),chosenFixed H.right (by decide),
      chosenFixed H.index (by decide),selectedWords] using stored.memory
  · rw [stored.index,chosenFixed H.index (by decide)]
  · intro reg lower different
    have scratchNe : reg≠R.storeAddress := by intro same; have := congrArg Fin.val same; simp only [R.storeAddress] at this; omega
    exact (stored.fixed reg scratchNe different).trans (chosenFixed reg lower)

end LeanTrominoes.Domino.WordRAM.EndpointWriter
