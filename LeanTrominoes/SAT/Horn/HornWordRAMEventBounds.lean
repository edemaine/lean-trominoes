/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMEventArrays

/-! # Persistent word bounds for Horn premise processing -/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

attribute [local simp] Reg.zero Reg.one Reg.heads Reg.counters Reg.stack Reg.rule Reg.value
  Reg.top Reg.event Reg.scratch Reg.headValue
  Slot.heads Slot.edgeRules Slot.buckets Slot.counters Slot.links Slot.stack

theorem readState_bounded_same {B : ℕ} {data : Data} (before : NaturalData.Bounded B data)
    (dst ptr index : Fin 32) (address : data.1 ptr+data.1 index≤B) :
    NaturalData.Bounded B (readState data dst ptr index) :=
  (before.set Reg.scratch address).set dst (before.2 _)

theorem writeState_bounded_same {B : ℕ} {data : Data} (before : NaturalData.Bounded B data)
    (src ptr index : Fin 32) (address : data.1 ptr+data.1 index≤B) :
    NaturalData.Bounded B (writeState data src ptr index) :=
  (before.set Reg.scratch address).store (before.1 src)

/-- Address calculations use allocated-array bounds, so repeated pushes need
no repeated multiplication of the register bound. -/
theorem Layout.pushState_bounded {B : ℕ} (layout : Layout) (data : Data)
    (before : NaturalData.Bounded B data) (pointers : layout.Pointers data)
    (unit : data.1 Reg.one=1) (within : data.1 Reg.rule<layout.rules)
    (room : data.1 Reg.top<layout.rules) (frontier : layout.frontier≤B) :
    NaturalData.Bounded B (pushState data) := by
  have ps : data.1 Reg.stack=layout.base Slot.stack := pointers Slot.stack
  have address : data.1 Reg.stack+data.1 Reg.top≤B := by
    rw [ps]
    exact (layout.address_bound Slot.stack _ room).le.trans frontier
  have rules : layout.rules≤B := by
    have high : layout.rules≤layout.frontier := by dsimp [Layout.frontier,Layout.base]; omega
    omega
  constructor
  · rw [pushState_registers]
    apply update_bound
    · apply update_bound
      · exact update_bound before.1 Reg.headValue (before.2 _)
      · exact address
    · rw [unit]
      omega
  · rw [pushState_memory]
    exact update_bound before.2 _ (before.2 _)

theorem Layout.storedCounter_bounded {B : ℕ} (layout : Layout) (data : Data)
    (before : NaturalData.Bounded B data) (pointers : layout.Pointers data)
    (within : data.1 Reg.rule<layout.rules) (frontier : layout.frontier≤B) :
    NaturalData.Bounded B (storedCounter data) := by
  have lower : NaturalData.Bounded B (loweredCounter data) :=
    before.set Reg.value ((Nat.sub_le _ _).trans (before.1 _))
  apply writeState_bounded_same lower
  have pc : data.1 Reg.counters=layout.base Slot.counters := pointers Slot.counters
  simpa [loweredCounter,NaturalData.set,pc] using
    (layout.address_bound Slot.counters _ within).le.trans frontier

theorem Layout.eventAction_bounded {B : ℕ} (layout : Layout) (data : Data)
    (before : NaturalData.Bounded B data) (pointers : layout.Pointers data)
    (unit : data.1 Reg.one=1) (within : data.1 Reg.rule<layout.rules)
    (room : data.1 Reg.top<layout.rules) (frontier : layout.frontier≤B) :
    NaturalData.Bounded B (eventActionState data) := by
  have stored := layout.storedCounter_bounded data before pointers within frontier
  unfold eventActionState
  split
  · exact before
  · split
    · apply layout.pushState_bounded (storedCounter data) stored
        (storedCounter_pointers layout data pointers)
      · simpa [storedCounter,loweredCounter,writeState,NaturalData.set,NaturalData.store] using unit
      · simpa [storedCounter,loweredCounter,writeState,NaturalData.set,NaturalData.store] using within
      · simpa [storedCounter,loweredCounter,writeState,NaturalData.set,NaturalData.store] using room
      · exact frontier
    · exact stored

/-- The sum counts the loop branch and back jump for each visited node. -/
def eventLoopCost (data : Data) : ℕ → ℕ
  | 0 => 2
  | n+1 => eventBodyCost data+eventLoopCost (eventState data) n+2

theorem eventLoopCost_le (data : Data) (n : ℕ) : eventLoopCost data n≤20*n+2 := by
  induction n generalizing data with
  | zero => simp [eventLoopCost]
  | succ n ih =>
    have rest := ih (eventState data)
    have step := eventBodyCost_le data
    simp only [eventLoopCost]
    omega

/-- A certified chain traversal compiles to the actual linked-list loop.
The hypotheses are facts about its reached states, including termination and
bounded words; no semantic function is assigned a unit operation cost. -/
theorem processEvents_exec {w B n : ℕ} (data : Data)
    (control : ∀ k, k<n →
      ((eventState^[k]) data).1 Reg.one=1 ∧ ((eventState^[k]) data).1 Reg.zero=0 ∧
      0<((eventState^[k]) data).1 Reg.event)
    (terminal : ((eventState^[n]) data).1 Reg.event=0 ∧ ((eventState^[n]) data).1 Reg.zero=0)
    (bounded : ∀ k, k<n → NaturalData.Bounded B ((eventState^[k]) data))
    (width : Fits w (128*B : ℕ)) :
    NaturalData.Exec w processEvents data ((eventState^[n]) data) (eventLoopCost data n) := by
  induction n generalizing data with
  | zero =>
    apply Structured.Exec.loop_done
    simp only [Structured.Condition.Holds,NaturalData.word]
    simp only [Function.iterate_zero,id_eq] at terminal
    rw [terminal.1,terminal.2]
    omega
  | succ n ih =>
    have now := control 0 (by omega)
    simp only [Function.iterate_zero,id_eq] at now
    have body := (eventBody_exec (bounded 0 (by omega)) now.1 now.2.1 now.2.2 width).1
    have rest := ih (eventState data)
      (fun k hk => by simpa only [Function.iterate_succ_apply] using control (k+1) (by omega))
      (by simpa only [Function.iterate_succ_apply] using terminal)
      (fun k hk => by simpa only [Function.iterate_succ_apply] using bounded (k+1) (by omega))
    have run := Structured.Exec.loop_more
      (show Structured.Condition.Holds (.lt Reg.zero Reg.event) data.word by
        simp only [Structured.Condition.Holds,NaturalData.word]
        rw [now.2.1]
        exact_mod_cast now.2.2) body rest
    simpa only [processEvents,eventLoopCost,Function.iterate_succ_apply,Function.iterate_zero,id_eq] using run

end LeanTrominoes.Horn.WordRAM
