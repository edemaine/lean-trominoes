/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMRepresentation

/-! # The Horn decision at a represented terminal worklist state -/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

attribute [local simp] Reg.zero Reg.one Reg.seen Reg.value Reg.output Reg.scratch

/-- An invariant terminal worklist accepts exactly the satisfiable inputs,
including Horn clauses whose head is the contradiction atom. -/
theorem terminal_satisfiable (input : Input) (state : HornState input)
    (invariant : Worklist.Invariant (Indexed.edges input.2).reverse (Indexed.head input.2) state)
    (empty : state.queue=[]) :
    state.seen none=false ↔ Satisfiable input.2.rules.toList := by
  have closed : Worklist.Closed (Indexed.edges input.2).reverse (Indexed.head input.2)
      (fun a => state.seen a=true) := by
    intro r premises
    have missing := (Worklist.missing_zero (Indexed.edges input.2).reverse state.seen r).mpr premises
    have ready := invariant.ready r ((invariant.counters r).trans missing)
    simpa only [Worklist.Covered,empty,List.not_mem_nil,or_false] using ready
  constructor
  · intro bottom
    let model : Fin input.1 → Prop := fun a => state.seen (some a)=true
    refine ⟨model,(Indexed.closed_extension input.2 model).mp ?_⟩
    have extension : Indexed.extension model=(fun a => state.seen a=true) := by
      funext a
      cases a <;> simp [Indexed.extension,model,bottom]
    rw [extension]
    exact (Worklist.closed_reverse _ _ _).mp closed
  · rintro ⟨model,satisfies⟩
    have modelClosed := (Worklist.closed_reverse _ _ _).mpr
      ((Indexed.closed_extension input.2 model).mpr satisfies)
    have absent : state.seen none≠true := by
      intro known
      exact invariant.sound (Indexed.extension model) modelClosed none (Or.inl known)
    cases known : state.seen none <;> simp_all

theorem represented_terminal_satisfiable (input : Input) (state : HornState input)
    (data : Data) (contents : Tables) (representation : MachineRep input state data contents)
    (invariant : Worklist.Invariant (Indexed.edges input.2).reverse (Indexed.head input.2) state)
    (empty : state.queue=[]) :
    contents Slot.seen 0=0 ↔ Satisfiable input.2.rules.toList := by
  have seen := representation.seen none
  have criterion := terminal_satisfiable input state invariant empty
  simp only [atomCode] at seen
  rw [seen]
  cases bottom : state.seen none <;> simpa [bottom] using criterion

def answerRead (data : Data) := readState data Reg.value Reg.seen Reg.zero

def answerState (data : Data) :=
  (answerRead data).set Reg.output
    (if (answerRead data).1 Reg.value=(answerRead data).1 Reg.zero then 1 else 0)

def answerCost (data : Data) : ℕ :=
  if (answerRead data).1 Reg.value=(answerRead data).1 Reg.zero then 4 else 5

/-- The final array read, branch, and output write are ordinary instructions. -/
theorem answer_exec {w B : ℕ} {data : Data} (before : NaturalData.Bounded B data)
    (unit : data.1 Reg.one=1) (width : Fits w (2*B : ℕ)) :
    NaturalData.Exec w answer data (answerState data) (answerCost data) := by
  have fits0 : Fits w (0 : ℕ) := Allocation.nat_fits_le width (Nat.zero_le _)
  have fits1 : Fits w (1 : ℕ) := Allocation.nat_fits_le width (by
    have value := before.1 Reg.one
    rw [unit] at value
    omega)
  have first := readState_exec data Reg.value Reg.seen Reg.zero (read_fits_of_bound before width (by omega) _ _)
  by_cases yes : (answerRead data).1 Reg.value=(answerRead data).1 Reg.zero
  · have second := NaturalData.constant_exec (answerRead data) Reg.output 1 fits1
    have branch := Structured.Exec.branch_yes (no := constant Reg.output 0)
      (show Structured.Condition.Holds (.eq Reg.value Reg.zero) (answerRead data).word by
        simpa [Structured.Condition.Holds,NaturalData.word] using yes) second
    simp only [answerState,answerCost,yes,ite_true]
    simpa only [answer,answerRead,constant,Nat.reduceAdd] using first.seq branch
  · have second := NaturalData.constant_exec (answerRead data) Reg.output 0 fits0
    have branch := Structured.Exec.branch_no (yes := constant Reg.output 1)
      (show ¬Structured.Condition.Holds (.eq Reg.value Reg.zero) (answerRead data).word by
        simpa [Structured.Condition.Holds,NaturalData.word] using yes) second
    simp only [answerState,answerCost,yes,ite_false]
    simpa only [answer,answerRead,constant,Nat.reduceAdd] using first.seq branch

theorem answerCost_le (data : Data) : answerCost data≤5 := by
  unfold answerCost
  split <;> omega

theorem answerState_output (input : Input) (state : HornState input) (data : Data) (contents : Tables)
    (representation : MachineRep input state data contents)
    (invariant : Worklist.Invariant (Indexed.edges input.2).reverse (Indexed.head input.2) state)
    (empty : state.queue=[]) :
    (answerState data).1 Reg.output=1 ↔ Satisfiable input.2.rules.toList := by
  have pointers : data.1 Reg.seen=(Layout.ofInput input).base Slot.seen := representation.pointers Slot.seen
  have read : data.2 (data.1 Reg.seen+data.1 Reg.zero)=contents Slot.seen 0 := by
    rw [pointers,representation.zero]
    have within : 0<(Layout.ofInput input).length Slot.seen := by
      change 0< input.1+1
      omega
    exact representation.realizes Slot.seen 0 within
  have zero : (answerRead data).1 Reg.zero=0 := by
    simpa [answerRead,readState,NaturalData.set] using representation.zero
  have value : (answerRead data).1 Reg.value=contents Slot.seen 0 := by
    simpa [answerRead,readState,NaturalData.set] using read
  simp only [answerState,NaturalData.set,Function.update_self,value,zero]
  rw [← represented_terminal_satisfiable input state data contents representation invariant empty]
  split <;> simp_all

end LeanTrominoes.Horn.WordRAM
