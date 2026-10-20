/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMPrepare
import LeanTrominoes.Computation.RAM.WordBounds

/-! # The original endpoint encoding at the RAM input boundary -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM

set_option linter.unusedSimpArgs false

def initialData (input : Input) : Data :=
  (fun _ => 0,fun address => if address=0 then (words input).length else ((words input)[address-1]?).getD 0)

theorem words_length (input : Input) : (words input).length=3+2*input.2.2.length := by
  simp [words]
  omega

theorem initialData_word (input : Input) : (initialData input).word=State.data (initial (r := 64) (encode input)) := by
  apply Prod.ext
  · rfl
  · funext address
    simp only [initialData,NaturalData.word,encode,initial,State.data]
    split_ifs <;> simp_all [List.getElem?_map]
    cases (words input)[address-1]? <;> rfl

theorem word_bound (input : Input) (x : Nat) (member : x∈words input) : x≤3*size input := by
  simp only [words,List.mem_append,List.mem_cons,List.mem_singleton,List.mem_map,List.not_mem_nil,or_false] at member
  rcases member with (header | left) | right
  · rcases header with equal | equal | equal
    all_goals subst x; dsimp [size]; omega
  · obtain ⟨edge,inside,equal⟩ := left
    subst x; have := edge.1.isLt; dsimp [size]; omega
  · obtain ⟨edge,inside,equal⟩ := right
    subst x; have := edge.2.isLt; dsimp [size]; omega

theorem initialData_bounded (input : Input) : NaturalData.Bounded (3*size input) (initialData input) := by
  constructor
  · intro i; simp [initialData]
  · intro address
    simp only [initialData]
    split_ifs with zero
    · rw [words_length]; dsimp [size]; omega
    · cases found : (words input)[address-1]? with
      | none => simp
      | some value =>
        simp only [Option.getD_some]
        exact word_bound input value (List.mem_of_getElem? found)

def preparedInput (input : Input) : Data :=
  prepared5 (initialData input) (words input).length input.1 input.2.1 input.2.2.length

theorem prepareEnd_frontier (input : Input) :
    prepareEnd (words input).length input.1 input.2.1=(Layout.ofInput input).frontier := by
  simp [prepareEnd,words_length,Layout.ofInput,Layout.frontier]
  omega

theorem prepare_on_input {w : Nat} (input : Input)
    (width : Fits w (Layout.ofInput input).frontier) :
    NaturalData.Exec w prepare (initialData input) (preparedInput input)
      (4*(2*input.1+input.2.1+2*(input.1*input.1))+58) := by
  apply prepare_exec
  · simp [initialData]
  · simp [initialData,words]
  · simp [initialData,words]
  · simp [initialData,words]
  · rw [words_length]
  · rwa [prepareEnd_frontier]

theorem frontier_polynomial (input : Input) : (Layout.ofInput input).frontier≤10*(size input+1)^2 := by
  dsimp [Layout.ofInput,Layout.frontier,size]
  nlinarith [Nat.zero_le (input.1*input.2.1),Nat.zero_le (input.1*input.2.2.length),
    Nat.zero_le (input.2.1*input.2.2.length)]

theorem frontier_fits {w : Nat} (input : Input) (width : 8*Nat.log2 (size input+2)+2≤w) :
    Fits w (Layout.ofInput input).frontier := by
  apply WordBounds.polynomial_fits_uniform 10 2 (size input) w
  · have log : Nat.log2 (10+1)=3 := by decide
    simp only [log,Nat.reduceMul,Nat.reduceAdd]
    have l : 0≤Nat.log2 (size input+2) := Nat.zero_le _
    omega
  · simp only [Int.natAbs_natCast]
    exact frontier_polynomial input

theorem word_frontier_bound (input : Input) (x : Nat) (member : x∈words input) :
    x≤(Layout.ofInput input).frontier := by
  simp only [words,List.mem_append,List.mem_cons,List.mem_singleton,List.mem_map,List.not_mem_nil,or_false] at member
  rcases member with (header | left) | right
  · rcases header with equal | equal | equal
    all_goals subst x; dsimp [Layout.ofInput,Layout.frontier]; omega
  · obtain ⟨edge,inside,equal⟩ := left
    subst x; have := edge.1.isLt; dsimp [Layout.ofInput,Layout.frontier]; omega
  · obtain ⟨edge,inside,equal⟩ := right
    subst x; have := edge.2.isLt; dsimp [Layout.ofInput,Layout.frontier]; omega

theorem initialData_frontier_bounded (input : Input) :
    NaturalData.Bounded (Layout.ofInput input).frontier (initialData input) := by
  constructor
  · intro i; simp [initialData]
  · intro address
    simp only [initialData]
    split_ifs
    · rw [words_length]; dsimp [Layout.ofInput,Layout.frontier]; omega
    · cases found : (words input)[address-1]? with
      | none => simp
      | some value =>
        simp only [Option.getD_some]
        exact word_frontier_bound input value (List.mem_of_getElem? found)

theorem preparedInput_bounded (input : Input) :
    NaturalData.Bounded (Layout.ofInput input).frontier (preparedInput input) := by
  have before : NaturalData.Bounded (prepareEnd (words input).length input.1 input.2.1) (initialData input) := by
    rw [prepareEnd_frontier]
    exact initialData_frontier_bounded input
  simpa only [preparedInput,prepareEnd_frontier] using prepared5_bounded (initialData input)
    (words input).length input.1 input.2.1 input.2.2.length (by rw [words_length]) before

attribute [local simp] Reg.heap Reg.request Reg.allocated Reg.cursor Reg.zero Reg.one
  Reg.n Reg.m Reg.edges Reg.edgeLeft Reg.edgeRight Reg.partnerLeft Reg.partnerRight
  Reg.lengths Reg.rowLeft Reg.rowRight Reg.cells Reg.scratch
  Allocation.frontier Allocation.count Allocation.result Allocation.cursor Allocation.zero Allocation.one
  header0 header1 header2 header3 header4 header5 header6 header7 header8 header9
  prepared1 prepared2 prepared3 prepared4 prepared5 allocationState
  NaturalData.initialized NaturalData.allocated NaturalData.allocatedRegisters NaturalData.set

theorem preparedInput_pointers (input : Input) : (Layout.ofInput input).Pointers (preparedInput input) := by
  intro slot
  fin_cases slot <;> simp [preparedInput,Layout.Pointers,pointer,Layout.base,Layout.ofInput,words_length] <;> omega

theorem preparedInput_controls (input : Input) :
    (preparedInput input).1 Reg.n=input.1 ∧ (preparedInput input).1 Reg.m=input.2.1 ∧
    (preparedInput input).1 Reg.edges=input.2.2.length ∧
    (preparedInput input).1 Reg.one=1 ∧ (preparedInput input).1 Reg.zero=0 := by simp [preparedInput]

end LeanTrominoes.BipartiteMatching.DenseWordRAM
