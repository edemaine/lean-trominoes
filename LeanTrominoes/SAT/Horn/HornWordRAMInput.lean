/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMPrepare

/-! # The Horn RAM input boundary and initialized execution prefix -/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

def initialData (input : Input) : Data :=
  (fun _ => 0,fun address => if address=0 then (words input).length
    else (words input)[address-1]?.getD 0)

theorem initialData_word (input : Input) :
    (initialData input).word=(initial (r := 32) (encode input)).data := by
  apply Prod.ext
  · rfl
  · funext address
    by_cases zero : address=0
    · subst address
      simp [NaturalData.word,initialData,initial,State.data,encode]
    · cases value : (words input)[address-1]? <;>
        simp [NaturalData.word,initialData,initial,State.data,encode,zero,value,Int.ofNat_eq_natCast]

theorem atomCode_le {n : ℕ} (a : Option (Fin n)) : atomCode a≤n := by
  cases a with
  | none => simp [atomCode]
  | some i => simp only [atomCode]; omega

theorem word_le_size (input : Input) (value : ℕ) (member : value∈words input) : value≤size input := by
  simp only [words,List.mem_append] at member
  rcases member with ((header | head) | atom) | rule
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at header
    rcases header with rfl | rfl | rfl <;> simp only [size] <;> omega
  · obtain ⟨r,_,rfl⟩ := List.mem_map.mp head
    exact (atomCode_le _).trans (by dsimp [size]; omega)
  · obtain ⟨ar,_,rfl⟩ := List.mem_map.mp atom
    exact (atomCode_le _).trans (by dsimp [size]; omega)
  · obtain ⟨ar,_,rfl⟩ := List.mem_map.mp rule
    have bound := ar.2.isLt
    dsimp [size,Indexed.RuleId] at *
    omega

theorem initialData_bounded (input : Input) : NaturalData.Bounded (3*size input) (initialData input) := by
  constructor
  · intro i
    simp [initialData]
  · intro address
    simp only [initialData]
    split
    · rw [words_length]
      dsimp [size]
      omega
    · cases value : (words input)[address-1]? with
      | none => simp
      | some n =>
        have bound := word_le_size input n (List.mem_of_getElem? value)
        simpa only [value,Option.getD_some] using bound.trans (show size input≤3*size input by omega)

/-- The initialized prefix executes on exactly the public RAM calling
convention, for every sufficiently large logarithmic word size. This theorem
covers input loading and allocation, before indexing or propagation. -/
theorem prepare_on_input {w : ℕ} (input : Input)
    (width : 5*Nat.log2 (size input+2)+2≤w) :
    Structured.Exec w prepare (initial (r := 32) (encode input)).data
      (prepared5 (initialData input) (words input).length input.1 input.2.rules.size
        (Indexed.edges input.2).length).word
      (4*(2*(input.1+1)+2*input.2.rules.size+(Indexed.edges input.2).length)+59) := by
  have endpoint : Fits w (prepareEnd (words input).length input.1 input.2.rules.size
      (Indexed.edges input.2).length : ℕ) := by
    apply WordBounds.polynomial_fits_uniform 8 1 (size input) w
    · have log : Nat.log2 (8+1)=3 := by decide
      simpa only [log,Nat.reduceMul,Nat.reduceAdd] using width
    · simp only [Int.natAbs_natCast,pow_one,prepareEnd,words_length,size]
      omega
  have trace := prepare_exec (initialData input) (words input).length input.1 input.2.rules.size
    (Indexed.edges input.2).length
    (by simp [initialData]) (by simp [initialData,words])
    (by simp [initialData,words]) (by simp [initialData,words])
    (by rw [words_length]; omega) endpoint
  simpa only [NaturalData.Exec,initialData_word] using trace

def preparedInput (input : Input) : Data :=
  prepared5 (initialData input) (words input).length input.1 input.2.rules.size (Indexed.edges input.2).length

def preparedBound (input : Input) : ℕ :=
  prepareEnd (words input).length input.1 input.2.rules.size (Indexed.edges input.2).length

theorem preparedInput_bounded (input : Input) : NaturalData.Bounded (preparedBound input) (preparedInput input) := by
  apply prepared5_bounded
  · rw [words_length]; omega
  · constructor
    · intro i; simp [initialData]
    · intro address
      simp only [initialData]
      split
      · dsimp [prepareEnd]; omega
      · cases value : (words input)[address-1]? with
        | none => simp
        | some n =>
          have h := word_le_size input n (List.mem_of_getElem? value)
          have le : size input≤preparedBound input := by
            dsimp [preparedBound,prepareEnd,size]
            rw [words_length]
            omega
          simpa only [value,Option.getD_some,preparedBound] using h.trans le

theorem buildIndex_on_input {w : ℕ} (input : Input)
    (width : 27*Nat.log2 (size input+2)+2≤w) :
    NaturalData.Exec w buildIndex (preparedInput input)
      ((index10^[(Indexed.edges input.2).length]) ((preparedInput input).set Reg.index 0))
      (19*(Indexed.edges input.2).length+3) := by
  let data := preparedInput input
  let bound := preparedBound input
  let events := (Indexed.edges input.2).length
  have control : data.1 Reg.one=1 ∧ data.1 Reg.occurrences=events :=
    prepared5_controls _ _ _ _ _
  have initial : NaturalData.Bounded bound data := preparedInput_bounded input
  have eventBound : events≤bound := by simpa only [control.2] using initial.1 Reg.occurrences
  have boundSize : bound≤6*size input := by
    dsimp [bound,preparedBound,prepareEnd,size]
    rw [words_length]
    omega
  have top : Fits w (1024*indexBound bound events : ℕ) := by
    apply WordBounds.polynomial_fits_uniform 2097152 3 (size input) w
    · have log : Nat.log2 (2097152+1)=21 := by decide
      simpa only [log,Nat.reduceMul,Nat.reduceAdd] using width
    · simp only [Int.natAbs_natCast]
      have polynomial := indexBound_polynomial bound events eventBound
      have power : (bound+1)^3≤(6*(size input+1))^3 := Nat.pow_le_pow_left (by omega) 3
      calc
        1024*indexBound bound events≤8192*(bound+1)^3 := by omega
        _≤8192*(6*(size input+1))^3 := Nat.mul_le_mul_left _ power
        _≤2097152*(size input+1)^3 := by nlinarith [Nat.zero_le ((size input+1)^3)]
  have trace := buildIndex_exec data control.1 (bound := indexBound bound events)
    (fun k hk => by
      have zeroed := initial.set Reg.index (show 0≤bound by omega)
      have one : (data.set Reg.index 0).1 Reg.one=1 := by
        simpa [NaturalData.set,Reg.index,Reg.one] using control.1
      have bounded := index_prefix_bounded (data.set Reg.index 0) zeroed one
        (by simp [NaturalData.set]) k (by simpa [NaturalData.set,Reg.index,Reg.occurrences] using hk.le)
      simpa only [NaturalData.set,Function.update_of_ne (show Reg.occurrences≠Reg.index by decide),control.2]
        using bounded) top
  simpa only [control.2] using trace

def indexedInput (input : Input) : Data :=
  (index10^[(Indexed.edges input.2).length]) ((preparedInput input).set Reg.index 0)

theorem prepare_size : prepare.size=74 := rfl
theorem buildIndex_size : buildIndex.size=21 := rfl

/-- Starting at the actual encoded input, the original bytecode reaches the
end of occurrence indexing in a linear number of primitive steps. The PC is
95; stack initialization and propagation follow after this prefix. -/
theorem indexed_prefix_exec {w : ℕ} (input : Input)
    (width : 27*Nat.log2 (size input+2)+2≤w) :
    RunsTo w bytecode (initial (encode input)) ((indexedInput input).word.at 95)
      (8*input.1+8*input.2.rules.size+23*(Indexed.edges input.2).length+70) := by
  have log : 1≤Nat.log2 (size input+2) := by
    have mono := Nat.log_mono_right (b := 2) (show 2≤size input+2 by omega)
    simpa [← Nat.log2_eq_log_two] using mono
  have seven : 7≤w := by omega
  have capacity : 95<2^w := by
    have power : (2 : ℕ)^7≤2^w := pow_le_pow_right₀ (by decide) seven
    norm_num at power
    omega
  have whole : Contains bytecode 0 (program.assemble 0) :=
    Contains.append (program.assemble 0) [.halt Reg.output]
  let suffix : Code := .seq buildIndex (.seq initialStack (.seq propagate answer))
  change Contains bytecode 0 (prepare.assemble 0 ++ suffix.assemble (0+prepare.size)) at whole
  have front := whole.append_left
  have rest := whole.append_right
  simp only [Structured.Code.assemble_length,Nat.zero_add] at rest
  change Contains bytecode prepare.size
    (buildIndex.assemble prepare.size ++
      (.seq initialStack (.seq propagate answer) : Code).assemble (prepare.size+buildIndex.size)) at rest
  have indexed := rest.append_left
  have one := (prepare_on_input (w := w) input (by omega)).compiles front
    (by rw [prepare_size]; omega)
  have first : RunsTo w bytecode (initial (encode input)) ((preparedInput input).word.at 74)
      (4*(2*(input.1+1)+2*input.2.rules.size+(Indexed.edges input.2).length)+59) := by
    simpa only [preparedInput,prepare_size,Nat.zero_add,ComplexityAbstract.RAM.Data.at,State.data,initial] using one
  have two := (buildIndex_on_input input width).compiles indexed
    (by rw [prepare_size,buildIndex_size]; omega)
  have second : RunsTo w bytecode ((preparedInput input).word.at 74)
      ((indexedInput input).word.at 95) (19*(Indexed.edges input.2).length+3) := by
    simpa only [prepare_size,buildIndex_size,indexedInput,Nat.reduceAdd] using two
  have cost : (4*(2*(input.1+1)+2*input.2.rules.size+(Indexed.edges input.2).length)+59)+
      (19*(Indexed.edges input.2).length+3)=
      8*input.1+8*input.2.rules.size+23*(Indexed.edges input.2).length+70 := by omega
  simpa only [cost] using first.trans second

theorem indexed_prefix_linear (input : Input) :
    8*input.1+8*input.2.rules.size+23*(Indexed.edges input.2).length+70≤70*size input := by
  dsimp [size]
  omega

end LeanTrominoes.Horn.WordRAM
