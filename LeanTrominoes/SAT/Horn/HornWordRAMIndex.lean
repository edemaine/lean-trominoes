/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMProgram
import LeanTrominoes.Computation.RAM.NaturalData
import LeanTrominoes.Computation.RAM.WordBounds

/-! # Instruction certificate for one Horn occurrence-indexing iteration

This is an operational certificate for the concrete program, including every
address calculation, array operation, and increment. Its word checks are stated
explicitly so the global indexing invariant can supply them.
-/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

attribute [local simp] Reg.heap Reg.request Reg.allocated Reg.cursor Reg.zero Reg.one Reg.atoms Reg.rules Reg.occurrences Reg.heads Reg.edgeAtoms Reg.edgeRules Reg.seen Reg.buckets Reg.counters Reg.links Reg.stack Reg.index Reg.atom Reg.rule Reg.value Reg.top Reg.event Reg.scratch Reg.headValue Reg.output

abbrev Data := NaturalData 32

def readState (data : Data) (dst pointer index : Fin 32) : Data :=
  (data.set Reg.scratch (data.1 pointer+data.1 index)).set dst
    (data.2 (data.1 pointer+data.1 index))

def writeState (data : Data) (src pointer index : Fin 32) : Data :=
  (data.set Reg.scratch (data.1 pointer+data.1 index)).store
    (data.1 pointer+data.1 index) (data.1 src)

def ReadFits (w : ℕ) (data : Data) (pointer index : Fin 32) : Prop :=
  Fits w (data.1 pointer+data.1 index : ℕ) ∧
  Fits w (data.2 (data.1 pointer+data.1 index))

def WriteFits (w : ℕ) (data : Data) (src pointer index : Fin 32) : Prop :=
  Fits w (data.1 pointer+data.1 index : ℕ) ∧ Fits w (data.1 src)

theorem readState_exec {w : ℕ} (data : Data) (dst pointer index : Fin 32)
    (fits : ReadFits w data pointer index) :
    NaturalData.Exec w (read dst pointer index) data (readState data dst pointer index) 2 :=
  NaturalData.read_exec data Reg.scratch dst pointer index fits.1 fits.2

theorem writeState_exec {w : ℕ} (data : Data) (src pointer index : Fin 32)
    (different : src≠Reg.scratch) (fits : WriteFits w data src pointer index) :
    NaturalData.Exec w (write src pointer index) data (writeState data src pointer index) 2 :=
  NaturalData.write_exec data Reg.scratch src pointer index different fits.1 fits.2

theorem readState_bounded {bound : ℕ} {data : Data} (h : NaturalData.Bounded bound data)
    (dst pointer index : Fin 32) : NaturalData.Bounded (2*bound) (readState data dst pointer index) := by
  have address : data.1 pointer+data.1 index≤2*bound := by
    have := h.1 pointer; have := h.1 index; omega
  have value : data.2 (data.1 pointer+data.1 index)≤2*bound := (h.2 _).trans (by omega)
  exact ((h.mono (by omega)).set Reg.scratch address).set dst value

theorem writeState_bounded {bound : ℕ} {data : Data} (h : NaturalData.Bounded bound data)
    (src pointer index : Fin 32) : NaturalData.Bounded (2*bound) (writeState data src pointer index) := by
  have address : data.1 pointer+data.1 index≤2*bound := by
    have := h.1 pointer; have := h.1 index; omega
  exact ((h.mono (by omega)).set Reg.scratch address).store ((h.1 src).trans (by omega))

theorem read_fits_of_bound {w bound upper : ℕ} {data : Data}
    (h : NaturalData.Bounded bound data) (width : Fits w upper) (room : 2*bound≤upper)
    (pointer index : Fin 32) : ReadFits w data pointer index := by
  exact ⟨Allocation.nat_fits_le width (by have := h.1 pointer; have := h.1 index; omega),
    Allocation.nat_fits_le width ((h.2 _).trans (by omega))⟩

theorem write_fits_of_bound {w bound upper : ℕ} {data : Data}
    (h : NaturalData.Bounded bound data) (width : Fits w upper) (room : 2*bound≤upper)
    (src pointer index : Fin 32) : WriteFits w data src pointer index := by
  exact ⟨Allocation.nat_fits_le width (by have := h.1 pointer; have := h.1 index; omega),
    Allocation.nat_fits_le width ((h.1 _).trans (by omega))⟩

/-- These states name the actual register/memory changes of `indexBody`.
They are not additional instructions or unit-cost function calls. -/
def index1 (data : Data) := readState data Reg.atom Reg.edgeAtoms Reg.index
def index2 (data : Data) := readState (index1 data) Reg.rule Reg.edgeRules Reg.index
def index3 (data : Data) := readState (index2 data) Reg.value Reg.buckets Reg.atom
def index4 (data : Data) := writeState (index3 data) Reg.value Reg.links Reg.index
def index5 (data : Data) := (index4 data).set Reg.value ((index4 data).1 Reg.index+(index4 data).1 Reg.one)
def index6 (data : Data) := writeState (index5 data) Reg.value Reg.buckets Reg.atom
def index7 (data : Data) := readState (index6 data) Reg.value Reg.counters Reg.rule
def index8 (data : Data) := (index7 data).set Reg.value ((index7 data).1 Reg.value+(index7 data).1 Reg.one)
def index9 (data : Data) := writeState (index8 data) Reg.value Reg.counters Reg.rule
def index10 (data : Data) := (index9 data).set Reg.index ((index9 data).1 Reg.index+(index9 data).1 Reg.one)

structure IndexFits (w : ℕ) (data : Data) : Prop where
  atom : ReadFits w data Reg.edgeAtoms Reg.index
  rule : ReadFits w (index1 data) Reg.edgeRules Reg.index
  bucket : ReadFits w (index2 data) Reg.buckets Reg.atom
  link : WriteFits w (index3 data) Reg.value Reg.links Reg.index
  pointer : Fits w ((index4 data).1 Reg.index+(index4 data).1 Reg.one : ℕ)
  setBucket : WriteFits w (index5 data) Reg.value Reg.buckets Reg.atom
  counter : ReadFits w (index6 data) Reg.counters Reg.rule
  increment : Fits w ((index7 data).1 Reg.value+(index7 data).1 Reg.one : ℕ)
  setCounter : WriteFits w (index8 data) Reg.value Reg.counters Reg.rule
  nextIndex : Fits w ((index9 data).1 Reg.index+(index9 data).1 Reg.one : ℕ)

/-- A coarse constant amount of word headroom suffices for this entire
straight-line fragment, even before using the stronger indexing invariant. -/
theorem indexFits_of_bound {w bound : ℕ} {data : Data}
    (h : NaturalData.Bounded bound data) (width : Fits w (1024*bound : ℕ)) : IndexFits w data := by
  have h1 : NaturalData.Bounded (2*bound) (index1 data) := readState_bounded h _ _ _
  have h2 : NaturalData.Bounded (4*bound) (index2 data) := by
    simpa only [index2,← Nat.mul_assoc,Nat.reduceMul] using readState_bounded h1 Reg.rule Reg.edgeRules Reg.index
  have h3 : NaturalData.Bounded (8*bound) (index3 data) := by
    simpa only [index3,← Nat.mul_assoc,Nat.reduceMul] using readState_bounded h2 Reg.value Reg.buckets Reg.atom
  have h4 : NaturalData.Bounded (16*bound) (index4 data) := by
    simpa only [index4,← Nat.mul_assoc,Nat.reduceMul] using writeState_bounded h3 Reg.value Reg.links Reg.index
  have h5 : NaturalData.Bounded (32*bound) (index5 data) :=
    (h4.mono (by omega)).set Reg.value (by have := h4.1 Reg.index; have := h4.1 Reg.one; omega)
  have h6 : NaturalData.Bounded (64*bound) (index6 data) := by
    simpa only [index6,← Nat.mul_assoc,Nat.reduceMul] using writeState_bounded h5 Reg.value Reg.buckets Reg.atom
  have h7 : NaturalData.Bounded (128*bound) (index7 data) := by
    simpa only [index7,← Nat.mul_assoc,Nat.reduceMul] using readState_bounded h6 Reg.value Reg.counters Reg.rule
  have h8 : NaturalData.Bounded (256*bound) (index8 data) :=
    (h7.mono (by omega)).set Reg.value (by have := h7.1 Reg.value; have := h7.1 Reg.one; omega)
  have h9 : NaturalData.Bounded (512*bound) (index9 data) := by
    simpa only [index9,← Nat.mul_assoc,Nat.reduceMul] using writeState_bounded h8 Reg.value Reg.counters Reg.rule
  exact ⟨read_fits_of_bound h width (by omega) _ _,
    read_fits_of_bound h1 width (by omega) _ _,read_fits_of_bound h2 width (by omega) _ _,
    write_fits_of_bound h3 width (by omega) _ _ _,
    Allocation.nat_fits_le width (by have := h4.1 Reg.index; have := h4.1 Reg.one; omega),
    write_fits_of_bound h5 width (by omega) _ _ _,read_fits_of_bound h6 width (by omega) _ _,
    Allocation.nat_fits_le width (by have := h7.1 Reg.value; have := h7.1 Reg.one; omega),
    write_fits_of_bound h8 width (by omega) _ _ _,
    Allocation.nat_fits_le width (by have := h9.1 Reg.index; have := h9.1 Reg.one; omega)⟩

/-- One occurrence is installed in exactly seventeen primitive instructions.
Every memory address and written word is checked by the actual RAM semantics. -/
theorem indexBody_exec {w : ℕ} (data : Data) (fits : IndexFits w data) :
    NaturalData.Exec w indexBody data (index10 data) 17 := by
  have a := readState_exec data Reg.atom Reg.edgeAtoms Reg.index fits.atom
  have b := readState_exec (index1 data) Reg.rule Reg.edgeRules Reg.index fits.rule
  have c := readState_exec (index2 data) Reg.value Reg.buckets Reg.atom fits.bucket
  have d := writeState_exec (index3 data) Reg.value Reg.links Reg.index (by decide) fits.link
  have e := NaturalData.add_exec (index4 data) Reg.value Reg.index Reg.one fits.pointer
  have f := writeState_exec (index5 data) Reg.value Reg.buckets Reg.atom (by decide) fits.setBucket
  have g := readState_exec (index6 data) Reg.value Reg.counters Reg.rule fits.counter
  have h := NaturalData.add_exec (index7 data) Reg.value Reg.value Reg.one fits.increment
  have i := writeState_exec (index8 data) Reg.value Reg.counters Reg.rule (by decide) fits.setCounter
  have j := NaturalData.add_exec (index9 data) Reg.index Reg.index Reg.one fits.nextIndex
  exact a.seq (b.seq (c.seq (d.seq (e.seq (f.seq (g.seq (h.seq (i.seq j))))))))

def indexAtom (data : Data) : ℕ := data.2 (data.1 Reg.edgeAtoms+data.1 Reg.index)
def indexRule (data : Data) : ℕ := data.2 (data.1 Reg.edgeRules+data.1 Reg.index)
def indexLinksMemory (data : Data) : ℕ → ℕ :=
  Function.update data.2 (data.1 Reg.links+data.1 Reg.index)
    (data.2 (data.1 Reg.buckets+indexAtom data))
def indexBucketsMemory (data : Data) : ℕ → ℕ :=
  Function.update (indexLinksMemory data) (data.1 Reg.buckets+indexAtom data)
    (data.1 Reg.index+data.1 Reg.one)
def indexCounter (data : Data) : ℕ := indexBucketsMemory data (data.1 Reg.counters+indexRule data)

theorem index10_memory (data : Data) : (index10 data).2=
    Function.update (indexBucketsMemory data) (data.1 Reg.counters+indexRule data)
      (indexCounter data+data.1 Reg.one) := by
  simp [index10,index9,index8,index7,index6,index5,index4,index3,index2,index1,
    readState,writeState,NaturalData.set,NaturalData.store,
    indexBucketsMemory,indexLinksMemory,indexAtom,indexRule,indexCounter]

theorem index10_registers (data : Data) : (index10 data).1=
    Function.update (Function.update (Function.update (Function.update (Function.update data.1
      Reg.atom (indexAtom data)) Reg.rule (indexRule data))
      Reg.value (indexCounter data+data.1 Reg.one))
      Reg.scratch (data.1 Reg.counters+indexRule data))
      Reg.index (data.1 Reg.index+data.1 Reg.one) := by
  funext i
  fin_cases i <;>
    simp [index10,index9,index8,index7,index6,index5,index4,index3,index2,index1,
      readState,writeState,NaturalData.set,NaturalData.store,
      indexBucketsMemory,indexLinksMemory,indexAtom,indexRule,indexCounter]

theorem update_bound {I : Type} [DecidableEq I] {f : I → ℕ} {bound value : ℕ}
    (h : ∀ i, f i≤bound) (i : I) (valueBound : value≤bound) :
    ∀ j, Function.update f i value j≤bound := by
  intro j
  simp only [Function.update_apply]
  split
  · exact valueBound
  · exact h j

/-- Even without non-aliasing assumptions, this fragment increases the maximum
memory word by at most index+2. This deliberately loose polynomial invariant
is sufficient for logarithmic words; the semantic invariant supplies sharper
counter bounds separately. -/
theorem index10_bounds {regBound memBound : ℕ} (data : Data)
    (regs : ∀ i, data.1 i≤regBound) (memory : ∀ a, data.2 a≤memBound)
    (unit : data.1 Reg.one=1) :
    (∀ i, (index10 data).1 i≤regBound+memBound+data.1 Reg.index+2) ∧
    (∀ a, (index10 data).2 a≤memBound+data.1 Reg.index+2) := by
  have atom : indexAtom data≤memBound := memory _
  have rule : indexRule data≤memBound := memory _
  have links : ∀ a, indexLinksMemory data a≤memBound :=
    update_bound memory _ (memory _)
  have buckets : ∀ a, indexBucketsMemory data a≤memBound+data.1 Reg.index+1 := by
    apply update_bound
    · intro a; exact (links a).trans (by omega)
    · rw [unit]; omega
  have counter : indexCounter data≤memBound+data.1 Reg.index+1 := buckets _
  constructor
  · rw [index10_registers]
    apply update_bound
    · apply update_bound
      · apply update_bound
        · apply update_bound
          · apply update_bound
            · intro i; exact (regs i).trans (by omega)
            · omega
          · omega
        · rw [unit]; omega
      · have := regs Reg.counters; omega
    · rw [unit]; omega
  · rw [index10_memory]
    apply update_bound
    · intro a; exact (buckets a).trans (by omega)
    · rw [unit]; omega

theorem index10_control (data : Data) :
    (index10 data).1 Reg.index=data.1 Reg.index+data.1 Reg.one ∧
    (index10 data).1 Reg.one=data.1 Reg.one ∧
    (index10 data).1 Reg.occurrences=data.1 Reg.occurrences := by
  simp [index10,index9,index8,index7,index6,index5,index4,index3,index2,index1,
    readState,writeState,NaturalData.set,NaturalData.store]

/-- The indexing loop executes 19 instructions per occurrence, plus two for
its final test. The bounded-state hypothesis is supplied by the global memory
invariant; it is not an assumed runtime or correctness result. -/
theorem indexLoop_exec {w bound remaining : ℕ} (data : Data)
    (unit : data.1 Reg.one=1)
    (remaining_eq : data.1 Reg.index+remaining=data.1 Reg.occurrences)
    (bounded : ∀ k, k<remaining → NaturalData.Bounded bound ((index10^[k]) data))
    (width : Fits w (1024*bound : ℕ)) :
    NaturalData.Exec w (.loop (.lt Reg.index Reg.occurrences) indexBody) data
      ((index10^[remaining]) data) (19*remaining+2) := by
  induction remaining generalizing data with
  | zero =>
    have stop : ¬Structured.Condition.Holds (.lt Reg.index Reg.occurrences) data.word := by
      simp only [Structured.Condition.Holds,NaturalData.word]
      have same : data.1 Reg.index=data.1 Reg.occurrences := by omega
      simp only [same,lt_self_iff_false,not_false_eq_true]
    exact Structured.Exec.loop_done stop
  | succ remaining ih =>
    have step := indexBody_exec data (indexFits_of_bound (bounded 0 (by omega)) width)
    have control := index10_control data
    have nextUnit : (index10 data).1 Reg.one=1 := control.2.1.trans unit
    have nextRemaining : (index10 data).1 Reg.index+remaining=(index10 data).1 Reg.occurrences := by
      rw [control.1,control.2.2,unit]
      omega
    have nextBounded : ∀ k, k<remaining → NaturalData.Bounded bound ((index10^[k]) (index10 data)) := by
      intro k hk
      simpa only [Function.iterate_succ_apply] using bounded (k+1) (by omega)
    have rest := ih (index10 data) nextUnit nextRemaining nextBounded
    have holds : Structured.Condition.Holds (.lt Reg.index Reg.occurrences) data.word := by
      simp only [Structured.Condition.Holds,NaturalData.word]
      exact_mod_cast (show data.1 Reg.index<data.1 Reg.occurrences by omega)
    have trace := Structured.Exec.loop_more holds step rest
    have cost : 17+(19*remaining+2)+2=19*(remaining+1)+2 := by omega
    simpa only [Function.iterate_succ_apply,cost] using trace

/-- Initialization of the loop index is charged as well. -/
theorem buildIndex_exec {w bound : ℕ} (data : Data)
    (unit : data.1 Reg.one=1)
    (bounded : ∀ k, k<data.1 Reg.occurrences →
      NaturalData.Bounded bound ((index10^[k]) (data.set Reg.index 0)))
    (width : Fits w (1024*bound : ℕ)) :
    NaturalData.Exec w buildIndex data
      ((index10^[data.1 Reg.occurrences]) (data.set Reg.index 0))
      (19*data.1 Reg.occurrences+3) := by
  have initialized := NaturalData.constant_exec data Reg.index 0
    (Allocation.nat_fits_le width (by omega))
  have one : (data.set Reg.index 0).1 Reg.one=1 := by simpa [NaturalData.set] using unit
  have occurrences : (data.set Reg.index 0).1 Reg.occurrences=data.1 Reg.occurrences := by
    simp [NaturalData.set]
  have trace := indexLoop_exec (remaining := data.1 Reg.occurrences) (data.set Reg.index 0) one
    (by simp [NaturalData.set]) bounded width
  have cost : 1+(19*data.1 Reg.occurrences+2)=19*data.1 Reg.occurrences+3 := by omega
  simpa only [buildIndex,constant,cost] using initialized.seq trace

/-- Uniform bound for all natural words during the indexing loop. -/
def indexBound (bound occurrences : ℕ) : ℕ :=
  bound+occurrences*(bound+occurrences*(bound+2)+bound+2)+bound+occurrences*(bound+2)

theorem index_prefix_bounded {bound : ℕ} (data : Data)
    (initial : NaturalData.Bounded bound data) (unit : data.1 Reg.one=1) (start : data.1 Reg.index=0)
    (k : ℕ) (within : k≤data.1 Reg.occurrences) :
    NaturalData.Bounded (indexBound bound (data.1 Reg.occurrences)) ((index10^[k]) data) := by
  let total := data.1 Reg.occurrences
  let rise := bound+total*(bound+2)+bound+2
  have totalBound : total≤bound := initial.1 Reg.occurrences
  have inv : ∀ n, n≤total →
      ((index10^[n]) data).1 Reg.one=1 ∧ ((index10^[n]) data).1 Reg.index=n ∧
      (∀ a, ((index10^[n]) data).2 a≤bound+n*(bound+2)) ∧
      (∀ i, ((index10^[n]) data).1 i≤bound+n*rise) := by
    intro n
    induction n with
    | zero =>
      intro _
      simpa only [Function.iterate_zero_apply,Nat.zero_mul,Nat.add_zero] using
        (show data.1 Reg.one=1 ∧ data.1 Reg.index=0 ∧ (∀ a, data.2 a≤bound) ∧
          (∀ i, data.1 i≤bound) from ⟨unit,start,initial.2,initial.1⟩)
    | succ n ih =>
      intro hn
      obtain ⟨one,index,memory,regs⟩ := ih (by omega)
      have step := index10_bounds ((index10^[n]) data) regs memory one
      have control := index10_control ((index10^[n]) data)
      rw [Function.iterate_succ_apply']
      refine ⟨control.2.1.trans one,?_,?_,?_⟩
      · rw [control.1,index,one]
      · intro a
        have h := step.2 a
        rw [index] at h
        have nBound : n≤bound := by omega
        simp only [Nat.add_mul,Nat.one_mul]
        omega
      · intro i
        have h := step.1 i
        rw [index] at h
        have nBound : n≤bound := by omega
        have growth : bound+n*(bound+2)+n+2≤rise := by
          have le : n*(bound+2)≤total*(bound+2) := Nat.mul_le_mul_right _ (by omega)
          dsimp [rise]
          omega
        simp only [Nat.add_mul,Nat.one_mul]
        omega
  obtain ⟨_,_,memory,regs⟩ := inv k within
  constructor
  · intro i
    have le := Nat.mul_le_mul_right rise within
    have h := regs i
    dsimp [indexBound,rise,total] at *
    omega
  · intro a
    have le := Nat.mul_le_mul_right (bound+2) within
    have h := memory a
    dsimp [indexBound,total] at *
    omega

theorem indexBound_polynomial (bound occurrences : ℕ) (le : occurrences≤bound) :
    indexBound bound occurrences≤8*(bound+1)^3 := by
  have memory := Nat.mul_le_mul_right (bound+2) le
  have registers : occurrences*(bound+occurrences*(bound+2)+bound+2)≤
      bound*(bound+bound*(bound+2)+bound+2) := Nat.mul_le_mul le (by omega)
  dsimp [indexBound]
  nlinarith [Nat.zero_le (bound^3)]

/-- The complete indexing phase has a genuine linear RAM execution for every
word size above a logarithmic threshold. It needs no aliasing assumptions or
unbounded counters. The semantic index invariant is proved separately. -/
theorem buildIndex_exec_bounded {w bound : ℕ} (data : Data)
    (initial : NaturalData.Bounded bound data) (unit : data.1 Reg.one=1)
    (width : 19*Nat.log2 (bound+2)+2≤w) :
    NaturalData.Exec w buildIndex data
      ((index10^[data.1 Reg.occurrences]) (data.set Reg.index 0))
      (19*data.1 Reg.occurrences+3) := by
  have top : Fits w (1024*indexBound bound (data.1 Reg.occurrences) : ℕ) := by
    apply WordBounds.polynomial_fits_uniform 8192 3 bound w
    · have log : Nat.log2 (8192+1)=13 := by decide
      simpa only [log,Nat.reduceMul,Nat.reduceAdd] using width
    · have polynomial := indexBound_polynomial bound (data.1 Reg.occurrences) (initial.1 Reg.occurrences)
      simpa only [Int.natAbs_natCast,← Nat.mul_assoc,Nat.reduceMul] using Nat.mul_le_mul_left 1024 polynomial
  apply buildIndex_exec data unit (bound := indexBound bound (data.1 Reg.occurrences)) ?_ top
  intro k hk
  have zeroed := initial.set Reg.index (show 0≤bound by omega)
  have one : (data.set Reg.index 0).1 Reg.one=1 := by simpa [NaturalData.set] using unit
  have occurrences : (data.set Reg.index 0).1 Reg.occurrences=data.1 Reg.occurrences := by simp [NaturalData.set]
  have bounded := index_prefix_bounded (data.set Reg.index 0) zeroed one (by simp [NaturalData.set]) k
    (by rw [occurrences]; omega)
  simpa only [occurrences] using bounded

/-- The same certificate gives a trace inside the original flat RAM program;
no function-call or array-operation primitive is assumed. -/
theorem indexBody_compiles {w pc : ℕ} {code : List (Instruction 32)} (data : Data)
    (fits : IndexFits w data) (contained : Contains code pc (indexBody.assemble pc))
    (capacity : pc+indexBody.size<2^w) :
    RunsTo w code (data.word.at pc) ((index10 data).word.at (pc+indexBody.size)) 17 :=
  (indexBody_exec data fits).compiles contained capacity

end LeanTrominoes.Horn.WordRAM
