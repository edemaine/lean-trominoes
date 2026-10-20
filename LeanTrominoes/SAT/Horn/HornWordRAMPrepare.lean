/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMIndex
import LeanTrominoes.Computation.RAM.NaturalAllocation

/-! # Initialization certificates for the concrete Horn RAM program -/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

attribute [local simp] Reg.heap Reg.request Reg.allocated Reg.cursor Reg.zero Reg.one
  Reg.atoms Reg.rules Reg.occurrences Reg.heads Reg.edgeAtoms Reg.edgeRules Reg.seen
  Reg.buckets Reg.counters Reg.links Reg.stack Reg.index Reg.atom Reg.rule Reg.value
  Reg.top Reg.event Reg.scratch Reg.headValue Reg.output
  Allocation.frontier Allocation.count Allocation.result Allocation.cursor Allocation.zero Allocation.one

def allocationState (data : Data) (dst length : Fin 32) : Data :=
  ((data.set Reg.request (data.1 length)).allocated (data.1 Reg.heap) (data.1 length)).set dst (data.1 Reg.heap)

/-- Copying the requested length and returning the block pointer are both
charged, in addition to initialization of every allocated word. -/
theorem allocate_exec {w : ℕ} (data : Data) (dst length : Fin 32)
    (width : Fits w (data.1 Reg.heap+data.1 length : ℕ)) (unit : Fits w 1) :
    NaturalData.Exec w (allocate dst length) data (allocationState data dst length)
      (4*data.1 length+9) := by
  have request := NaturalData.copy_exec data Reg.request length
    (Allocation.nat_fits_le width (by omega))
  have allocated := NaturalData.allocate_exec (r := 26) (data.set Reg.request (data.1 length))
    (data.1 Reg.heap) (data.1 length) (by simp [NaturalData.set]) (by simp [NaturalData.set]) width unit
  have pointer := NaturalData.copy_exec
    ((data.set Reg.request (data.1 length)).allocated (data.1 Reg.heap) (data.1 length)) dst Reg.allocated
    (by simpa [NaturalData.allocated,NaturalData.allocatedRegisters] using
      Allocation.nat_fits_le width (show data.1 Reg.heap≤data.1 Reg.heap+data.1 length by omega))
  have trace := request.seq (allocated.seq pointer)
  have result : ((data.set Reg.request (data.1 length)).allocated
      (data.1 Reg.heap) (data.1 length)).1 Reg.allocated=data.1 Reg.heap := by
    simp [NaturalData.allocated,NaturalData.allocatedRegisters]
  have cost : 1+(4*data.1 length+7+1)=4*data.1 length+9 := by omega
  simpa only [allocate,copy,allocationState,result,cost] using trace

theorem allocationState_bounded {bound : ℕ} {data : Data} (dst length : Fin 32)
    (initial : NaturalData.Bounded bound data) (endpoint : data.1 Reg.heap+data.1 length≤bound)
    (unit : 1≤bound) : NaturalData.Bounded bound (allocationState data dst length) :=
  (NaturalData.allocated_bounded (r := 26) (initial := initial.set Reg.request (initial.1 length)) endpoint unit).set dst (initial.1 Reg.heap)

def header0 (data : Data) (header : ℕ) := data.initialized header
def header1 (data : Data) (header : ℕ) := (header0 data header).set Reg.scratch 1
def header2 (data : Data) (header n : ℕ) := (header1 data header).set Reg.atoms n
def header3 (data : Data) (header n : ℕ) := (header2 data header n).set Reg.atoms (n+1)
def header4 (data : Data) (header n : ℕ) := (header3 data header n).set Reg.scratch 2
def header5 (data : Data) (header n m : ℕ) := (header4 data header n).set Reg.rules m
def header6 (data : Data) (header n m : ℕ) := (header5 data header n m).set Reg.scratch 3
def header7 (data : Data) (header n m events : ℕ) := (header6 data header n m).set Reg.occurrences events
def header8 (data : Data) (header n m events : ℕ) := (header7 data header n m events).set Reg.heads 4
def header9 (data : Data) (header n m events : ℕ) := (header8 data header n m events).set Reg.edgeAtoms (4+m)
def header10 (data : Data) (header n m events : ℕ) := (header9 data header n m events).set Reg.edgeRules (4+m+events)

/-- Reading the three count headers, establishing all input pointers, and
initializing the allocation frontier takes fourteen primitive instructions. -/
theorem header_exec {w : ℕ} (data : Data) (header n m events bound : ℕ)
    (h0 : data.2 0=header) (h1 : data.2 1=n) (h2 : data.2 2=m) (h3 : data.2 3=events)
    (room : header+1≤bound ∧ n+1≤bound ∧ 4+m+events≤bound) (width : Fits w bound) :
    NaturalData.Exec w headerProgram data (header10 data header n m events) 14 := by
  have unit : Fits w 1 := by simpa using Allocation.nat_fits_le (a := 1) width (by omega)
  have a := NaturalData.initialize_exec (r := 26) data header h0
    (Allocation.nat_fits_le width room.1) unit
  have b := NaturalData.constant_exec (header0 data header) Reg.scratch 1 unit
  have c : NaturalData.Exec w (.atom (.load Reg.atoms Reg.scratch)) (header1 data header)
      (header2 data header n) 1 := by
    simpa [header2,header1,header0,NaturalData.initialized,NaturalData.set,h1] using
      NaturalData.load_exec (header1 data header) Reg.atoms Reg.scratch
        (by simpa [header1,NaturalData.set] using unit)
        (by simpa [header2,header1,header0,NaturalData.initialized,NaturalData.set,h1] using
          Allocation.nat_fits_le width (show n≤bound by omega))
  have d : NaturalData.Exec w (increment Reg.atoms) (header2 data header n) (header3 data header n) 1 := by
    simpa [increment,add,header3,header2,header1,header0,NaturalData.initialized,NaturalData.set] using
      NaturalData.add_exec (header2 data header n) Reg.atoms Reg.atoms Reg.one
        (by simpa [header2,header1,header0,NaturalData.initialized,NaturalData.set] using
          Allocation.nat_fits_le width room.2.1)
  have e := NaturalData.constant_exec (header3 data header n) Reg.scratch 2
    (Allocation.nat_fits_le width (by omega))
  have f : NaturalData.Exec w (.atom (.load Reg.rules Reg.scratch)) (header4 data header n)
      (header5 data header n m) 1 := by
    simpa [header5,header4,header3,header2,header1,header0,NaturalData.initialized,NaturalData.set,h2] using
      NaturalData.load_exec (header4 data header n) Reg.rules Reg.scratch
        (by simpa [header4,NaturalData.set] using Allocation.nat_fits_le width (show 2≤bound by omega))
        (by simpa [header4,header3,header2,header1,header0,NaturalData.initialized,NaturalData.set,h2] using
          Allocation.nat_fits_le width (show m≤bound by omega))
  have g := NaturalData.constant_exec (header5 data header n m) Reg.scratch 3
    (Allocation.nat_fits_le width (by omega))
  have h : NaturalData.Exec w (.atom (.load Reg.occurrences Reg.scratch)) (header6 data header n m)
      (header7 data header n m events) 1 := by
    simpa [header7,header6,header5,header4,header3,header2,header1,header0,
      NaturalData.initialized,NaturalData.set,h3] using
      NaturalData.load_exec (header6 data header n m) Reg.occurrences Reg.scratch
        (by simpa [header6,NaturalData.set] using Allocation.nat_fits_le width (show 3≤bound by omega))
        (by simpa [header6,header5,header4,header3,header2,header1,header0,
          NaturalData.initialized,NaturalData.set,h3] using
          Allocation.nat_fits_le width (show events≤bound by omega))
  have i := NaturalData.constant_exec (header7 data header n m events) Reg.heads 4
    (Allocation.nat_fits_le width (by omega))
  have j : NaturalData.Exec w (add Reg.edgeAtoms Reg.heads Reg.rules) (header8 data header n m events)
      (header9 data header n m events) 1 := by
    simpa [add,header9,header8,header7,header6,header5,NaturalData.set] using
      NaturalData.add_exec (header8 data header n m events) Reg.edgeAtoms Reg.heads Reg.rules
        (by simpa [header8,header7,header6,header5,NaturalData.set] using
          Allocation.nat_fits_le width (show 4+m≤bound by omega))
  have k : NaturalData.Exec w (add Reg.edgeRules Reg.edgeAtoms Reg.occurrences) (header9 data header n m events)
      (header10 data header n m events) 1 := by
    simpa [add,header10,header9,header8,header7,NaturalData.set] using
      NaturalData.add_exec (header9 data header n m events) Reg.edgeRules Reg.edgeAtoms Reg.occurrences
        (by simpa [header9,header8,header7,NaturalData.set] using
          Allocation.nat_fits_le width room.2.2)
  exact a.seq (b.seq (c.seq (d.seq (e.seq (f.seq (g.seq (h.seq (i.seq (j.seq k)))))))))

def prepared1 (data : Data) (h n m e : ℕ) := allocationState (header10 data h n m e) Reg.seen Reg.atoms
def prepared2 (data : Data) (h n m e : ℕ) := allocationState (prepared1 data h n m e) Reg.buckets Reg.atoms
def prepared3 (data : Data) (h n m e : ℕ) := allocationState (prepared2 data h n m e) Reg.counters Reg.rules
def prepared4 (data : Data) (h n m e : ℕ) := allocationState (prepared3 data h n m e) Reg.links Reg.occurrences
def prepared5 (data : Data) (h n m e : ℕ) := allocationState (prepared4 data h n m e) Reg.stack Reg.rules

def prepareEnd (header n m events : ℕ) : ℕ := header+1+2*(n+1)+2*m+events

attribute [local simp] header0 header1 header2 header3 header4 header5 header6 header7 header8 header9 header10
  prepared1 prepared2 prepared3 prepared4 prepared5 allocationState
  NaturalData.initialized NaturalData.allocated NaturalData.allocatedRegisters NaturalData.set

theorem header10_bounded {bound : ℕ} (data : Data) (header n m events : ℕ)
    (initial : NaturalData.Bounded bound data)
    (room : header+1≤bound ∧ n+1≤bound ∧ 4+m+events≤bound) :
    NaturalData.Bounded bound (header10 data header n m events) := by
  have zero : 0≤bound := by omega
  have one : 1≤bound := by omega
  have a : NaturalData.Bounded bound (header0 data header) :=
    ((initial.set Reg.zero zero).set Reg.one one).set Reg.heap room.1
  have b : NaturalData.Bounded bound (header1 data header) := a.set Reg.scratch one
  have c : NaturalData.Bounded bound (header2 data header n) := b.set Reg.atoms (by omega)
  have d : NaturalData.Bounded bound (header3 data header n) := c.set Reg.atoms room.2.1
  have e : NaturalData.Bounded bound (header4 data header n) := d.set Reg.scratch (by omega)
  have f : NaturalData.Bounded bound (header5 data header n m) := e.set Reg.rules (by omega)
  have g : NaturalData.Bounded bound (header6 data header n m) := f.set Reg.scratch (by omega)
  have h : NaturalData.Bounded bound (header7 data header n m events) := g.set Reg.occurrences (by omega)
  have i : NaturalData.Bounded bound (header8 data header n m events) := h.set Reg.heads (by omega)
  have j : NaturalData.Bounded bound (header9 data header n m events) := i.set Reg.edgeAtoms (by omega)
  exact j.set Reg.edgeRules room.2.2

theorem prepared5_bounded (data : Data) (header n m events : ℕ)
    (headerLength : 3≤header) (initial : NaturalData.Bounded (prepareEnd header n m events) data) :
    NaturalData.Bounded (prepareEnd header n m events) (prepared5 data header n m events) := by
  have room : header+1≤prepareEnd header n m events ∧ n+1≤prepareEnd header n m events ∧
      4+m+events≤prepareEnd header n m events := by
    dsimp [prepareEnd]
    omega
  have unit : 1≤prepareEnd header n m events := by dsimp [prepareEnd]; omega
  have a := header10_bounded data header n m events initial room
  have b : NaturalData.Bounded (prepareEnd header n m events) (prepared1 data header n m events) :=
    allocationState_bounded _ _ a (by simp; dsimp [prepareEnd]; omega) unit
  have c : NaturalData.Bounded (prepareEnd header n m events) (prepared2 data header n m events) :=
    allocationState_bounded _ _ b (by simp; dsimp [prepareEnd]; omega) unit
  have d : NaturalData.Bounded (prepareEnd header n m events) (prepared3 data header n m events) :=
    allocationState_bounded _ _ c (by simp; dsimp [prepareEnd]; omega) unit
  have e : NaturalData.Bounded (prepareEnd header n m events) (prepared4 data header n m events) :=
    allocationState_bounded _ _ d (by simp; dsimp [prepareEnd]; omega) unit
  exact allocationState_bounded _ _ e (by simp; dsimp [prepareEnd]; omega) unit

theorem prepared5_controls (data : Data) (header n m events : ℕ) :
    (prepared5 data header n m events).1 Reg.one=1 ∧
    (prepared5 data header n m events).1 Reg.occurrences=events := by simp

/-- The full preparation prefix includes five fresh zeroed arrays. Both the
stores and allocation bookkeeping are included in this exact instruction count. -/
theorem prepare_exec {w : ℕ} (data : Data) (header n m events : ℕ)
    (h0 : data.2 0=header) (h1 : data.2 1=n) (h2 : data.2 2=m) (h3 : data.2 3=events)
    (headerLength : 3≤header) (width : Fits w (prepareEnd header n m events)) :
    NaturalData.Exec w prepare data (prepared5 data header n m events)
      (4*(2*(n+1)+2*m+events)+59) := by
  have unit : Fits w 1 := by
    simpa using Allocation.nat_fits_le (a := 1) width (by dsimp [prepareEnd]; omega)
  have a := header_exec data header n m events (prepareEnd header n m events) h0 h1 h2 h3
    (by dsimp [prepareEnd]; omega) width
  have b : NaturalData.Exec w (allocate Reg.seen Reg.atoms) (header10 data header n m events)
      (prepared1 data header n m events) (4*(n+1)+9) := by
    simpa using allocate_exec (header10 data header n m events) Reg.seen Reg.atoms
      (by simpa using Allocation.nat_fits_le (a := header+1+(n+1)) width (by dsimp [prepareEnd]; omega)) unit
  have c : NaturalData.Exec w (allocate Reg.buckets Reg.atoms) (prepared1 data header n m events)
      (prepared2 data header n m events) (4*(n+1)+9) := by
    simpa using allocate_exec (prepared1 data header n m events) Reg.buckets Reg.atoms
      (by simpa using Allocation.nat_fits_le (a := header+1+(n+1)+(n+1)) width (by dsimp [prepareEnd]; omega)) unit
  have d : NaturalData.Exec w (allocate Reg.counters Reg.rules) (prepared2 data header n m events)
      (prepared3 data header n m events) (4*m+9) := by
    simpa using allocate_exec (prepared2 data header n m events) Reg.counters Reg.rules
      (by simpa using Allocation.nat_fits_le (a := header+1+(n+1)+(n+1)+m) width (by dsimp [prepareEnd]; omega)) unit
  have e : NaturalData.Exec w (allocate Reg.links Reg.occurrences) (prepared3 data header n m events)
      (prepared4 data header n m events) (4*events+9) := by
    simpa using allocate_exec (prepared3 data header n m events) Reg.links Reg.occurrences
      (by simpa using Allocation.nat_fits_le (a := header+1+(n+1)+(n+1)+m+events) width (by dsimp [prepareEnd]; omega)) unit
  have f : NaturalData.Exec w (allocate Reg.stack Reg.rules) (prepared4 data header n m events)
      (prepared5 data header n m events) (4*m+9) := by
    simpa using allocate_exec (prepared4 data header n m events) Reg.stack Reg.rules
      (by simpa using Allocation.nat_fits_le (a := header+1+(n+1)+(n+1)+m+events+m) width (by dsimp [prepareEnd]; omega)) unit
  have trace := a.seq (b.seq (c.seq (d.seq (e.seq f))))
  have cost : 14+(4*(n+1)+9+(4*(n+1)+9+(4*m+9+(4*events+9+(4*m+9)))))=
      4*(2*(n+1)+2*m+events)+59 := by omega
  simpa only [prepare,cost] using trace

end LeanTrominoes.Horn.WordRAM
