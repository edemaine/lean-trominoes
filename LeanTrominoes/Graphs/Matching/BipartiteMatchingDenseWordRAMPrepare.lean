/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMSemantics

/-! # Parsing and allocation of the dense matching RAM program -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM
attribute [local simp] Reg.heap Reg.request Reg.allocated Reg.cursor Reg.zero Reg.one
  Reg.n Reg.m Reg.edges Reg.edgeLeft Reg.edgeRight Reg.partnerLeft Reg.partnerRight
  Reg.lengths Reg.rowLeft Reg.rowRight Reg.cells Reg.scratch
  Allocation.frontier Allocation.count Allocation.result Allocation.cursor Allocation.zero Allocation.one

def allocationState (data : Data) (dst length : Fin 64) : Data :=
  ((data.set Reg.request (data.1 length)).allocated (data.1 Reg.heap) (data.1 length)).set dst (data.1 Reg.heap)

theorem allocate_exec {w : Nat} (data : Data) (dst length : Fin 64)
    (width : Fits w (data.1 Reg.heap+data.1 length : Nat)) (unit : Fits w 1) :
    NaturalData.Exec w (allocate dst length) data (allocationState data dst length) (4*data.1 length+9) := by
  have request := NaturalData.copy_exec data Reg.request length (Allocation.nat_fits_le (a := data.1 length) width (by omega))
  have allocated := NaturalData.allocate_exec (r := 58) (data.set Reg.request (data.1 length))
    (data.1 Reg.heap) (data.1 length) (by simp [NaturalData.set]) (by simp [NaturalData.set]) width unit
  have pointer := NaturalData.copy_exec
    ((data.set Reg.request (data.1 length)).allocated (data.1 Reg.heap) (data.1 length)) dst Reg.allocated
    (by simpa [NaturalData.allocated,NaturalData.allocatedRegisters] using
      Allocation.nat_fits_le width (show data.1 Reg.heap≤data.1 Reg.heap+data.1 length by omega))
  have result : ((data.set Reg.request (data.1 length)).allocated (data.1 Reg.heap) (data.1 length)).1 Reg.allocated=data.1 Reg.heap := by
    simp [NaturalData.allocated,NaturalData.allocatedRegisters]
  have cost : 1+(4*data.1 length+7+1)=4*data.1 length+9 := by omega
  simpa only [allocate,copy,allocationState,result,cost] using request.seq (allocated.seq pointer)

def header0 (data : Data) (H : Nat) := data.initialized H
def header1 (data : Data) (H : Nat) := (header0 data H).set Reg.cursor 1
def header2 (data : Data) (H n : Nat) := (header1 data H).set Reg.n n
def header3 (data : Data) (H n : Nat) := (header2 data H n).set Reg.cursor 2
def header4 (data : Data) (H n m : Nat) := (header3 data H n).set Reg.m m
def header5 (data : Data) (H n m : Nat) := (header4 data H n m).set Reg.cursor 3
def header6 (data : Data) (H n m E : Nat) := (header5 data H n m).set Reg.edges E
def header7 (data : Data) (H n m E : Nat) := (header6 data H n m E).set Reg.edgeLeft 4
def header8 (data : Data) (H n m E : Nat) := (header7 data H n m E).set Reg.edgeRight (4+E)
def header9 (data : Data) (H n m E : Nat) := (header8 data H n m E).set Reg.cells (n*n)

attribute [local simp] header0 header1 header2 header3 header4 header5 header6 header7 header8 header9
  NaturalData.initialized NaturalData.set

theorem header_exec {w : Nat} (data : Data) (H n m E B : Nat)
    (h0 : data.2 0=H) (h1 : data.2 1=n) (h2 : data.2 2=m) (h3 : data.2 3=E)
    (room : H+1≤B ∧ n≤B ∧ m≤B ∧ E≤B ∧ 4+E≤B ∧ n*n≤B) (width : Fits w B) :
    NaturalData.Exec w header data (header9 data H n m E) 13 := by
  have unit : Fits w 1 := by simpa using Allocation.nat_fits_le (a := 1) width (by omega)
  have a := NaturalData.initialize_exec (r := 58) data H h0 (Allocation.nat_fits_le width room.1) unit
  have b := Natural.Exec.atom (Natural.Step.constant (header0 data H) Reg.cursor 1 (show 1≤B by omega))
  have c : Natural.Exec B (.atom (.load Reg.n Reg.cursor)) (header1 data H) (header2 data H n) 1 := by
    simpa [h1] using Natural.Exec.atom (Natural.Step.load (bound := B) (header1 data H) Reg.n Reg.cursor (by simp; omega) (by simp [h1]; omega))
  have d : Natural.Exec B (increment Reg.cursor) (header2 data H n) (header3 data H n) 1 := by
    simpa [increment,add] using Natural.Exec.atom (Natural.Step.add (bound := B) (header2 data H n) Reg.cursor Reg.cursor Reg.one (by simp; omega))
  have e : Natural.Exec B (.atom (.load Reg.m Reg.cursor)) (header3 data H n) (header4 data H n m) 1 := by
    simpa [h2] using Natural.Exec.atom (Natural.Step.load (bound := B) (header3 data H n) Reg.m Reg.cursor (by simp; omega) (by simp [h2]; omega))
  have f : Natural.Exec B (increment Reg.cursor) (header4 data H n m) (header5 data H n m) 1 := by
    simpa [increment,add] using Natural.Exec.atom (Natural.Step.add (bound := B) (header4 data H n m) Reg.cursor Reg.cursor Reg.one (by simp; omega))
  have g : Natural.Exec B (.atom (.load Reg.edges Reg.cursor)) (header5 data H n m) (header6 data H n m E) 1 := by
    simpa [h3] using Natural.Exec.atom (Natural.Step.load (bound := B) (header5 data H n m) Reg.edges Reg.cursor (by simp; omega) (by simp [h3]; omega))
  have h := Natural.Exec.atom (Natural.Step.constant (header6 data H n m E) Reg.edgeLeft 4 (show 4≤B by omega))
  have i : Natural.Exec B (add Reg.edgeRight Reg.edgeLeft Reg.edges) (header7 data H n m E) (header8 data H n m E) 1 := by
    simpa [add] using Natural.Exec.atom (Natural.Step.add (bound := B) (header7 data H n m E) Reg.edgeRight Reg.edgeLeft Reg.edges (by simp; omega))
  have j : Natural.Exec B (mul Reg.cells Reg.n Reg.n) (header8 data H n m E) (header9 data H n m E) 1 := by
    simpa [mul] using Natural.Exec.atom (Natural.Step.mul (bound := B) (header8 data H n m E) Reg.cells Reg.n Reg.n (by simp; omega))
  have rest := b.seq (c.seq (d.seq (e.seq (f.seq (g.seq (h.seq (i.seq j)))))))
  have trace := a.seq (rest.compiles width)
  simpa only [header,constant,Nat.reduceAdd] using trace

def prepared1 (data : Data) (H n m E : Nat) := allocationState (header9 data H n m E) Reg.partnerLeft Reg.n
def prepared2 (data : Data) (H n m E : Nat) := allocationState (prepared1 data H n m E) Reg.partnerRight Reg.m
def prepared3 (data : Data) (H n m E : Nat) := allocationState (prepared2 data H n m E) Reg.lengths Reg.n
def prepared4 (data : Data) (H n m E : Nat) := allocationState (prepared3 data H n m E) Reg.rowLeft Reg.cells
def prepared5 (data : Data) (H n m E : Nat) := allocationState (prepared4 data H n m E) Reg.rowRight Reg.cells

def prepareEnd (H n m : Nat) := H+1+2*n+m+2*(n*n)
attribute [local simp] prepared1 prepared2 prepared3 prepared4 prepared5 allocationState
  NaturalData.allocated NaturalData.allocatedRegisters

theorem prepare_exec {w : Nat} (data : Data) (H n m E : Nat)
    (h0 : data.2 0=H) (h1 : data.2 1=n) (h2 : data.2 2=m) (h3 : data.2 3=E)
    (headerLength : 3+2*E≤H) (width : Fits w (prepareEnd H n m)) :
    NaturalData.Exec w prepare data (prepared5 data H n m E) (4*(2*n+m+2*(n*n))+58) := by
  have unit : Fits w 1 := Allocation.nat_fits_le width (by dsimp [prepareEnd]; omega)
  have a := header_exec data H n m E (prepareEnd H n m) h0 h1 h2 h3 (by dsimp [prepareEnd]; omega) width
  have b : NaturalData.Exec w (allocate Reg.partnerLeft Reg.n) (header9 data H n m E)
      (prepared1 data H n m E) (4*n+9) := by
    simpa using allocate_exec (header9 data H n m E) Reg.partnerLeft Reg.n
      (by simpa using Allocation.nat_fits_le (a := H+1+n) width (by dsimp [prepareEnd]; omega)) unit
  have c : NaturalData.Exec w (allocate Reg.partnerRight Reg.m) (prepared1 data H n m E)
      (prepared2 data H n m E) (4*m+9) := by
    simpa using allocate_exec (prepared1 data H n m E) Reg.partnerRight Reg.m
      (by simpa using Allocation.nat_fits_le (a := H+1+n+m) width (by dsimp [prepareEnd]; omega)) unit
  have d : NaturalData.Exec w (allocate Reg.lengths Reg.n) (prepared2 data H n m E)
      (prepared3 data H n m E) (4*n+9) := by
    simpa using allocate_exec (prepared2 data H n m E) Reg.lengths Reg.n
      (by simpa using Allocation.nat_fits_le (a := H+1+n+m+n) width (by dsimp [prepareEnd]; omega)) unit
  have e : NaturalData.Exec w (allocate Reg.rowLeft Reg.cells) (prepared3 data H n m E)
      (prepared4 data H n m E) (4*(n*n)+9) := by
    simpa using allocate_exec (prepared3 data H n m E) Reg.rowLeft Reg.cells
      (by simpa using Allocation.nat_fits_le (a := H+1+n+m+n+n*n) width (by dsimp [prepareEnd]; omega)) unit
  have f : NaturalData.Exec w (allocate Reg.rowRight Reg.cells) (prepared4 data H n m E)
      (prepared5 data H n m E) (4*(n*n)+9) := by
    simpa using allocate_exec (prepared4 data H n m E) Reg.rowRight Reg.cells
      (by simpa [prepareEnd,two_mul,add_assoc,add_left_comm,add_comm] using width) unit
  have cost : 13+(4*n+9+(4*m+9+(4*n+9+(4*(n*n)+9+(4*(n*n)+9)))))=4*(2*n+m+2*(n*n))+58 := by omega
  simpa only [prepare,cost] using a.seq (b.seq (c.seq (d.seq (e.seq f))))

theorem allocationState_bounded {B : Nat} {data : Data} (dst length : Fin 64)
    (before : NaturalData.Bounded B data) (endpoint : data.1 Reg.heap+data.1 length≤B) (unit : 1≤B) :
    NaturalData.Bounded B (allocationState data dst length) :=
  (NaturalData.allocated_bounded (r := 58) (initial := before.set Reg.request (before.1 length)) endpoint unit).set dst (before.1 Reg.heap)

theorem header9_bounded {B : Nat} (data : Data) (H n m E : Nat)
    (before : NaturalData.Bounded B data)
    (room : H+1≤B ∧ n≤B ∧ m≤B ∧ E≤B ∧ 4+E≤B ∧ n*n≤B) :
    NaturalData.Bounded B (header9 data H n m E) := by
  have a : NaturalData.Bounded B (header0 data H) :=
    ((before.set Reg.zero (by omega)).set Reg.one (by omega)).set Reg.heap room.1
  have b : NaturalData.Bounded B (header1 data H) := a.set Reg.cursor (by omega)
  have c : NaturalData.Bounded B (header2 data H n) := b.set Reg.n (by omega)
  have d : NaturalData.Bounded B (header3 data H n) := c.set Reg.cursor (by omega)
  have e : NaturalData.Bounded B (header4 data H n m) := d.set Reg.m (by omega)
  have f : NaturalData.Bounded B (header5 data H n m) := e.set Reg.cursor (by omega)
  have g : NaturalData.Bounded B (header6 data H n m E) := f.set Reg.edges (by omega)
  have h : NaturalData.Bounded B (header7 data H n m E) := g.set Reg.edgeLeft (by omega)
  have i : NaturalData.Bounded B (header8 data H n m E) := h.set Reg.edgeRight (by omega)
  exact i.set Reg.cells (by omega)

theorem prepared5_bounded (data : Data) (H n m E : Nat) (headerLength : 3+2*E≤H)
    (before : NaturalData.Bounded (prepareEnd H n m) data) :
    NaturalData.Bounded (prepareEnd H n m) (prepared5 data H n m E) := by
  have unit : 1≤prepareEnd H n m := by dsimp [prepareEnd]; omega
  have a := header9_bounded data H n m E before (by dsimp [prepareEnd]; omega)
  have b : NaturalData.Bounded (prepareEnd H n m) (prepared1 data H n m E) :=
    allocationState_bounded _ _ a (by simp; dsimp [prepareEnd]; omega) unit
  have c : NaturalData.Bounded (prepareEnd H n m) (prepared2 data H n m E) :=
    allocationState_bounded _ _ b (by simp; dsimp [prepareEnd]; omega) unit
  have d : NaturalData.Bounded (prepareEnd H n m) (prepared3 data H n m E) :=
    allocationState_bounded _ _ c (by simp; dsimp [prepareEnd]; omega) unit
  have e : NaturalData.Bounded (prepareEnd H n m) (prepared4 data H n m E) :=
    allocationState_bounded _ _ d (by simp; dsimp [prepareEnd]; omega) unit
  exact allocationState_bounded _ _ e (by simp; dsimp [prepareEnd]; omega) unit

end LeanTrominoes.BipartiteMatching.DenseWordRAM
