/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMEndpointFooter

/-! # Exact bounded-word execution of one padded graph candidate

The program reads the computed coordinate parities, constructs both lifted
endpoint indices and writes the forward and reverse pair. Failed candidates
write the dummy pair twice. Every instruction, including address arithmetic,
is counted. The arithmetic probe's first64 registers are preserved.
-/
namespace LeanTrominoes.Domino.WordRAM.EndpointWriter
open ComplexityAbstract.RAM

def emittedWords {d : Nat} (phase : PeriodicLatticeGraph.DoubleCover.Phase d) (bits : Fin d → Nat)
    (n u v active : Nat) : List (Nat × Nat) :=
  let source := if active=0 then n*2^d else (finFunctionFinEquiv phase).val+2^d*u
  let target := if active=0 then n*2^d else phaseValue phase bits+2^d*v
  [(source,target),(target,source)]

structure Output (words : List (Nat × Nat)) (before after : Data) : Prop where
  memory : after.2=appendMemory before.2 (before.1 H.left) (before.1 H.right) (before.1 H.index) words
  index : after.1 H.index=before.1 H.index+words.length
  fixed : ∀ reg : Fin 128, reg.val<96 → reg≠H.index → after.1 reg=before.1 reg

structure Bounds (B d n : Nat) (data : Data) : Prop where
  small : 2≤B
  dimension : d≤B
  parities : data.1 H.parities+d≤B
  capacity : 2^d≤B
  vertices : n*2^d≤B
  left : data.1 H.left+data.1 H.index+1≤B
  right : data.1 H.right+data.1 H.index+1≤B
  cursor : data.1 H.index+2≤B

theorem program_exec {B n d : Nat} (phase : PeriodicLatticeGraph.DoubleCover.Phase d) (bits : Fin d → Nat)
    (data : Data) (u v : Fin n) (bounds : Bounds B d n data)
    (uInput : data.1 H.u=u.val) (vInput : data.1 H.v=v.val) (nInput : data.1 H.n=n)
    (bitBound : ∀ i, bits i≤1) (known : ∀ i, data.2 (data.1 H.parities+i.val)=bits i) :
    ∃ result, Natural.Exec B (program phase) data result (9*d+25) ∧
      Output (emittedWords phase bits n u.val v.val (data.1 H.active)) data result := by
  have sourceBound : 2^d*u.val+(finFunctionFinEquiv phase).val≤B := by
    have grow := Nat.mul_le_mul_left (2^d) (show u.val+1≤n by have := u.isLt; omega)
    have phaseBound := (finFunctionFinEquiv phase).isLt
    exact (show 2^d*u.val+(finFunctionFinEquiv phase).val≤n*2^d by nlinarith).trans bounds.vertices
  have targetBound : 2^d*v.val+phaseValue phase bits≤B := by
    have grow := Nat.mul_le_mul_left (2^d) (show v.val+1≤n by have := v.isLt; omega)
    have phaseBound := phaseValue_lt phase bits
    exact (show 2^d*v.val+phaseValue phase bits≤n*2^d by nlinarith).trans bounds.vertices
  obtain ⟨phased,xorRun,xorCorrect⟩ := xor_exec phase bits data bounds.small bounds.dimension bounds.parities bounds.capacity bitBound known
  have phasedFixed (reg : Fin 128) (low : reg.val<96) : phased.1 reg=data.1 reg := xorCorrect.fixed reg (Or.inl low)
  have endpointsRun := endpoints_exec phase phased bounds.capacity
    (by rw [phasedFixed H.u (by decide),uInput]; exact sourceBound)
    (by rw [phasedFixed H.v (by decide),vInput,xorCorrect.phase]; exact targetBound)
    (by rw [phasedFixed H.n (by decide),nInput]; exact bounds.vertices)
  let ready := endpointState phased d (finFunctionFinEquiv phase).val
  have readyFixed (reg : Fin 128) (low : reg.val<96) : ready.1 reg=data.1 reg :=
    (endpointState_fixed phased d (finFunctionFinEquiv phase).val reg (Or.inl (by omega))).trans (phasedFixed reg low)
  have values := endpointState_values phased d (finFunctionFinEquiv phase).val
  have sourceValue : ready.1 R.source=2^d*u.val+(finFunctionFinEquiv phase).val := by
    rw [values.1,phasedFixed H.u (by decide),uInput]
  have targetValue : ready.1 R.target=2^d*v.val+phaseValue phase bits := by
    rw [values.2.1,phasedFixed H.v (by decide),vInput,xorCorrect.phase]
  have dummyValue : ready.1 R.dummy=n*2^d := by rw [values.2.2.1,phasedFixed H.n (by decide),nInput]
  have scratchValue : ready.1 R.constant=(finFunctionFinEquiv phase).val := values.2.2.2
  have readyOne : ready.1 R.one=1 := (endpointState_fixed phased d (finFunctionFinEquiv phase).val R.one (by decide)).trans xorCorrect.one
  obtain ⟨result,footerRun,footerCorrect⟩ := footer_exec ready readyOne
    (sourceValue ▸ sourceBound) (targetValue ▸ targetBound) (dummyValue ▸ bounds.vertices)
    (by rw [scratchValue]; exact (finFunctionFinEquiv phase).isLt.le.trans bounds.capacity)
    (by rw [readyFixed H.left (by decide),readyFixed H.index (by decide)]; exact bounds.left)
    (by rw [readyFixed H.right (by decide),readyFixed H.index (by decide)]; exact bounds.right)
    (by rw [readyFixed H.index (by decide)]; exact bounds.cursor)
  have words : selectedWords ready=emittedWords phase bits n u.val v.val (data.1 H.active) := by
    simp only [selectedWords,selectedSource,selectedTarget,emittedWords,sourceValue,targetValue,dummyValue,readyFixed H.active (by decide)]
    simp only [Nat.add_comm]
  have trace := xorRun.seq (endpointsRun.seq footerRun)
  refine ⟨result,?_,?_,?_,?_⟩
  · change Natural.Exec B (program phase) data result ((9*d+4)+(7+14)) at trace
    exact trace
  · simpa only [words,readyFixed H.left (by decide),readyFixed H.right (by decide),readyFixed H.index (by decide),
      ready,endpointState_memory,xorCorrect.memory] using footerCorrect.memory
  · rw [footerCorrect.index,readyFixed H.index (by decide)]
    simp [emittedWords]
  · intro reg low different
    exact (footerCorrect.fixed reg low different).trans (readyFixed reg low)

theorem emittedWords_candidate {n d : Nat} (B : BasisData n d) (u : Fin n) (direction : Fin d) (v : Fin n)
    (phase : PeriodicLatticeGraph.DoubleCover.Phase d) (bits : Fin d → Nat) (active : Nat)
    (valid : active≠0 ↔ PaddedGraph.Active B u direction v)
    (parities : PaddedGraph.Active B u direction v → ∀ i,
      bits i=(PaddedGraph.coordinates B u direction v i%2).toNat) :
    emittedWords phase bits n u.val v.val active=candidateWords B (u,direction,v,phase) := by
  rw [candidateWords_eq B u direction v phase bits parities]
  by_cases zero : active=0
  · have inactive : ¬PaddedGraph.Active B u direction v := by intro h; exact valid.mpr h zero
    simp [emittedWords,zero,inactive]
  · simp [emittedWords,zero,valid.mp zero]

end LeanTrominoes.Domino.WordRAM.EndpointWriter
