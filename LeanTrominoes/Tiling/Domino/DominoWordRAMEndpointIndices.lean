/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMEndpointXor

/-! # Seven ordinary instructions compute the two lifted vertex indices -/
namespace LeanTrominoes.Domino.WordRAM.EndpointWriter
open ComplexityAbstract.RAM

def endpoint1 (data : Data) (d : Nat) := data.set R.capacity (2^d)
def endpoint2 (data : Data) (d : Nat) := (endpoint1 data d).set R.source (2^d*data.1 H.u)
def endpoint3 (data : Data) (d phase : Nat) := (endpoint2 data d).set R.constant phase
def endpoint4 (data : Data) (d phase : Nat) := (endpoint3 data d phase).set R.source (2^d*data.1 H.u+phase)
def endpoint5 (data : Data) (d phase : Nat) := (endpoint4 data d phase).set R.target (2^d*data.1 H.v)
def endpoint6 (data : Data) (d phase : Nat) := (endpoint5 data d phase).set R.target (2^d*data.1 H.v+data.1 R.phase)
def endpointState (data : Data) (d phase : Nat) := (endpoint6 data d phase).set R.dummy (data.1 H.n*2^d)

attribute [local simp] constant add mul copy H.u H.v H.n R.phase R.source R.target R.capacity R.dummy R.constant
  endpoint1 endpoint2 endpoint3 endpoint4 endpoint5 endpoint6 endpointState NaturalData.set

theorem endpoints_exec {B d : Nat} (phase : PeriodicLatticeGraph.DoubleCover.Phase d) (data : Data)
    (capacity : 2^d≤B) (source : 2^d*data.1 H.u+(finFunctionFinEquiv phase).val≤B)
    (target : 2^d*data.1 H.v+data.1 R.phase≤B) (dummy : data.1 H.n*2^d≤B) :
    Natural.Exec B (endpoints phase) data (endpointState data d (finFunctionFinEquiv phase).val) 7 := by
  dsimp only [H.u,H.v,H.n,R.phase] at *
  have phaseBound : (finFunctionFinEquiv phase).val≤B := (finFunctionFinEquiv phase).isLt.le.trans capacity
  have first := Natural.Exec.atom (Natural.Step.constant data R.capacity (2^d) capacity)
  have second : Natural.Exec B (mul R.source R.capacity H.u) (endpoint1 data d) (endpoint2 data d) 1 := by
    simpa using Natural.Exec.atom (Natural.Step.mul (bound:=B) (endpoint1 data d) R.source R.capacity H.u (by simp; omega))
  have third := Natural.Exec.atom (Natural.Step.constant (endpoint2 data d) R.constant (finFunctionFinEquiv phase).val phaseBound)
  have fourth : Natural.Exec B (add R.source R.source R.constant) (endpoint3 data d (finFunctionFinEquiv phase).val)
      (endpoint4 data d (finFunctionFinEquiv phase).val) 1 := by
    simpa using Natural.Exec.atom (Natural.Step.add (bound:=B) (endpoint3 data d (finFunctionFinEquiv phase).val) R.source R.source R.constant (by simpa using source))
  have fifth : Natural.Exec B (mul R.target R.capacity H.v) (endpoint4 data d (finFunctionFinEquiv phase).val)
      (endpoint5 data d (finFunctionFinEquiv phase).val) 1 := by
    simpa using Natural.Exec.atom (Natural.Step.mul (bound:=B) (endpoint4 data d (finFunctionFinEquiv phase).val) R.target R.capacity H.v (by simp; omega))
  have sixth : Natural.Exec B (add R.target R.target R.phase) (endpoint5 data d (finFunctionFinEquiv phase).val)
      (endpoint6 data d (finFunctionFinEquiv phase).val) 1 := by
    simpa using Natural.Exec.atom (Natural.Step.add (bound:=B) (endpoint5 data d (finFunctionFinEquiv phase).val) R.target R.target R.phase (by simpa using target))
  have seventh : Natural.Exec B (mul R.dummy H.n R.capacity) (endpoint6 data d (finFunctionFinEquiv phase).val)
      (endpointState data d (finFunctionFinEquiv phase).val) 1 := by
    simpa using Natural.Exec.atom (Natural.Step.mul (bound:=B) (endpoint6 data d (finFunctionFinEquiv phase).val) R.dummy H.n R.capacity (by simpa using dummy))
  simpa only [endpoints,constant,Nat.reduceAdd] using first.seq (second.seq (third.seq (fourth.seq (fifth.seq (sixth.seq seventh)))))

theorem endpointState_memory (data : Data) (d phase : Nat) : (endpointState data d phase).2=data.2 := rfl

theorem endpointState_values (data : Data) (d phase : Nat) :
    (endpointState data d phase).1 R.source=2^d*data.1 H.u+phase ∧
    (endpointState data d phase).1 R.target=2^d*data.1 H.v+data.1 R.phase ∧
    (endpointState data d phase).1 R.dummy=data.1 H.n*2^d ∧
    (endpointState data d phase).1 R.constant=phase := by simp

theorem endpointState_fixed (data : Data) (d phase : Nat) (reg : Fin 128)
    (outside : reg.val<106 ∨ 111<reg.val) : (endpointState data d phase).1 reg=data.1 reg := by
  have different (dst : Fin 128) (lower : 106≤dst.val) (upper : dst.val≤111) : reg≠dst := by
    intro same; have equal := congrArg Fin.val same; omega
  simp only [endpointState,endpoint6,endpoint5,endpoint4,endpoint3,endpoint2,endpoint1,NaturalData.set]
  simp only [Function.update_of_ne (different R.source (by decide) (by decide)),
    Function.update_of_ne (different R.target (by decide) (by decide)),
    Function.update_of_ne (different R.dummy (by decide) (by decide)),
    Function.update_of_ne (different R.constant (by decide) (by decide)),
    Function.update_of_ne (different R.capacity (by decide) (by decide))]

end LeanTrominoes.Domino.WordRAM.EndpointWriter
