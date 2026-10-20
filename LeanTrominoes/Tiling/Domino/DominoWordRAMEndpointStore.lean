/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMEndpointIndices

/-! # Actual stores to the original endpoint table format -/
namespace LeanTrominoes.Domino.WordRAM.EndpointWriter
open ComplexityAbstract.RAM

def write1 (data : Data) := data.set R.storeAddress (data.1 H.left+data.1 H.index)
def write2 (data : Data) (source : Fin 128) := (write1 data).store (data.1 H.left+data.1 H.index) (data.1 source)
def write3 (data : Data) (source : Fin 128) := (write2 data source).set R.storeAddress (data.1 H.right+data.1 H.index)
def write4 (data : Data) (source target : Fin 128) := (write3 data source).store (data.1 H.right+data.1 H.index) (data.1 target)
def writeState (data : Data) (source target : Fin 128) := (write4 data source target).set H.index (data.1 H.index+data.1 R.one)

def writeMemory (memory : Nat → Nat) (left right index source target : Nat) : Nat → Nat :=
  Function.update (Function.update memory (left+index) source) (right+index) target

attribute [local simp] add H.left H.right H.index R.one R.storeAddress
  write1 write2 write3 write4 writeState NaturalData.set NaturalData.store

theorem writePair_exec {B : Nat} (data : Data) (source target : Fin 128)
    (sourceSafe : source≠R.storeAddress) (targetSafe : target≠R.storeAddress)
    (left : data.1 H.left+data.1 H.index≤B) (right : data.1 H.right+data.1 H.index≤B)
    (sourceBound : data.1 source≤B) (targetBound : data.1 target≤B)
    (cursor : data.1 H.index+data.1 R.one≤B) :
    Natural.Exec B (writePair source target) data (writeState data source target) 5 := by
  have first : Natural.Exec B (add R.storeAddress H.left H.index) data (write1 data) 1 := Natural.Exec.atom (Natural.Step.add _ _ _ _ left)
  have second : Natural.Exec B (.atom (.store R.storeAddress source)) (write1 data) (write2 data source) 1 := by
    simpa [sourceSafe] using Natural.Exec.atom (Natural.Step.store (bound:=B) (write1 data) R.storeAddress source
      (by simpa using left) (by simpa [sourceSafe] using sourceBound))
  have third : Natural.Exec B (add R.storeAddress H.right H.index) (write2 data source) (write3 data source) 1 := by
    simpa using Natural.Exec.atom (Natural.Step.add (bound:=B) (write2 data source) R.storeAddress H.right H.index (by simpa using right))
  have fourth : Natural.Exec B (.atom (.store R.storeAddress target)) (write3 data source) (write4 data source target) 1 := by
    simpa [targetSafe] using Natural.Exec.atom (Natural.Step.store (bound:=B) (write3 data source) R.storeAddress target
      (by simpa using right) (by simpa [targetSafe] using targetBound))
  have fifth : Natural.Exec B (add H.index H.index R.one) (write4 data source target) (writeState data source target) 1 := by
    simpa using Natural.Exec.atom (Natural.Step.add (bound:=B) (write4 data source target) H.index H.index R.one (by simpa using cursor))
  simpa only [writePair,Nat.reduceAdd] using first.seq (second.seq (third.seq (fourth.seq fifth)))

theorem writeState_memory (data : Data) (source target : Fin 128) :
    (writeState data source target).2=writeMemory data.2 (data.1 H.left) (data.1 H.right) (data.1 H.index) (data.1 source) (data.1 target) := rfl

theorem writeState_index (data : Data) (source target : Fin 128) :
    (writeState data source target).1 H.index=data.1 H.index+data.1 R.one := by simp

theorem writeState_fixed (data : Data) (source target reg : Fin 128)
    (different : reg≠R.storeAddress ∧ reg≠H.index) : (writeState data source target).1 reg=data.1 reg := by
  simp only [writeState,write4,write3,write2,write1,NaturalData.set,NaturalData.store,
    Function.update_of_ne different.1,Function.update_of_ne different.2]

end LeanTrominoes.Domino.WordRAM.EndpointWriter
