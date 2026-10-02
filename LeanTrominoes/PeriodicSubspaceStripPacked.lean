/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicSubspaceStripCompletionWindow
import LeanTrominoes.PeriodicCNFLinePacked
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Binary words for arbitrary finite-footprint strip windows -/
namespace LeanTrominoes.PeriodicSubspaceTiling.Strip

def bits (input : Data) (bound : Nat) : Nat := (2*bound+1)*input.2.length

def decodeWord (input : Data) (bound word : Nat) : Window input bound :=
  fun c i => word.testBit (i.val+input.2.length*c.val)

def encodeWindow (input : Data) (bound : Nat) (w : Window input bound) : Nat :=
  (BitVec.ofBoolListLE (List.ofFn fun i : Fin (bits input bound) =>
    let ci := (finProdFinEquiv (m := 2*bound+1) (n := input.2.length)).symm i
    w ci.1 ci.2)).toNat

theorem decodeWord_encodeWindow (input : Data) (bound : Nat) (w : Window input bound) :
    decodeWord input bound (encodeWindow input bound w)=w := by
  funext c i
  let index := finProdFinEquiv (c,i)
  have small : i.val+input.2.length*c.val < bits input bound := index.isLt
  simp only [decodeWord,encodeWindow,BitVec.testBit_toNat,BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD,List.getElem?_ofFn,small,dif_pos,Option.getD_some]
  change w ((finProdFinEquiv.symm index).1) ((finProdFinEquiv.symm index).2) = w c i
  rw [Equiv.symm_apply_apply]

theorem encodeWindow_lt (input : Data) (bound : Nat) (w : Window input bound) :
    encodeWindow input bound w < 2^bits input bound := by
  simpa only [encodeWindow,List.length_ofFn] using (BitVec.ofBoolListLE (List.ofFn fun i : Fin (bits input bound) =>
    let ci := (finProdFinEquiv (m := 2*bound+1) (n := input.2.length)).symm i
    w ci.1 ci.2)).isLt

def packedTransition (input : Data) (bound a b : Nat) : Prop :=
  LocalWindow.Transition (Valid input bound) (decodeWord input bound a) (decodeWord input bound b)

instance (input : Data) (bound : Nat) (w : Window input bound) : Decidable (Valid input bound w) := by
  unfold Valid ExistsUnique
  simp only [and_assoc,and_imp]
  infer_instance

instance (input : Data) (bound a b : Nat) : Decidable (packedTransition input bound a b) := by
  unfold packedTransition LocalWindow.Transition
  infer_instance

theorem packed_cycle_iff (input : Data) (bound : Nat) :
    FiniteState.HasCycle (fun a b : Fin (2^bits input bound) => packedTransition input bound a b) ↔
      FiniteState.HasCycle (LocalWindow.Transition (Valid input bound)) := by
  constructor
  · rintro ⟨period,states,step⟩
    exact ⟨period,fun i => decodeWord input bound (states i),step⟩
  · rintro ⟨period,states,step⟩
    refine ⟨period,fun i => ⟨encodeWindow input bound (states i),encodeWindow_lt input bound _⟩,?_⟩
    intro i
    simpa only [packedTransition,decodeWord_encodeWindow] using step i

def packedCompletionTransition (data : CompletionData) (bound a b : Nat) : Prop :=
  LocalWindow.Transition (CompletionValid data bound) (decodeWord data.1 bound a) (decodeWord data.1 bound b)

instance (data : CompletionData) (bound : Nat) (w : Window data.1 bound) :
    Decidable (CompletionValid data bound w) := by
  unfold CompletionValid
  infer_instance

instance (data : CompletionData) (bound a b : Nat) :
    Decidable (packedCompletionTransition data bound a b) := by
  unfold packedCompletionTransition LocalWindow.Transition
  infer_instance

theorem packed_completion_cycle_iff (data : CompletionData) (bound : Nat) :
    FiniteState.HasCycle (fun a b : Fin (2^bits data.1 bound) => packedCompletionTransition data bound a b) ↔
      FiniteState.HasCycle (LocalWindow.Transition (CompletionValid data bound)) := by
  constructor
  · rintro ⟨period,states,step⟩
    exact ⟨period,fun i => decodeWord data.1 bound (states i),step⟩
  · rintro ⟨period,states,step⟩
    refine ⟨period,fun i => ⟨encodeWindow data.1 bound (states i),encodeWindow_lt data.1 bound _⟩,?_⟩
    intro i
    simpa only [packedCompletionTransition,decodeWord_encodeWindow] using step i

end LeanTrominoes.PeriodicSubspaceTiling.Strip
