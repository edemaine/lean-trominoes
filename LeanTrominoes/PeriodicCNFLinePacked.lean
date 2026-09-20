/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFLineSearch
import Mathlib.Data.BitVec

/-! # Binary state words for the one-dimensional CNF checker -/
namespace LeanTrominoes.PeriodicCNF.LineWindow
variable {V : Type} [DecidableEq V]

def keys (f : PeriodicCNF V) : List (Fin 3 × Fin f.variableOccurrences.length) :=
  (List.finRange 3).flatMap fun c => (List.finRange f.variableOccurrences.length).map (c,·)

omit [DecidableEq V] in
theorem mem_keys (f : PeriodicCNF V) (a : Fin 3 × Fin f.variableOccurrences.length) : a ∈ keys f := by
  simp only [keys,List.mem_flatMap,List.mem_finRange,true_and,List.mem_map]
  exact ⟨a.1,a.2,rfl⟩

omit [DecidableEq V] in
theorem keys_length (f : PeriodicCNF V) : (keys f).length = 3*f.variableOccurrences.length := by
  simp [keys,List.length_flatMap]
  omega

def decodeWord (f : PeriodicCNF V) (word : Nat) : Window f :=
  fun c i => word.testBit ((keys f).idxOf (c,i))

def encodeWindow (f : PeriodicCNF V) (w : Window f) : Nat :=
  (BitVec.ofBoolListLE ((keys f).map fun a => w a.1 a.2)).toNat

omit [DecidableEq V] in
theorem decodeWord_encodeWindow (f : PeriodicCNF V) (w : Window f) :
    decodeWord f (encodeWindow f w) = w := by
  funext c i
  simp only [decodeWord,encodeWindow,BitVec.testBit_toNat,BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_idxOf (mem_keys f (c,i))]
  rfl

omit [DecidableEq V] in
theorem encodeWindow_lt (f : PeriodicCNF V) (w : Window f) :
    encodeWindow f w < 2^(3*f.variableOccurrences.length) := by
  have bound := (BitVec.ofBoolListLE ((keys f).map fun a => w a.1 a.2)).isLt
  simpa [encodeWindow,keys_length] using bound

def packedTransition (f : PeriodicCNF V) (first second : Nat) : Prop :=
  LocalWindow.Transition (Valid f) (decodeWord f first) (decodeWord f second)

instance (f : PeriodicCNF V) : DecidableRel (packedTransition f) := by
  intro a b
  unfold packedTransition
  infer_instance

abbrev PackedState (f : PeriodicCNF V) := Fin (2^(3*f.variableOccurrences.length))

theorem packed_cycle_iff (f : PeriodicCNF V) :
    FiniteState.HasCycle (fun a b : PackedState f => packedTransition f a.val b.val) ↔
      FiniteState.HasCycle (LocalWindow.Transition (Valid f)) := by
  constructor
  · rintro ⟨period,states,step⟩
    exact ⟨period,fun i => decodeWord f (states i).val,step⟩
  · rintro ⟨period,states,step⟩
    refine ⟨period,fun i => ⟨encodeWindow f (states i),encodeWindow_lt f (states i)⟩,?_⟩
    intro i
    simpa only [packedTransition,decodeWord_encodeWindow] using step i

theorem satisfiable_iff_packed_cycle (f : PeriodicCNF V)
    (horizontal : f.IsOneDimensional) (locality : f.IsLocalOnLine) :
    f.Satisfiable ↔ FiniteState.HasCycle
      (fun a b : PackedState f => packedTransition f a.val b.val) :=
  (satisfiable_iff_cycle f horizontal locality).trans (packed_cycle_iff f).symm

end LeanTrominoes.PeriodicCNF.LineWindow
