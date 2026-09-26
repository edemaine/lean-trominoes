/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMLineDecision
import LeanTrominoes.LocalWindowCycle
import Mathlib.Data.BitVec
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Three-column matching windows for local horizontal periodic 3DM -/
namespace LeanTrominoes.PeriodicThreeDM.LineWindow
open Gadget
abbrev Column (p : PeriodicThreeDM) := Fin p.triples.length → Bool
abbrev Window (p : PeriodicThreeDM) := LocalWindow.Window (Column p) 2

def value (p : PeriodicThreeDM) (index : Nat) (column : Column p) : Bool :=
  if h : index < p.triples.length then column ⟨index,h⟩ else false

def position (i : Incidence) : Fin 3 := ⟨(1-i.offset.1).toNat%3,Nat.mod_lt _ (by decide)⟩

def Valid (p : PeriodicThreeDM) (w : Window p) : Prop :=
  ∀ color atom, atom < p.elementCount color → PeriodicOneInThree.ExactlyOne
    ((p.incidences color atom).map fun i => value p i.tripleIndex (w (position i)))

theorem position_eq (p : PeriodicThreeDM) (locality : p.IsLocal) (color : WireColor) (atom : Nat)
    {i : Incidence} (hi : i ∈ p.incidences color atom) : (position i).val = (1:Int)-i.offset.1 := by
  have small := incidence_offset_local locality color atom hi
  have nonneg : 0 ≤ 1-i.offset.1 := by omega
  have bound : (1-i.offset.1).toNat < 3 := by omega
  simp only [position,Nat.mod_eq_of_lt bound,Int.toNat_of_nonneg nonneg]

theorem satisfiable_iff (p : PeriodicThreeDM) (horizontal : p.IsOneDimensional) (locality : p.IsLocal) :
    p.Satisfiable ↔ LocalWindow.Satisfiable 2 (Valid p) := by
  constructor
  · rintro ⟨assignment,satisfies⟩
    refine ⟨fun x i => assignment i.val (x,0),?_⟩
    intro x color atom ha
    have holds := satisfies color atom ha (x+1,0)
    change PeriodicOneInThree.ExactlyOne (List.map _ _) at holds ⊢
    convert holds using 1
    apply List.map_congr_left
    intro i hi
    have index := incidence_tripleIndex_lt p color atom hi
    have pos := position_eq p locality color atom hi
    have vert := incidence_offset_vertical_eq_zero horizontal color atom hi
    simp only [value,dif_pos index,LocalWindow.windowAt,liftAssignment,Cell.sub,vert,sub_zero]
    congr 2
    omega
  · rintro ⟨configuration,valid⟩
    refine ⟨fun j x => value p j (configuration x.1),?_⟩
    intro color atom ha x
    have holds := valid (x.1-1) color atom ha
    change PeriodicOneInThree.ExactlyOne (List.map _ _) at holds ⊢
    convert holds using 1
    apply List.map_congr_left
    intro i hi
    have pos := position_eq p locality color atom hi
    change value p i.tripleIndex (configuration (x.1-i.offset.1)) =
      value p i.tripleIndex (configuration ((x.1-1)+(position i).val))
    congr 2
    omega

def decodeWord (p : PeriodicThreeDM) (word : Nat) : Window p :=
  fun c i => word.testBit (finProdFinEquiv (c,i)).val

def encodeWindow (p : PeriodicThreeDM) (w : Window p) : Nat :=
  (BitVec.ofBoolListLE (List.ofFn fun i : Fin (3*p.triples.length) =>
    w (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)).toNat

theorem decodeWord_encodeWindow (p : PeriodicThreeDM) (w : Window p) : decodeWord p (encodeWindow p w) = w := by
  funext c i
  simp only [decodeWord,encodeWindow,BitVec.testBit_toNat,BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  rw [dif_pos (finProdFinEquiv (c,i)).isLt]
  change w (finProdFinEquiv.symm (finProdFinEquiv (c,i))).1
    (finProdFinEquiv.symm (finProdFinEquiv (c,i))).2 = w c i
  rw [Equiv.symm_apply_apply]

theorem encodeWindow_lt (p : PeriodicThreeDM) (w : Window p) : encodeWindow p w < 2^(3*p.triples.length) := by
  have h := (BitVec.ofBoolListLE (List.ofFn fun i : Fin (3*p.triples.length) =>
    w (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)).isLt
  simpa [encodeWindow] using h

def packedTransition (p : PeriodicThreeDM) (a b : Nat) : Prop :=
  LocalWindow.Transition (Valid p) (decodeWord p a) (decodeWord p b)
abbrev PackedState (p : PeriodicThreeDM) := Fin (2^(3*p.triples.length))

theorem satisfiable_iff_packed_cycle (p : PeriodicThreeDM)
    (horizontal : p.IsOneDimensional) (locality : p.IsLocal) : p.Satisfiable ↔
    FiniteState.HasCycle (fun a b : PackedState p => packedTransition p a.val b.val) := by
  rw [satisfiable_iff p horizontal locality,LocalWindow.satisfiable_iff_cycle]
  constructor
  · rintro ⟨period,states,step⟩
    refine ⟨period,fun i => ⟨encodeWindow p (states i),encodeWindow_lt p (states i)⟩,?_⟩
    intro i
    simpa only [packedTransition,decodeWord_encodeWindow] using step i
  · rintro ⟨period,states,step⟩
    exact ⟨period,fun i => decodeWord p (states i).val,step⟩

end LeanTrominoes.PeriodicThreeDM.LineWindow
