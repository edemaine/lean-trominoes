/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Complexity.FiniteCertificateStack

/-! # Symbolic initialization with a bounded binary certificate -/
noncomputable section
namespace LeanTrominoes.FiniteCertificate
open Turing PeriodicCNF PeriodicCNF.BoundedMachineAtom
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin
variable (tm : FinTM2) (space : Nat) [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

def otherStacks : TransitionExpr :=
  TransitionExpr.all ((finiteValues tm.K).map fun stack =>
    if stack=tm.k₀ then .constant true
    else currentStackIs (space := space) (clockBits := 0) (initList tm []) stack)

def initialExpression (initial : List (tm.Γ tm.k₀)) (bit : Bool → tm.Γ tm.k₀) (capacity : Nat) : TransitionExpr :=
  .and (currentLabelIs (tm := tm) (space := space) (clockBits := 0) (some tm.main))
    (.and (currentControlIs (tm := tm) (space := space) (clockBits := 0) tm.initialState)
      (.and (otherStacks tm space) (stackExpression tm space tm.k₀ initial bit capacity)))

theorem otherStacks_encode (cfg : tm.Cfg) (fits : ∀ stack, (cfg.stk stack).length ≤ space) :
    (otherStacks tm space).eval (FiniteMachineTrace.configValues tm space cfg)
      (FiniteMachineTrace.configValues tm space cfg)=true ↔
      ∀ stack, stack≠tm.k₀ → cfg.stk stack=[] := by
  simp only [otherStacks,TransitionExpr.all_eval,List.all_eq_true,List.forall_mem_map,
    mem_finiteValues,forall_const]
  apply forall_congr'
  intro stack
  by_cases same : stack=tm.k₀
  · simp [same,TransitionExpr.eval]
  · simp only [if_neg same,FiniteMachineTrace.configValues]
    rw [currentStackIs_encode_iff ⟨0,cfg⟩ ⟨0,cfg⟩ (initList tm []) stack (fits stack)
      (by simp [initList,same])]
    simp [initList,same]

omit stackFinite in
theorem cfg_eq_init (cfg : tm.Cfg) (word : List (tm.Γ tm.k₀))
    (label : cfg.l=some tm.main) (control : cfg.var=tm.initialState)
    (input : cfg.stk tm.k₀=word) (others : ∀ stack, stack≠tm.k₀ → cfg.stk stack=[]) :
    cfg=initList tm word := by
  have stackEq : cfg.stk=(initList tm word).stk := by
    funext stack
    by_cases same : stack=tm.k₀
    · subst stack
      simpa [initList] using input
    · simpa [initList,same] using others stack same
  cases cfg
  simp_all only [initList]

theorem initialExpression_encode (initial : List (tm.Γ tm.k₀)) (bit : Bool → tm.Γ tm.k₀)
    (capacity : Nat) (cfg : tm.Cfg) (fits : ∀ stack, (cfg.stk stack).length ≤ space)
    (room : initial.length+capacity ≤ space) :
    (initialExpression tm space initial bit capacity).eval
      (FiniteMachineTrace.configValues tm space cfg) (FiniteMachineTrace.configValues tm space cfg)=true ↔
      ∃ certificate : List Bool, certificate.length ≤ capacity ∧
        cfg=initList tm (initial++certificate.map bit) := by
  simp only [initialExpression,TransitionExpr.eval,Bool.and_eq_true]
  rw [otherStacks_encode tm space cfg fits,
    stackExpression_encode tm space tm.k₀ initial bit capacity cfg (fits tm.k₀) room]
  have labelEq : (currentLabelIs (tm := tm) (space := space) (clockBits := 0) (some tm.main)).eval
      (FiniteMachineTrace.configValues tm space cfg) (FiniteMachineTrace.configValues tm space cfg)=true ↔
      cfg.l=some tm.main := by
    simp [currentLabelIs,TransitionExpr.current,TransitionExpr.eval,TransitionWire.value,
      FiniteMachineTrace.configValues]
  have controlEq : (currentControlIs (tm := tm) (space := space) (clockBits := 0) tm.initialState).eval
      (FiniteMachineTrace.configValues tm space cfg) (FiniteMachineTrace.configValues tm space cfg)=true ↔
      cfg.var=tm.initialState := by
    simp [currentControlIs,TransitionExpr.current,TransitionExpr.eval,TransitionWire.value,
      FiniteMachineTrace.configValues]
  rw [labelEq,controlEq]
  constructor
  · rintro ⟨label,control,others,certificate,bound,input⟩
    exact ⟨certificate,bound,cfg_eq_init tm cfg _ label control input others⟩
  · rintro ⟨certificate,bound,rfl⟩
    refine ⟨rfl,rfl,?_,certificate,bound,?_⟩
    · intro stack different
      simp [initList,different]
    · simp [initList]

theorem initialExpression_atomsBelow (initial : List (tm.Γ tm.k₀)) (bit : Bool → tm.Γ tm.k₀)
    (capacity : Nat) :
    (initialExpression tm space initial bit capacity).AtomsBelow
      (atomCount (tm := tm) (space := space) (clockBits := 0)) := by
  refine ⟨currentLabelIs_atomsBelow _,currentControlIs_atomsBelow _,?_,
    stackExpression_atomsBelow tm space tm.k₀ initial bit capacity⟩
  apply TransitionExpr.all_atomsBelow
  intro expression member
  obtain ⟨stack,_,rfl⟩ := List.mem_map.mp member
  split_ifs
  · trivial
  · exact currentStackIs_atomsBelow _ _

theorem otherStacks_gateCount_le :
    (otherStacks tm space).gateCount ≤ Fintype.card tm.K*(2*space+2)+1 := by
  have bound (indices : List tm.K) :
      (TransitionExpr.all (indices.map fun stack =>
        if stack=tm.k₀ then .constant true
        else currentStackIs (space := space) (clockBits := 0) (initList tm []) stack)).gateCount ≤
      indices.length*(2*space+2)+1 := by
    induction indices with
    | nil => simp [TransitionExpr.all,TransitionExpr.gateCount]
    | cons stack rest ih =>
      simp only [List.map_cons,TransitionExpr.all,TransitionExpr.gateCount,List.length_cons,Nat.add_mul]
      split_ifs <;> simp only [TransitionExpr.gateCount,currentStackIs_gateCount] <;> omega
  simpa [otherStacks,finiteValues] using bound (finiteValues tm.K)

theorem initialExpression_gateCount_le (initial : List (tm.Γ tm.k₀)) (bit : Bool → tm.Γ tm.k₀)
    (capacity : Nat) :
    (initialExpression tm space initial bit capacity).gateCount ≤
      Fintype.card tm.K*(2*space+2)+6*space+7 := by
  have others := otherStacks_gateCount_le tm space
  have input := stackExpression_gateCount_le tm space tm.k₀ initial bit capacity
  simp only [initialExpression,TransitionExpr.gateCount,currentLabelIs,currentControlIs,
    TransitionExpr.current,TransitionExpr.gateCount]
  omega

end LeanTrominoes.FiniteCertificate
