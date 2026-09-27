/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic

/-! # Horn rules and their period-one models in arbitrary dimensions

A missing conclusion represents a negative clause. Offsets belong to any
additive group; in particular they may belong to `Fin d → Int` for any `d`.
-/
namespace LeanTrominoes.Horn

structure Rule (Variable : Type*) where
  premises : List Variable
  conclusion : Option Variable
  deriving DecidableEq, Repr

def Rule.Holds {V : Type*} (r : Rule V) (model : V → Prop) : Prop :=
  (∀ a ∈ r.premises, model a) → match r.conclusion with
    | none => False
    | some a => model a

def Satisfies {V : Type*} (rules : List (Rule V)) (model : V → Prop) : Prop :=
  ∀ r ∈ rules, r.Holds model

def Satisfiable {V : Type*} (rules : List (Rule V)) : Prop := ∃ model, Satisfies rules model

structure PeriodicRule (Variable Offset : Type*) where
  premises : List (Variable × Offset)
  conclusion : Option (Variable × Offset)
  deriving DecidableEq, Repr

def PeriodicRule.erase {V G : Type*} (r : PeriodicRule V G) : Rule V :=
  ⟨r.premises.map Prod.fst,r.conclusion.map Prod.fst⟩

def PeriodicRule.Holds {V G : Type*} [Add G] (r : PeriodicRule V G)
    (model : V → G → Prop) (z : G) : Prop :=
  (∀ a ∈ r.premises, model a.1 (z+a.2)) → match r.conclusion with
    | none => False
    | some a => model a.1 (z+a.2)

def PeriodicSatisfies {V G : Type*} [Add G] (rules : List (PeriodicRule V G)) (model : V → G → Prop) : Prop :=
  ∀ r ∈ rules, ∀ z, r.Holds model z

def PeriodicSatisfiable {V G : Type*} [Add G] (rules : List (PeriodicRule V G)) : Prop :=
  ∃ model, PeriodicSatisfies rules model

theorem constant_satisfies_iff {V G : Type*} [AddGroup G] (rules : List (PeriodicRule V G)) (model : V → Prop) :
    PeriodicSatisfies rules (fun a _ => model a) ↔ Satisfies (rules.map PeriodicRule.erase) model := by
  simp only [PeriodicSatisfies,Satisfies,List.forall_mem_map,PeriodicRule.Holds,
    PeriodicRule.erase,Rule.Holds,List.forall_mem_map]
  constructor
  · intro h r hr
    have one := h r hr 0
    cases head : r.conclusion <;> simpa [head] using one
  · intro h r hr z
    have one := h r hr
    cases head : r.conclusion <;> simpa [head] using one

/-- Intersecting all translates of a model gives a model of the finite quotient. -/
theorem intersection_satisfies {V G : Type*} [AddGroup G] (rules : List (PeriodicRule V G))
    (model : V → G → Prop) (satisfied : PeriodicSatisfies rules model) :
    Satisfies (rules.map PeriodicRule.erase) (fun a => ∀ z, model a z) := by
  intro r hr
  obtain ⟨rule,member,rfl⟩ := List.mem_map.mp hr
  intro premises
  have allPremises (z : G) : ∀ a ∈ rule.premises, model a.1 (z+a.2) := by
    intro a ha
    exact premises a.1 (List.mem_map.mpr ⟨a,ha,rfl⟩) _
  cases head : rule.conclusion with
  | none =>
    have contradiction := satisfied rule member 0 (allPremises 0)
    simp [PeriodicRule.Holds,head] at contradiction
  | some a =>
    change match rule.conclusion.map Prod.fst with
      | none => False
      | some v => ∀ z, model v z
    simp only [head,Option.map_some]
    intro z
    have forced := satisfied rule member (z-a.2) (allPremises (z-a.2))
    simpa [PeriodicRule.Holds,head,sub_add_cancel] using forced

theorem periodic_satisfiable_iff {V G : Type*} [AddGroup G] (rules : List (PeriodicRule V G)) :
    PeriodicSatisfiable rules ↔ Satisfiable (rules.map PeriodicRule.erase) := by
  constructor
  · rintro ⟨model,h⟩
    exact ⟨_,intersection_satisfies rules model h⟩
  · rintro ⟨model,h⟩
    exact ⟨fun a _ => model a,(constant_satisfies_iff rules model).mpr h⟩

theorem exists_period_one {V G : Type*} [AddGroup G] (rules : List (PeriodicRule V G))
    (h : PeriodicSatisfiable rules) : ∃ model : V → Prop, PeriodicSatisfies rules (fun a _ => model a) := by
  obtain ⟨model,hm⟩ := (periodic_satisfiable_iff rules).mp h
  exact ⟨model,(constant_satisfies_iff rules model).mpr hm⟩

end LeanTrominoes.Horn
