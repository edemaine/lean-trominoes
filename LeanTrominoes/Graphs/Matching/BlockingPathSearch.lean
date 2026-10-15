/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic

/-! # A worklist depth-first search for disjoint paths

Each vertex is entered at most once. Failed branches remain blocked; a
successful route reserves its vertices and terminal. This is the search
primitive used on a Hopcroft–Karp level graph. Function-valued stores denote
indexed RAM arrays, as in the Horn worklist model.
-/
namespace LeanTrominoes.BlockingPath
variable {V T : Type*}

inductive Route (V T : Type*) where
  | last (vertex : V) (terminal : T)
  | cons (vertex : V) (label : T) (rest : Route V T)
  deriving Repr, DecidableEq

def Route.first : Route V T → V
  | .last v _ => v
  | .cons v _ _ => v

def Route.target : Route V T → T
  | .last _ t => t
  | .cons _ _ p => p.target

def Route.vertices : Route V T → List V
  | .last v _ => [v]
  | .cons v _ p => v::p.vertices

abbrev Buckets (V T : Type*) := V → List (T × Option V)

inductive Follows (buckets : Buckets V T) : Route V T → Prop
  | last {v t} : (t,none) ∈ buckets v → Follows buckets (.last v t)
  | cons {v t p} : (t,some p.first) ∈ buckets v → Follows buckets p →
      Follows buckets (.cons v t p)

structure State (V T : Type*) where
  blocked : V → Bool
  used : V → Bool
  reserved : T → Bool

structure Result (V T : Type*) where
  state : State V T
  route : Option (Route V T)
  cost : Nat

def Extends (s t : State V T) : Prop :=
  (∀ v, s.blocked v=true → t.blocked v=true) ∧
  (∀ v, s.used v=true → t.used v=true) ∧
  (∀ r, s.reserved r=true → t.reserved r=true)

theorem Extends.refl (s : State V T) : Extends s s := ⟨fun _ h => h,fun _ h => h,fun _ h => h⟩
theorem Extends.trans {s t u : State V T} (h : Extends s t) (g : Extends t u) : Extends s u :=
  ⟨fun v hv => g.1 v (h.1 v hv),fun v hv => g.2.1 v (h.2.1 v hv),fun r hr => g.2.2 r (h.2.2 r hr)⟩

def Valid (s : State V T) : Prop := ∀ v, s.used v=true → s.blocked v=true

/-- A failed vertex has only blocked successors and reserved terminals. -/
def ClosedAt (buckets : Buckets V T) (s : State V T) (v : V) : Prop :=
  ∀ arc ∈ buckets v, match arc.2 with
    | none => s.reserved arc.1=true
    | some w => s.blocked w=true

def Trap (buckets : Buckets V T) (s : State V T) : Prop :=
  ∀ v, s.blocked v=true → s.used v=false → ClosedAt buckets s v

variable [DecidableEq V] [DecidableEq T]

def enter (s : State V T) (v : V) : State V T :=
  { s with blocked := Function.update s.blocked v true,used := Function.update s.used v true }

def reserve (s : State V T) (t : T) : State V T :=
  { s with reserved := Function.update s.reserved t true }

def retire (s : State V T) (v : V) : State V T :=
  { s with used := Function.update s.used v false }

/-- The list scan is separate so recursive vertex calls use less fuel. -/
def scan (descend : V → State V T → Result V T) (v : V) :
    List (T × Option V) → State V T → Result V T
  | [],s => ⟨s,none,1⟩
  | (t,none)::arcs,s =>
    if s.reserved t then
      let later := scan descend v arcs s
      { later with cost := 8+later.cost }
    else ⟨reserve s t,some (.last v t),8⟩
  | (t,some w)::arcs,s =>
    let child := descend w s
    match child.route with
    | none =>
      let later := scan descend v arcs child.state
      { later with cost := 8+child.cost+later.cost }
    | some path => ⟨child.state,some (.cons v t path),8+child.cost⟩

def search (buckets : Buckets V T) : Nat → V → State V T → Result V T
  | 0,_,s => ⟨s,none,1⟩
  | fuel+1,v,s =>
    if s.blocked v then ⟨s,none,2⟩
    else
      let later := scan (search buckets fuel) v (buckets v) (enter s v)
      match later.route with
      | none => ⟨retire later.state v,none,10+later.cost⟩
      | some p => ⟨later.state,some p,8+later.cost⟩

/-- The exact postcondition needed by the blocking phase. -/
structure Spec (buckets : Buckets V T) (v : V) (s : State V T) (result : Result V T) : Prop where
  extension : Extends s result.state
  valid : Valid result.state
  trap : Trap buckets result.state
  blocked : result.state.blocked v=true
  failure : result.route=none → result.state.used=s.used ∧ result.state.reserved=s.reserved
  success : ∀ p, result.route=some p →
    p.first=v ∧ Follows buckets p ∧ p.vertices.Nodup ∧
    (∀ w ∈ p.vertices, s.blocked w=false) ∧ s.reserved p.target=false ∧
    (∀ w, result.state.used w=true ↔ s.used w=true ∨ w ∈ p.vertices) ∧
    (∀ t, result.state.reserved t=true ↔ s.reserved t=true ∨ t=p.target)

end LeanTrominoes.BlockingPath
