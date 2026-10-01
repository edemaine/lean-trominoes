/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingState

/-! # Breadth-first alternating layers for perfect matching

The extra Hall check rejects whenever a layer grows by fewer vertices than
the initial number of free left vertices. Before reaching a free right
vertex, such a layer witnesses a deficient neighbor set. Thus a successful
search of depth `D` also certifies `freeCount*D ≤ |L|`, which directly supplies
the density hypothesis of the square-root phase bound.
-/
namespace LeanTrominoes.BipartiteMatching.BreadthSearch
variable {L R : Type*} [DecidableEq L] [DecidableEq R]

structure Wave (L : Type*) where
  distance : L → Option Nat
  next : List L
  terminal : Bool
  cost : Nat

def visit (matching : State L R) (depth : Nat) : List R → Wave L → Wave L
  | [],s => { s with cost := s.cost+1 }
  | r::rs,s =>
    match matching.right r with
    | none => visit matching depth rs { s with terminal := true,cost := s.cost+5 }
    | some w =>
      match s.distance w with
      | some _ => visit matching depth rs { s with cost := s.cost+6 }
      | none => visit matching depth rs
          { s with distance := Function.update s.distance w (some (depth+1)),
                   next := w::s.next,cost := s.cost+10 }

def expand (buckets : L → List R) (matching : State L R) (depth : Nat) : List L → Wave L → Wave L
  | [],s => { s with cost := s.cost+1 }
  | v::vs,s => expand buckets matching depth vs
      (visit matching depth (buckets v) { s with cost := s.cost+3 })

inductive Outcome (L : Type*) where
  | layers (distance : L → Option Nat) (depth : Nat) (cost : Nat)
  | deficient (distance : L → Option Nat) (depth : Nat) (cost : Nat)
  | exhausted (cost : Nat)

/-- Fuel is supplied by the number of indexed left vertices. -/
def run (buckets : L → List R) (matching : State L R) (freeCount : Nat) :
    Nat → Nat → List L → (L → Option Nat) → Outcome L
  | 0,_,_,_ => .exhausted 1
  | fuel+1,depth,frontier,distance =>
    let wave := expand buckets matching depth frontier ⟨distance,[],false,0⟩
    if wave.terminal then .layers wave.distance (depth+1) (wave.cost+3)
    else if wave.next.length < freeCount then .deficient wave.distance depth (wave.cost+wave.next.length+4)
    else
      match run buckets matching freeCount fuel (depth+1) wave.next wave.distance with
      | .layers labels height cost => .layers labels height (wave.cost+wave.next.length+5+cost)
      | .deficient labels height cost => .deficient labels height (wave.cost+wave.next.length+5+cost)
      | .exhausted cost => .exhausted (wave.cost+wave.next.length+5+cost)

def freeVertices (vertices : List L) (matching : State L R) : List L :=
  vertices.filter (fun l => (matching.left l).isNone)

def initialDistance (matching : State L R) (l : L) : Option Nat :=
  if (matching.left l).isNone then some 0 else none

def search (vertices : List L) (buckets : L → List R) (matching : State L R) : Outcome L :=
  let free := freeVertices vertices matching
  run buckets matching free.length vertices.length 0 free (initialDistance matching)

end LeanTrominoes.BipartiteMatching.BreadthSearch
