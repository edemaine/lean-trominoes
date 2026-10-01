/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingBreadthSemantics
import LeanTrominoes.BipartiteMatchingBreadthCost
import LeanTrominoes.BipartiteMatchingPhaseProgress
import LeanTrominoes.BipartiteMatchingPhaseSize

/-! # Executable finite perfect-matching solver

Each round scans the indexed vertex arrays, computes alternating breadth-first
layers, finds a blocking family in the fixed level graph, and rewires it.
Function stores denote random-access arrays; charges count indexed reads and
writes, scalar operations, and linked-list cells, not Lean VM time. No graph
oracle is used. The trace is ghost data recording successful phase certificates.
-/
namespace LeanTrominoes.BipartiteMatching
open BlockingPath
variable {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L] [Fintype R]

structure SolverResult (L R : Type*) where
  matching : Option (State L R)
  trace : List (Nat × Nat)
  cost : Nat

def phase (buckets : L → List R) (matching : State L R) (distance : L → Option Nat)
    (depth : Nat) (roots : List L) : State L R × Nat :=
  let levels := levelBuckets buckets matching (BreadthSearch.height distance depth) depth
  let paths := batch levels (Fintype.card L) roots initial
  let written := executeRoutes matching paths.paths
  (written.1,10*(∑ l, (buckets l).length)+8*Fintype.card L+4*Fintype.card R+paths.cost+written.2+5)

/-- Vertex-list scans and array initialization are included in the round charge. -/
def solve (vertices : List L) (buckets : L → List R) : Nat → State L R → SolverResult L R
  | 0,matching =>
    let roots := BreadthSearch.freeVertices vertices matching
    ⟨if roots.isEmpty then some matching else none,[],16*vertices.length+3⟩
  | fuel+1,matching =>
    let roots := BreadthSearch.freeVertices vertices matching
    let setup := 16*vertices.length+3
    if roots.isEmpty then ⟨some matching,[],setup⟩ else
      match BreadthSearch.search vertices buckets matching with
      | .deficient _ _ cost => ⟨none,[],setup+cost+2⟩
      | .exhausted cost => ⟨none,[],setup+cost+2⟩
      | .layers distance depth cost =>
        let first := phase buckets matching distance depth roots
        let later := solve vertices buckets fuel first.1
        ⟨later.matching,(roots.length,depth)::later.trace,setup+cost+first.2+later.cost+4⟩

def Full (matching : State L R) : Prop := ∀ l, matching.left l ≠ none

def HasFiniteMatching (buckets : L → List R) : Prop := ∃ f : L ≃ R, ∀ l, f l ∈ buckets l

theorem full_equiv (buckets : L → List R) (matching : State L R)
    (consistent : Consistent matching) (supported : Supported (fun l r => r ∈ buckets l) matching)
    (balanced : Fintype.card L=Fintype.card R) (full : Full matching) : HasFiniteMatching buckets := by
  classical
  have present (l : L) : ∃ r, matching.left l=some r := Option.ne_none_iff_exists'.mp (full l)
  choose f paired using present
  have injective : Function.Injective f := by
    intro l k equal
    have one := (consistent l (f l)).mp (paired l)
    have two := (consistent k (f k)).mp (paired k)
    rw [← equal] at two
    exact Option.some.inj (one.symm.trans two)
  let eqv := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨injective,balanced⟩)
  exact ⟨eqv,fun l => supported l (f l) (paired l)⟩

theorem free_mem (vertices : List L) (matching : State L R) (l : L) :
    l ∈ BreadthSearch.freeVertices vertices matching ↔ l ∈ vertices ∧ matching.left l=none := by
  simp [BreadthSearch.freeVertices]

theorem roots_empty_full (vertices : List L) (complete : ∀ l, l ∈ vertices) (matching : State L R)
    (empty : (BreadthSearch.freeVertices vertices matching).isEmpty=true) : Full matching := by
  intro l free
  have member := (free_mem vertices matching l).mpr ⟨complete l,free⟩
  have nil := List.isEmpty_iff.mp empty
  rw [nil] at member
  simp at member

theorem phase_state (buckets : L → List R) (matching : State L R) (distance : L → Option Nat)
    (depth : Nat) (roots : List L) :
    (phase buckets matching distance depth roots).1=
      applyRoutes matching (batch (levelBuckets buckets matching (BreadthSearch.height distance depth) depth)
        (Fintype.card L) roots initial).paths := by
  exact executeRoutes_state _ _

end LeanTrominoes.BipartiteMatching
