/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNF
import LeanTrominoes.PlaneTilingSearchComputability

/-! # Finite obstructions for periodic CNF satisfiability -/
namespace LeanTrominoes.PeriodicCNF
namespace FiniteSearch

variable {V : Type} [DecidableEq V]

abbrev Ground (V : Type) := List (List ((V × Cell) × Bool))

def instantiate (f : PeriodicCNF V) (r : Nat) : Ground V :=
  (TrominoAssignment.boxCellList r).flatMap fun c =>
    f.clauses.map fun clause => clause.map fun l =>
      ((l.atom, Cell.add c l.offset), l.value)

def Holds (g : Ground V) (a : V × Cell → Bool) : Prop :=
  ∀ clause ∈ g, ∃ l ∈ clause, a l.1 = l.2

def atoms (g : Ground V) : List (V × Cell) :=
  g.flatMap fun clause => clause.map Prod.fst

def Check (g : Ground V) : Prop :=
  ∃ selected ∈ PlaneTilingSearch.subsets (atoms g),
    Holds g (fun a => decide (a ∈ selected))

instance (g : Ground V) : Decidable (Check g) := by
  unfold Check Holds
  infer_instance

theorem check_iff (g : Ground V) : Check g ↔ ∃ a, Holds g a := by
  constructor
  · rintro ⟨s, _, hs⟩; exact ⟨_, hs⟩
  · rintro ⟨a, ha⟩
    refine ⟨(atoms g).filter a, PlaneTilingSearch.filter_mem_subsets _ _, ?_⟩
    intro clause hc
    obtain ⟨l, hl, value⟩ := ha clause hc
    refine ⟨l, hl, ?_⟩
    have mem : l.1 ∈ atoms g :=
      List.mem_flatMap.mpr ⟨clause, hc, List.mem_map.mpr ⟨l, hl, rfl⟩⟩
    simp [List.mem_filter, mem, value]

omit [DecidableEq V] in
theorem holds_instantiate (f : PeriodicCNF V) (r : Nat) (a : V × Cell → Bool) :
    Holds (instantiate f r) a ↔
      ∀ c ∈ TrominoAssignment.boxCellList r,
        ∀ clause ∈ f.clauses, clause.Holds (fun v c => a (v,c)) c := by
  simp only [Holds, instantiate, List.forall_mem_flatMap, List.forall_mem_map,
    PeriodicClause.Holds, PeriodicLiteral.Holds]
  simp only [List.mem_map, exists_exists_and_eq_and]

local instance : TopologicalSpace Bool := ⊥
local instance : DiscreteTopology Bool := discreteTopology_bot _
local instance : CompactSpace Bool := Finite.compactSpace

omit [DecidableEq V] in
private theorem clause_closed (clause : List ((V × Cell) × Bool)) :
    IsClosed {a : V × Cell → Bool | ∃ l ∈ clause, a l.1 = l.2} := by
  induction clause with
  | nil => simp
  | cons l ls ih =>
    have one : IsClosed {a : V × Cell → Bool | a l.1 = l.2} :=
      isClosed_singleton.preimage (continuous_apply l.1)
    simpa only [List.mem_cons, exists_eq_or_imp, Set.setOf_or] using one.union ih

omit [DecidableEq V] in
private theorem holds_closed (g : Ground V) : IsClosed {a | Holds g a} := by
  unfold Holds
  convert isClosed_iInter (fun clause => isClosed_iInter (fun (_ : clause ∈ g) =>
    clause_closed clause)) using 1
  ext a
  simp

theorem satisfiable_iff (f : PeriodicCNF V) :
    f.Satisfiable ↔ ∀ r, Check (instantiate f r) := by
  constructor
  · rintro ⟨a, ha⟩ r
    apply (check_iff _).2
    exact ⟨fun p => a p.1 p.2, (holds_instantiate _ _ _).2 (fun c _ clause hc => ha c clause hc)⟩
  · intro finite
    let patches (r : Nat) : Set (V × Cell → Bool) := {a | Holds (instantiate f r) a}
    have nonempty (r : Nat) : (patches r).Nonempty := (check_iff _).1 (finite r)
    have closed (r : Nat) : IsClosed (patches r) := holds_closed _
    have decreasing (r : Nat) : patches (r + 1) ⊆ patches r := by
      intro a ha
      apply (holds_instantiate _ _ _).2
      intro c hc
      apply (holds_instantiate _ _ _).1 ha c
      rw [TrominoAssignment.mem_boxCellList_iff] at hc ⊢
      exact LeanWang.inBox_mono (by omega) hc
    obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      patches decreasing nonempty (closed 0).isCompact closed
    have all : ∀ r, a ∈ patches r := by simpa using ha
    refine ⟨fun v c => a (v,c), fun c clause hc => ?_⟩
    apply (holds_instantiate _ _ _).1 (all (max c.1.natAbs c.2.natAbs)) c _ clause hc
    rw [TrominoAssignment.mem_boxCellList_iff]
    exact LeanWang.inBox_of_natAbs_le (Nat.le_max_left _ _) (Nat.le_max_right _ _)

end FiniteSearch
end LeanTrominoes.PeriodicCNF
