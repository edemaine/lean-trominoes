/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFiniteSearch

/-! # Finite obstructions with prescribed Boolean values -/
namespace LeanTrominoes.PeriodicCNF

abbrev Seed (V : Type) := List ((V × Cell) × Bool)

def Seeded {V : Type} (f : PeriodicCNF V) (seed : Seed V) : Prop :=
  ∃ a : V → Cell → Bool, f.Satisfies a ∧
    ∀ pin ∈ seed, a pin.1.1 pin.1.2 = pin.2

namespace FiniteSearch
variable {V : Type} [DecidableEq V]

def withSeed (f : PeriodicCNF V) (seed : Seed V) (r : Nat) : Ground V :=
  instantiate f r ++ seed.map (fun pin => [pin])

omit [DecidableEq V] in
theorem holds_withSeed (f : PeriodicCNF V) (seed : Seed V) (r : Nat)
    (a : V × Cell → Bool) :
    Holds (withSeed f seed r) a ↔
      Holds (instantiate f r) a ∧ ∀ pin ∈ seed, a pin.1 = pin.2 := by
  simp only [withSeed,Holds,List.forall_mem_append,List.forall_mem_map,
    List.mem_singleton,exists_eq_left]

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
    simpa only [List.mem_cons,exists_eq_or_imp,Set.setOf_or] using one.union ih

omit [DecidableEq V] in
private theorem holds_closed (g : Ground V) : IsClosed {a | Holds g a} := by
  unfold Holds
  convert isClosed_iInter (fun clause => isClosed_iInter (fun (_ : clause ∈ g) =>
    clause_closed clause)) using 1
  ext a
  simp

theorem seeded_iff (f : PeriodicCNF V) (seed : Seed V) :
    f.Seeded seed ↔ ∀ r, Check (withSeed f seed r) := by
  constructor
  · rintro ⟨a,ha,hpins⟩ r
    apply (check_iff _).2
    refine ⟨fun p => a p.1 p.2,(holds_withSeed _ _ _ _).2 ⟨?_,hpins⟩⟩
    exact (holds_instantiate _ _ _).2 (fun c _ clause hc => ha c clause hc)
  · intro finite
    let patches (r : Nat) : Set (V × Cell → Bool) := {a | Holds (withSeed f seed r) a}
    have nonempty (r : Nat) : (patches r).Nonempty := (check_iff _).1 (finite r)
    have closed (r : Nat) : IsClosed (patches r) := holds_closed _
    have decreasing (r : Nat) : patches (r+1) ⊆ patches r := by
      intro a ha
      obtain ⟨formula,pins⟩ := (holds_withSeed _ _ _ _).1 ha
      apply (holds_withSeed _ _ _ _).2
      refine ⟨(holds_instantiate _ _ _).2 ?_,pins⟩
      intro c hc clause hclause
      apply (holds_instantiate _ _ _).1 formula c _ clause hclause
      rw [TrominoAssignment.mem_boxCellList_iff] at hc ⊢
      exact LeanWang.inBox_mono (by omega) hc
    obtain ⟨a,ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      patches decreasing nonempty (closed 0).isCompact closed
    have all : ∀ r, a ∈ patches r := by simpa using ha
    refine ⟨fun v c => a (v,c),?_,(holds_withSeed _ _ _ _).1 (all 0) |>.2⟩
    intro c clause hc
    apply (holds_instantiate _ _ _).1
      ((holds_withSeed _ _ _ _).1 (all (max c.1.natAbs c.2.natAbs))).1 c _ clause hc
    rw [TrominoAssignment.mem_boxCellList_iff]
    exact LeanWang.inBox_of_natAbs_le (Nat.le_max_left _ _) (Nat.le_max_right _ _)

end FiniteSearch
end LeanTrominoes.PeriodicCNF
