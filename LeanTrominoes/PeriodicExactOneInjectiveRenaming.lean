/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFInjectiveRenaming
import LeanTrominoes.PeriodicOneInThree

/-! # Exact-one satisfiability under injective atom renaming -/
namespace LeanTrominoes.PeriodicOneInThree
variable {V W : Type*} (g : V → W) (f : PeriodicCNF V)

theorem satisfies_rename (assignment : W → Cell → Bool) :
    Satisfies (f.rename g) assignment ↔ Satisfies f (fun v => assignment (g v)) := by
  simp [PeriodicCNF.rename,PeriodicCNF.renameClause,Satisfies,ClauseHolds,
    clauseValues,PeriodicLiteral.rename,List.map_map,Function.comp_def]

theorem satisfiable_rename_iff (injective : Function.Injective g) :
    Satisfiable (f.rename g) ↔ Satisfiable f := by
  classical
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨fun v => a (g v),(satisfies_rename g f a).mp ha⟩
  · rintro ⟨a,ha⟩
    let target : W → Cell → Bool := fun w cell =>
      if h : ∃ v, g v=w then a h.choose cell else false
    refine ⟨target,(satisfies_rename g f target).mpr ?_⟩
    have eq (v : V) : target (g v)=a v := by
      funext cell
      simp only [target,dif_pos (show ∃ u, g u=g v from ⟨v,rfl⟩)]
      congr 1
      exact injective (Exists.choose_spec (show ∃ u, g u=g v from ⟨v,rfl⟩))
    simpa only [eq] using ha
end LeanTrominoes.PeriodicOneInThree
