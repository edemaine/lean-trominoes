/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFRenamingData
import LeanTrominoes.PeriodicCNFOneDimensional
import Mathlib.Logic.Function.Basic

/-! # Semantic and syntactic invariance under injective atom renaming -/
namespace LeanTrominoes.PeriodicCNF

variable {V W : Type*} (g : V → W) (f : PeriodicCNF V)

theorem satisfies_rename (assignment : W → Cell → Bool) :
    (f.rename g).Satisfies assignment ↔ f.Satisfies (fun v => assignment (g v)) := by
  simp [rename,renameClause,Satisfies,PeriodicClause.Holds,PeriodicLiteral.Holds,PeriodicLiteral.rename]

theorem satisfiable_rename_iff (injective : Function.Injective g) :
    (f.rename g).Satisfiable ↔ f.Satisfiable := by
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

theorem width_rename (bound : Nat) : (f.rename g).WidthAtMost bound ↔ f.WidthAtMost bound := by
  simp [rename,renameClause,WidthAtMost,PeriodicClause.WidthAtMost]

theorem oneDimensional_rename : (f.rename g).IsOneDimensional ↔ f.IsOneDimensional := by
  simp [rename,renameClause,IsOneDimensional,PeriodicLiteral.rename]

theorem localOnLine_rename : (f.rename g).IsLocalOnLine ↔ f.IsLocalOnLine := by
  simp [rename,renameClause,IsLocalOnLine,PeriodicClause.IsLocalOnLine,
    PeriodicClause.offsetDistanceOnLine,PeriodicLiteral.rename]

theorem variableOccurrences_rename : (f.rename g).variableOccurrences = f.variableOccurrences.map g := by
  simp [rename,renameClause,variableOccurrences,List.flatMap_map,List.map_flatMap,List.map_map,
    Function.comp_def,PeriodicLiteral.rename]

theorem occurrences_rename [DecidableEq V] [DecidableEq W]
    (injective : Function.Injective g) (bound : Nat) (h : f.OccurrencesAtMost bound) :
    (f.rename g).OccurrencesAtMost bound := by
  intro w
  rw [variableOccurrences_rename]
  by_cases hm : w ∈ f.variableOccurrences.map g
  · obtain ⟨v,_,rfl⟩ := List.mem_map.mp hm
    rw [List.count_map_of_injective _ _ injective]
    exact h v
  · rw [List.count_eq_zero.mpr hm]
    exact Nat.zero_le _

end LeanTrominoes.PeriodicCNF

namespace LeanTrominoes

/-- Use compact ranks on a finite support and disjoint codes everywhere else. -/
def supportedNatCode {V : Type*} [DecidableEq V] [Encodable V]
    (support : List V) (v : V) : Nat :=
  if v ∈ support then support.idxOf v else support.length+Encodable.encode v

theorem supportedNatCode_injective {V : Type*} [DecidableEq V] [Encodable V]
    (support : List V) : Function.Injective (supportedNatCode support) := by
  intro a b eq
  by_cases ha : a ∈ support <;> by_cases hb : b ∈ support
  · simp only [supportedNatCode,if_pos ha,if_pos hb] at eq
    exact (List.idxOf_inj ha).mp eq
  · have h := List.idxOf_lt_length_iff.mpr ha
    simp only [supportedNatCode,if_pos ha,if_neg hb] at eq
    omega
  · have h := List.idxOf_lt_length_iff.mpr hb
    simp only [supportedNatCode,if_neg ha,if_pos hb] at eq
    omega
  · simp only [supportedNatCode,if_neg ha,if_neg hb,Nat.add_left_cancel_iff] at eq
    exact Encodable.encode_injective eq

end LeanTrominoes
