/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Planar.PeriodicPlanarSATGeometricPlaneCompleteness
import LeanTrominoes.SAT.Planar.PeriodicPlanarSATInjectiveRenaming

/-! # Natural-number atoms preserve the complete geometric plane languages -/
namespace LeanTrominoes.PeriodicPlanarSAT.GeometricNat

private theorem transport {A B : Type} [Primcodable A] [Primcodable B]
    {p : A → Prop} {q : B → Prop} (complete : LeanWang.CoREComplete p)
    (membership : LeanWang.CoREPred q) (map : A → B) (computable : Computable map)
    (correct : ∀ a, p a ↔ q (map a)) : LeanWang.CoREComplete q := by
  refine ⟨membership,?_⟩
  intro C _ source hs
  obtain ⟨f,hf,hcorrect⟩ := complete.2 source hs
  exact ⟨map ∘ f,computable.comp hf,fun a => (hcorrect a).trans (correct (f a))⟩

private theorem rename_computable {V : Type} [Primcodable V] :
    Computable (renameInput (Encodable.encode : V → ℕ)) := by
  have literal : Primrec (PeriodicLiteral.rename (Encodable.encode : V → ℕ)) :=
    PeriodicLiteral.equivData_symm_primrec.comp
      ((Primrec.pair (Primrec.encode.comp Primrec.fst) Primrec.snd).comp PeriodicLiteral.equivData_primrec)
  have clause := Primrec.list_map Primrec.id (literal.comp Primrec.snd).to₂
  have formula : Primrec (PeriodicCNF.rename (Encodable.encode : V → ℕ)) :=
    PeriodicCNF.equivData_symm_primrec.comp
      ((Primrec.list_map Primrec.id (clause.comp Primrec.snd).to₂).comp PeriodicCNF.equivData_primrec)
  exact (Primrec.pair (formula.comp Primrec.fst) Primrec.snd).to_comp

macro "geometric_rename" : tactic => `(tactic|
  simp only [Geometric,Orbit.BoundedLocalProblem,Orbit.BoundedLocalThreeOccurrenceProblem,
    Orbit.LocalProblem,Orbit.LocalThreeOccurrenceProblem,Orbit.Problem,Orbit.ThreeOccurrenceProblem,Orbit.Valid,
    Unbounded.BoundedLocalExactOneProblem,Unbounded.BoundedLocalExactOneThreeOccurrenceProblem,
    Unbounded.LocalExactOneProblem,Unbounded.LocalExactOneThreeOccurrenceProblem,
    Unbounded.ExactOneProblem,Unbounded.ExactOneThreeOccurrenceProblem,Unbounded.Valid,
    GridBound,PeriodicCNF.presentationSize_rename,renameInput,
    PeriodicCNF.local_rename,PeriodicCNF.width_rename,
    PeriodicCNF.occurrences_rename_iff _ Encodable.encode_injective,
    PeriodicCNF.orbitCompatible_rename _ Encodable.encode_injective,
    PeriodicCNF.finiteCompatible_rename _ Encodable.encode_injective,
    PeriodicCNF.satisfiable_rename_iff _ _ Encodable.encode_injective,
    PeriodicOneInThree.satisfiable_rename_iff _ _ Encodable.encode_injective])

theorem ordinary : LeanWang.CoREComplete (Geometric (Orbit.BoundedLocalProblem (V:=ℕ))) := by
  classical
  apply transport ThreeOccurrenceGeometry.WangReduction.geometricBoundedLocalCoREComplete
    (GeometricSearch.geometric_coRE Orbit.boundedLocalProblem_coRE) (renameInput Encodable.encode) rename_computable
  intro input
  geometric_rename
  apply Iff.of_eq
  congr <;> exact Subsingleton.elim _ _

theorem ordinaryThree : LeanWang.CoREComplete (Geometric (Orbit.BoundedLocalThreeOccurrenceProblem (V:=ℕ))) := by
  classical
  apply transport ThreeOccurrenceGeometry.WangReduction.geometricBoundedLocalThreeOccurrenceCoREComplete
    (GeometricSearch.geometric_coRE Orbit.boundedLocalThreeOccurrenceProblem_coRE) (renameInput Encodable.encode) rename_computable
  intro input
  geometric_rename
  apply Iff.of_eq
  congr <;> exact Subsingleton.elim _ _

theorem exactOne : LeanWang.CoREComplete (Geometric (Unbounded.BoundedLocalExactOneProblem (V:=ℕ))) := by
  classical
  apply transport ExactOneEndpoint.WangReduction.geometricBoundedLocalCoREComplete
    (GeometricSearch.geometric_coRE Unbounded.boundedLocalExactOneProblem_coRE) (renameInput Encodable.encode) rename_computable
  intro input
  geometric_rename
  apply Iff.of_eq
  congr <;> exact Subsingleton.elim _ _

theorem exactOneThree : LeanWang.CoREComplete (Geometric (Unbounded.BoundedLocalExactOneThreeOccurrenceProblem (V:=ℕ))) := by
  classical
  apply transport ExactOneEndpoint.WangReduction.geometricBoundedLocalThreeOccurrenceCoREComplete
    (GeometricSearch.geometric_coRE Unbounded.boundedLocalExactOneThreeOccurrenceProblem_coRE) (renameInput Encodable.encode) rename_computable
  intro input
  geometric_rename
  apply Iff.of_eq
  congr <;> exact Subsingleton.elim _ _

end LeanTrominoes.PeriodicPlanarSAT.GeometricNat
