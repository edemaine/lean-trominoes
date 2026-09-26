/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision
import LeanTrominoes.PeriodicCNFIncidenceGraphSize
import LeanTrominoes.PeriodicCNFInjectiveRenaming

/-! # Polarity normalization retains at least the source literal count -/
namespace LeanTrominoes

@[simp] theorem PeriodicCNF.literalCount_anchorNormalize {V : Type*} (source : PeriodicCNF V) :
    source.anchorNormalize.presentationLiteralCount = source.presentationLiteralCount := by
  simp [presentationLiteralCount, anchorNormalize, List.length_flatten, List.map_map,
    PeriodicClause.anchorNormalize, Function.comp_def]

@[simp] theorem PeriodicCNF.literalCount_variableGauge {V : Type*} (source : PeriodicCNF V) (gauge : V → Cell) :
    (source.variableGauge gauge).presentationLiteralCount = source.presentationLiteralCount := by
  simp [presentationLiteralCount, variableGauge, List.length_flatten, List.map_map,
    PeriodicClause.variableGauge, Function.comp_def]

@[simp] theorem PeriodicCNF.literalCount_rename {V W : Type*} (source : PeriodicCNF V) (name : V → W) :
    (source.rename name).presentationLiteralCount = source.presentationLiteralCount := by
  simp [presentationLiteralCount, rename, renameClause, List.length_flatten, List.map_map, Function.comp_def]

namespace PeriodicOneInThreePolarityNormalization

theorem literalCount_le {V : Type*} (source : PeriodicCNF V) :
    source.presentationLiteralCount ≤ (formula source).presentationLiteralCount := by
  have block (ci : Nat) (clause : PeriodicClause V) :
      clause.length ≤ (clauseClauses ci clause).flatten.length := by
    simp [clauseClauses, normalizeClause, normalizeClauseFrom]
  have lifted (tags : List (PeriodicClause V × Nat)) :
      (tags.flatMap Prod.fst).length ≤
        (tags.flatMap (fun tag => (clauseClauses tag.2 tag.1).flatten)).length := by
    induction tags with
    | nil => rfl
    | cons tag tags ih =>
        simp only [List.flatMap_cons, List.length_append]
        have := block tag.2 tag.1
        omega
  have bound := lifted source.clauses.zipIdx
  have sourceEq : source.clauses.zipIdx.flatMap Prod.fst = source.clauses.flatten := by
    simpa only [List.flatten_eq_flatMap, List.flatMap_map, Function.comp_def, id_eq] using
      congrArg List.flatten (List.zipIdx_map_fst 0 source.clauses)
  rw [sourceEq] at bound
  simpa only [PeriodicCNF.presentationLiteralCount, formula, List.flatten_eq_flatMap,
    List.flatMap_assoc] using bound

end PeriodicOneInThreePolarityNormalization
end LeanTrominoes
