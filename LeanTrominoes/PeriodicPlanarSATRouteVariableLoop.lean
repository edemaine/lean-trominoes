/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATRouteRepresentativeSemantics

/-! # The representative loop checks exactly one semantic variable endpoint -/
namespace LeanTrominoes.PeriodicPlanarSAT.RouteProgram
open BoundedArithmetic BoundedArithmetic.Expr
open RouteInput PeriodicCNF.FlatScanner PeriodicCNF.IncidenceFields PeriodicCNFFlatEncoding

theorem representatives_truth (input : Input Nat) (e k ci h v : Nat)
    (he : e < input.2.edgeRoutes.length) (hs : v+ci < input.2.vertexPositions.length)
    (c : PeriodicClause Nat) (hc : (h,c)∈clauseEntries 1 input.1.clauses) (hk : k<c.length)
    (ha : c[k].atom∈input.1.variableOccurrences.dedup)
    (ht : input.1.variableOccurrences.dedup.idxOf c[k].atom < input.2.vertexPositions.length) :
    representatives.value ([e,k,ci,h,v]++context input) ≠ 0 ↔
      input.2.edgeRoutes[e].head? = some input.2.vertexPositions[v+ci] ∧
      input.2.edgeRoutes[e].getLast? = some (Cell.add
        input.2.vertexPositions[input.1.variableOccurrences.dedup.idxOf c[k].atom]
        (input.2.periodTranslation (Cell.sub c[k].offset (PeriodicCNF.clauseAnchor c)))) := by
  rw [representatives,NativeScalar.all_value_ne_zero]
  change (∀ r < (formulaFields input.1).length, representativeBody.value ([r,e,k,ci,h,v]++context input) ≠ 0) ↔ _
  have row (r : Nat) : representativeBody.value ([r,e,k,ci,h,v]++context input) ≠ 0 ↔
      (representative input.1 r ∧ (formulaFields input.1)[r]?.getD 0=c[k].atom →
        targetBody.value ([input.1.variableOccurrences.dedup.idxOf c[k].atom,r,e,k,ci,h,v]++context input) ≠ 0) := by
    rw [representativeBody,NativeScalar.implies_value_ne_zero]
    change (representativeGuard.Truth _ → targetBody.value (targetRank.value _ :: _) ≠ 0) ↔ _
    rw [representativeGuard_truth input r e k ci h v c hc hk]
    constructor
    · intro run guard
      have result := run guard
      rw [targetRank_value input r e k ci h v guard.1,guard.2] at result
      exact result
    · intro run guard
      rw [targetRank_value input r e k ci h v guard.1,guard.2]
      exact run guard
  constructor
  · intro run
    obtain ⟨r,hr,eq⟩ := representative_exists input.1 c[k].atom ha
    have checked := (row r).mp (run r (representative_bound input.1 r hr)) ⟨hr,eq⟩
    exact (targetBody_truth input _ r e k ci h v he hs ht c hc hk).mp checked
  · intro checked r _
    apply (row r).mpr
    intro _
    exact (targetBody_truth input _ r e k ci h v he hs ht c hc hk).mpr checked

end LeanTrominoes.PeriodicPlanarSAT.RouteProgram
