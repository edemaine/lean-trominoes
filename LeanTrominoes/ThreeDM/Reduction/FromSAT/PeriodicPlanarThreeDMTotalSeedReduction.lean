/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ThreeDM.Reduction.FromSAT.PeriodicPlanarThreeDMSeedComputability
import LeanTrominoes.SAT.CNF.PeriodicBooleanSeedSupport
import LeanTrominoes.ThreeDM.PeriodicThreeDMCNF
import LeanTrominoes.SAT.ExactOne.PeriodicExactOneSeededCoRE

/-! # Total seed reductions, including unused variables and inconsistent pins -/
noncomputable section
namespace LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM
open PeriodicCNF.SignedDecoder
variable {V : Type} [DecidableEq V]

theorem exactOne_stable_on_occurringVariables (source : PeriodicCNF V)
    (a b : V → Cell → Bool)
    (same : ∀ v ∈ occurringVariables source, ∀ c, a v c = b v c) :
    PeriodicOneInThree.Satisfies source a ↔ PeriodicOneInThree.Satisfies source b := by
  have values (c : Cell) (clause : PeriodicClause V) (member : clause ∈ source.clauses) :
      PeriodicOneInThree.clauseValues a c clause = PeriodicOneInThree.clauseValues b c clause := by
    apply List.map_congr_left
    intro literal literalMember
    rw [same literal.atom (by
      change literal.atom ∈ (PeriodicCNF.variableOccurrences source).dedup
      rw [List.mem_dedup]
      exact List.mem_flatMap.mpr ⟨clause,member,List.mem_map.mpr ⟨literal,literalMember,rfl⟩⟩)]
  constructor <;> intro valid c clause member
  · unfold PeriodicOneInThree.ClauseHolds
    rw [← values c clause member]
    exact valid c clause member
  · unfold PeriodicOneInThree.ClauseHolds
    rw [values c clause member]
    exact valid c clause member

def totalSeedReduction (source : PeriodicCNF V) : PeriodicCNF.Seed V → PeriodicCNF.Seed Nat :=
  supportedReduction (occurringVariables source) (encodedSeedRead source) 0

theorem totalSeedReduction_correct (source : PeriodicCNF V)
    (occurrences : source.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source) (seed : PeriodicCNF.Seed V) :
    Prescribed (PeriodicOneInThree.Satisfies source) seed ↔
      Prescribed (encodedProblem source).Satisfies (totalSeedReduction source seed) :=
  supportedReduction_correct _ _ (encodedSeedFactor source occurrences arity)
    (exactOne_stable_on_occurringVariables source) seed

theorem totalSeedReduction_primrec [Primcodable V] (source : PeriodicCNF V) :
    Primrec (totalSeedReduction source) :=
  supportedReduction_primrec _ (encodedSeedRead_primrec source) _

end LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM

namespace LeanTrominoes.PeriodicThreeDM
open PeriodicCNF.SignedDecoder

theorem prescribed_coRE (problem : PeriodicThreeDM) :
    LeanWang.CoREPred (Prescribed problem.Satisfies) := by
  have upper := PeriodicExactOneCNF.fixed_seeded_coRE (AsCNF.exactOne problem)
  exact upper.of_eq (fun seed => not_congr (by
    apply exists_congr
    intro a
    exact and_congr (AsCNF.exactOne_satisfies problem a) Iff.rfl))

end LeanTrominoes.PeriodicThreeDM
