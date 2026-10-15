/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.PeriodicBooleanSignedDecoder
import LeanTrominoes.SAT.ExactOne.PeriodicOneInThreeComputability
import LeanTrominoes.SAT.ExactOne.PeriodicOneInThreeNoUnitsComputability
import LeanTrominoes.SAT.ExactOne.PeriodicOneInThreePolarityNormalizationComputability

/-! # Finite prescriptions through exact-one conversion and normalization -/
namespace LeanTrominoes
open PeriodicCNF.SignedDecoder

namespace PeriodicCNF.SignedDecoder
def inclusionRead {V Aux : Type} (v : V) : PeriodicLiteral (V ⊕ Aux) := ⟨Sum.inl v,(0,0),true⟩

theorem inclusionRead_primrec {V Aux : Type} [Primcodable V] [Primcodable Aux] :
    Primrec (@inclusionRead V Aux) :=
  PeriodicLiteral.equivData_symm_primrec.comp
    (Primrec.pair Primrec.sumInl (Primrec.const ((0,0),true)))
end PeriodicCNF.SignedDecoder

namespace PeriodicOneInThree
variable {V : Type}

theorem seedFactor (source : PeriodicCNF V) (width : source.WidthAtMost 3) :
    LogicalFactor source.Satisfies (Satisfies (formula source)) inclusionRead Set.univ := by
  constructor
  · intro a ha
    have equal : decode inclusionRead a = restrictAssignment a := by
      funext v c
      simp [decode,inclusionRead,restrictAssignment,Cell.add]
    rw [equal]
    exact satisfies_of_formula_satisfies source width a ha
  · intro a ha
    refine ⟨extendAssignment a,formula_satisfies_of_satisfies source width a ha,?_⟩
    intro v _ c
    simp [decode,inclusionRead,extendAssignment,Cell.add]

theorem seeded_iff (source : PeriodicCNF V) (width : source.WidthAtMost 3)
    (seed : PeriodicCNF.Seed V) :
    source.Seeded seed ↔ Prescribed (Satisfies (formula source)) (transportSeed inclusionRead seed) :=
  (seedFactor source width).seeded_iff seed (fun _ _ => Set.mem_univ _)

end PeriodicOneInThree

namespace PeriodicOneInThreeNoUnits
variable {V : Type}

theorem seedFactor (source : PeriodicCNF V) :
    LogicalFactor (PeriodicOneInThree.Satisfies source)
      (PeriodicOneInThree.Satisfies (formula source)) inclusionRead Set.univ := by
  constructor
  · intro a ha
    have equal : decode inclusionRead a = restrictAssignment a := by
      funext v c
      simp [decode,inclusionRead,restrictAssignment,Cell.add]
    rw [equal]
    exact satisfies_of_formula_satisfies source a ha
  · intro a ha
    refine ⟨extendAssignment a,formula_satisfies_of_satisfies source a ha,?_⟩
    intro v _ c
    simp [decode,inclusionRead,extendAssignment,Cell.add]

theorem seeded_iff (source : PeriodicCNF V) (seed : PeriodicCNF.Seed V) :
    Prescribed (PeriodicOneInThree.Satisfies source) seed ↔
      Prescribed (PeriodicOneInThree.Satisfies (formula source)) (transportSeed inclusionRead seed) :=
  (seedFactor source).seeded_iff seed (fun _ _ => Set.mem_univ _)

end PeriodicOneInThreeNoUnits

namespace PeriodicOneInThreePolarityNormalization
variable {V : Type}

theorem seedFactor (source : PeriodicCNF V) :
    LogicalFactor (PeriodicOneInThree.Satisfies source)
      (PeriodicOneInThree.Satisfies (formula source)) inclusionRead Set.univ := by
  constructor
  · intro a ha
    have equal : decode inclusionRead a = restrictAssignment a := by
      funext v c
      simp [decode,inclusionRead,restrictAssignment,Cell.add]
    rw [equal]
    exact satisfies_of_formula_satisfies source a ha
  · intro a ha
    refine ⟨extendAssignment a,formula_satisfies_of_satisfies source a ha,?_⟩
    intro v _ c
    simp [decode,inclusionRead,extendAssignment,Cell.add]

theorem seeded_iff (source : PeriodicCNF V) (seed : PeriodicCNF.Seed V) :
    Prescribed (PeriodicOneInThree.Satisfies source) seed ↔
      Prescribed (PeriodicOneInThree.Satisfies (formula source)) (transportSeed inclusionRead seed) :=
  (seedFactor source).seeded_iff seed (fun _ _ => Set.mem_univ _)

end PeriodicOneInThreePolarityNormalization

open Lean Elab Command in
run_cmd do
  for name in [``PeriodicOneInThree.seedFactor,``PeriodicOneInThreeNoUnits.seedFactor,
      ``PeriodicOneInThreePolarityNormalization.seedFactor] do
    let axioms ← Lean.collectAxioms name
    let extra := axioms.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes
