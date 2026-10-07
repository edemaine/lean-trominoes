/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicBooleanSignedDecoder
import LeanTrominoes.PeriodicCNFSeedVariableGauge
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeOneInThree
import LeanTrominoes.PeriodicOneInThreeAnchorNormalization

/-! # Exact-one finite prescriptions under gauges and anchor normalization -/
namespace LeanTrominoes.PeriodicCNF.SignedDecoder
variable {V W X : Type}

theorem compose_primrec [Primcodable V] [Primcodable W] [Primcodable X]
    {first : Read V W} {second : Read W X}
    (one : Primrec first) (two : Primrec second) : Primrec (compose first second) := by
  have a := PeriodicLiteral.equivData_primrec.comp one
  have b := PeriodicLiteral.equivData_primrec.comp (two.comp (Primrec.fst.comp a))
  exact PeriodicLiteral.equivData_symm_primrec.comp
    (Primrec.pair (Primrec.fst.comp b)
      (Primrec.pair
        (Computability.cell_add_primrec.comp
          (Primrec.fst.comp (Primrec.snd.comp a)) (Primrec.fst.comp (Primrec.snd.comp b)))
        (Primrec.ite
          (Primrec.eq.comp (Primrec.snd.comp (Primrec.snd.comp a)) (Primrec.const true))
          (Primrec.snd.comp (Primrec.snd.comp b))
          (Primrec.not.comp (Primrec.snd.comp (Primrec.snd.comp b))))))

theorem exactOneGaugeFactor (source : PeriodicCNF V) (gauge : V → Cell) :
    LogicalFactor (PeriodicOneInThree.Satisfies source)
      (PeriodicOneInThree.Satisfies (source.variableGauge gauge)) (gaugeRead gauge) Set.univ := by
  constructor
  · intro a ha c clause member
    rw [gauge_decode]
    exact (PeriodicOneInThree.clauseHolds_push_variableGauge_iff gauge a c clause).2
      (ha c _ (List.mem_map.mpr ⟨clause,member,rfl⟩))
  · intro a ha
    refine ⟨pullVariableGaugeAssignment gauge a,?_,?_⟩
    · intro c clause member
      obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
      exact (PeriodicOneInThree.clauseHolds_variableGauge_pull_iff gauge a c original).2
        (ha c original originalMember)
    · intro v _ c
      simp [decode,gaugeRead,pullVariableGaugeAssignment,Cell.add,Cell.sub]

end LeanTrominoes.PeriodicCNF.SignedDecoder
