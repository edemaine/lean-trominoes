/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.PeriodicCNFSignedDecoderComposition
import LeanTrominoes.SAT.Planar.OccurrenceSplit.PeriodicEightOccurrenceSplit

/-! # Fixed-eight occurrence splitting preserves finite prescriptions -/
namespace LeanTrominoes.PeriodicEightOccurrenceSplit
open PeriodicCNF.SignedDecoder
variable {V : Type} [DecidableEq V]

def seedRead (v : V) : PeriodicLiteral (ThreeOccurrenceVariable V) := ⟨(v,8,0),(0,0),true⟩

omit [DecidableEq V] in
theorem seedRead_decode (a : ThreeOccurrenceVariable V → Cell → Bool) :
    decode seedRead a = restrictAssignment a := by
  funext v c
  simp [decode,seedRead,restrictAssignment,copies,OccurrenceSplitRing.cycleVertices,
    ringCopy,Cell.add]

theorem seedFactor (source : PeriodicCNF V) (ports : OccurrencePorts) :
    Factor source (formula source ports) seedRead Set.univ := by
  constructor
  · intro a ha
    rw [seedRead_decode]
    exact satisfies_of_formula_satisfies source ports a ha
  · intro a ha
    refine ⟨PeriodicThreeSATThree.extendAssignment a,
      formula_satisfies_of_satisfies source ports a ha,?_⟩
    intro v _ c
    simp [decode,seedRead,PeriodicThreeSATThree.extendAssignment,Cell.add]

theorem seeded_iff (source : PeriodicCNF V) (ports : OccurrencePorts) (seed : PeriodicCNF.Seed V) :
    source.Seeded seed ↔ (formula source ports).Seeded (transportSeed seedRead seed) :=
  (seedFactor source ports).seeded_iff seed (fun _ _ => Set.mem_univ _)

omit [DecidableEq V] in
theorem seedRead_primrec [Primcodable V] : Primrec (@seedRead V) :=
  PeriodicLiteral.equivData_symm_primrec.comp
    (Primrec.pair (Primrec.pair Primrec.id (Primrec.const (8,0))) (Primrec.const ((0,0),true)))

end LeanTrominoes.PeriodicEightOccurrenceSplit
