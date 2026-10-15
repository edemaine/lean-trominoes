/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.PeriodicCNFSeededCoRE
import LeanTrominoes.SAT.ThreeSAT.PeriodicThreeCNFCorrectness
import LeanTrominoes.SAT.ThreeSAT.PeriodicThreeCNFComputability

/-! # Clause splitting preserves finite prescriptions -/
namespace LeanTrominoes.PeriodicThreeCNF
variable {V : Type}

def liftSeed (seed : PeriodicCNF.Seed V) : PeriodicCNF.Seed (ThreeCNFVariable V) :=
  seed.map fun pin => (((Sum.inl pin.1.1),pin.1.2),pin.2)

theorem seeded_iff (source : PeriodicCNF V) (seed : PeriodicCNF.Seed V) :
    source.Seeded seed ↔ (formula source).Seeded (liftSeed seed) := by
  constructor
  · rintro ⟨a,ha,pins⟩
    refine ⟨extendAssignment a,threeCNF_satisfies_of_satisfies source a ha,?_⟩
    intro pin member
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp member
    exact pins p hp
  · rintro ⟨a,ha,pins⟩
    refine ⟨restrictAssignment a,satisfies_of_threeCNF_satisfies source a ha,?_⟩
    intro pin member
    exact pins _ (List.mem_map.mpr ⟨pin,member,rfl⟩)

theorem liftSeed_primrec [Primcodable V] : Primrec (@liftSeed V) :=
  Primrec.list_map Primrec.id
    (Primrec.pair (Primrec.pair
      (Primrec.sumInl.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd))

end LeanTrominoes.PeriodicThreeCNF
