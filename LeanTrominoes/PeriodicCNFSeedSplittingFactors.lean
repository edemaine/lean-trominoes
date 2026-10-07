/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFSignedDecoderComposition
import LeanTrominoes.PeriodicThreeCNFSeed
import LeanTrominoes.PeriodicThreeSATThreeSeed

/-! # Local decoder certificates for clause and occurrence splitting -/
namespace LeanTrominoes
open PeriodicCNF.SignedDecoder

namespace PeriodicThreeCNF
variable {V : Type}

def seedRead (v : V) : PeriodicLiteral (ThreeCNFVariable V) := ⟨Sum.inl v,(0,0),true⟩

theorem seedRead_decode (a : ThreeCNFVariable V → Cell → Bool) :
    decode seedRead a = restrictAssignment a := by
  funext v c
  simp [decode,seedRead,restrictAssignment,Cell.add]

theorem seedFactor (source : PeriodicCNF V) : Factor source (formula source) seedRead Set.univ := by
  constructor
  · intro a ha
    rw [seedRead_decode]
    exact satisfies_of_threeCNF_satisfies source a ha
  · intro a ha
    refine ⟨extendAssignment a,threeCNF_satisfies_of_satisfies source a ha,?_⟩
    intro v _ c
    simp [decode,seedRead,extendAssignment,Cell.add]

theorem seedRead_primrec [Primcodable V] : Primrec (@seedRead V) :=
  PeriodicLiteral.equivData_symm_primrec.comp
    (Primrec.pair Primrec.sumInl (Primrec.const ((0,0),true)))

end PeriodicThreeCNF

namespace PeriodicThreeSATThree
variable {V : Type} [DecidableEq V]

def seedRead (source : PeriodicCNF V) (v : V) :
    PeriodicLiteral (ThreeOccurrenceVariable V) := ⟨seedCopy source v,(0,0),true⟩

theorem seedRead_decode_at (source : PeriodicCNF V)
    (a : ThreeOccurrenceVariable V → Cell → Bool) (v : V) (c : Cell) :
    decode (seedRead source) a v c = a (seedCopy source v) c := by
  simp [decode,seedRead,Cell.add]

/-- The unused-variable fallback reads a fresh unconstrained copy. Thus
prescriptions on unused variables are preserved as well. -/
theorem seedFactor (source : PeriodicCNF V) :
    Factor source (formula source) (seedRead source) Set.univ := by
  constructor
  · intro a ha c clause member
    obtain ⟨literal,literalMember,value⟩ := satisfies_of_formula_satisfies source a ha c clause member
    refine ⟨literal,literalMember,?_⟩
    have used := atom_mem_sourceVariables source member literalMember
    have equal := restrictAssignment_eq_copy source a ha literal.atom used
      (Cell.add c literal.offset) (seedCopy source literal.atom) (seedCopy_mem source literal.atom used)
    simpa only [PeriodicLiteral.Holds,seedRead_decode_at,equal] using value
  · intro a ha
    refine ⟨extendAssignment a,formula_satisfies_of_satisfies source a ha,?_⟩
    intro v _ c
    simp only [seedRead_decode_at,extendAssignment,seedCopy_fst]

theorem transportSeed_eq (source : PeriodicCNF V) (seed : PeriodicCNF.Seed V) :
    transportSeed (seedRead source) seed = liftSeed source seed := by
  unfold transportSeed liftSeed
  apply List.map_congr_left
  intro pin _
  simp [transportPin,seedRead,Cell.add]

theorem seeded_iff_all (source : PeriodicCNF V) (seed : PeriodicCNF.Seed V) :
    source.Seeded seed ↔ (formula source).Seeded (liftSeed source seed) := by
  rw [← transportSeed_eq]
  exact (seedFactor source).seeded_iff seed (fun _ _ => Set.mem_univ _)

theorem seedRead_primrec [Primcodable V] (source : PeriodicCNF V) : Primrec (seedRead source) :=
  PeriodicLiteral.equivData_symm_primrec.comp
    (Primrec.pair (seedCopy_primrec.comp (Primrec.const source) Primrec.id)
      (Primrec.const ((0,0),true)))

end PeriodicThreeSATThree
end LeanTrominoes
