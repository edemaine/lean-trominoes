/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.PeriodicCNFSeededCoRE
import LeanTrominoes.SAT.ThreeSAT.PeriodicThreeSATThreeCorrectness
import LeanTrominoes.SAT.ThreeSAT.PeriodicThreeSATThreeComputability

/-! # Occurrence splitting preserves finite prescriptions on used variables -/
namespace LeanTrominoes.PeriodicThreeSATThree
variable {V : Type} [DecidableEq V]

def seedCopy (source : PeriodicCNF V) (atom : V) : ThreeOccurrenceVariable V :=
  ((occurrenceVariables source atom).head?).getD (atom,0,0)

def liftSeed (source : PeriodicCNF V) (seed : PeriodicCNF.Seed V) :
    PeriodicCNF.Seed (ThreeOccurrenceVariable V) :=
  seed.map fun pin => ((seedCopy source pin.1.1,pin.1.2),pin.2)

def SupportedSeed (source : PeriodicCNF V) (seed : PeriodicCNF.Seed V) : Prop :=
  ∀ pin ∈ seed, pin.1.1 ∈ sourceVariables source

theorem atom_mem_sourceVariables (source : PeriodicCNF V)
    {clause : PeriodicClause V} (clauseMember : clause ∈ source.clauses)
    {literal : PeriodicLiteral V} (literalMember : literal ∈ clause) :
    literal.atom ∈ sourceVariables source := by
  have clauseIndexed : clause ∈ source.clauses.zipIdx.map Prod.fst := by
    simpa only [List.zipIdx_map_fst] using clauseMember
  obtain ⟨⟨stored,index⟩,storedMember,equal⟩ := List.mem_map.mp clauseIndexed
  simp only at equal
  subst stored
  have literalIndexed : literal ∈ clause.zipIdx.map Prod.fst := by
    simpa only [List.zipIdx_map_fst] using literalMember
  obtain ⟨⟨storedLiteral,literalIndex⟩,storedLiteralMember,equal⟩ :=
    List.mem_map.mp literalIndexed
  simp only at equal
  subst storedLiteral
  exact sourceVariables_mem source (taggedLiterals_mem source storedMember storedLiteralMember)

theorem seedCopy_mem (source : PeriodicCNF V) (atom : V)
    (used : atom ∈ sourceVariables source) : seedCopy source atom ∈ occurrenceVariables source atom := by
  simp only [sourceVariables,List.mem_dedup,List.mem_map] at used
  obtain ⟨tagged,member,equal⟩ := used
  have existsCopy := occurrenceVariables_mem source member
  rw [equal] at existsCopy
  cases copies : occurrenceVariables source atom with
  | nil => simp [copies] at existsCopy
  | cons first rest => simp [seedCopy,copies]

theorem seedCopy_fst (source : PeriodicCNF V) (atom : V) : (seedCopy source atom).1 = atom := by
  cases copies : occurrenceVariables source atom with
  | nil => simp [seedCopy,copies]
  | cons first rest =>
      have firstMem : first ∈ occurrenceVariables source atom := by simp [copies]
      simpa [seedCopy,copies] using occurrenceVariables_fst source atom firstMem

theorem seeded_iff (source : PeriodicCNF V) (seed : PeriodicCNF.Seed V)
    (supported : SupportedSeed source seed) :
    source.Seeded seed ↔ (formula source).Seeded (liftSeed source seed) := by
  constructor
  · rintro ⟨a,ha,pins⟩
    refine ⟨extendAssignment a,formula_satisfies_of_satisfies source a ha,?_⟩
    intro pin member
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp member
    simpa only [extendAssignment,seedCopy_fst] using pins p hp
  · rintro ⟨a,ha,pins⟩
    refine ⟨restrictAssignment source a,satisfies_of_formula_satisfies source a ha,?_⟩
    intro pin member
    rw [restrictAssignment_eq_copy source a ha pin.1.1 (supported pin member)
      pin.1.2 (seedCopy source pin.1.1) (seedCopy_mem source pin.1.1 (supported pin member))]
    exact pins _ (List.mem_map.mpr ⟨pin,member,rfl⟩)

theorem seedCopy_primrec [Primcodable V] : Primrec₂ (@seedCopy V _) :=
  Primrec.option_getD.comp (Primrec.list_head?.comp occurrenceVariables_primrec)
    (Primrec.pair Primrec.snd (Primrec.const (0,0)))

theorem liftSeed_primrec [Primcodable V] : Primrec₂ (@liftSeed V _) := by
  have pin : Primrec (fun a : PeriodicCNF V × PeriodicCNF.Seed V × ((V × Cell) × Bool) =>
      ((seedCopy a.1 a.2.2.1.1,a.2.2.1.2),a.2.2.2)) :=
    Primrec.pair (Primrec.pair
      (seedCopy_primrec.comp Primrec.fst (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_map Primrec.snd
    (pin.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)))

end LeanTrominoes.PeriodicThreeSATThree
