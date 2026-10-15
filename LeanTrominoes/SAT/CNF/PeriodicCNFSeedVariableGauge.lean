/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.PeriodicCNFSignedDecoderComposition
import LeanTrominoes.SAT.Planar.PositionedPeriodicCNFVariableGauge

/-! # Variable gauges preserve finite prescriptions at the shifted cells -/
namespace LeanTrominoes.PeriodicCNF.SignedDecoder
variable {V : Type}

def gaugeRead (gauge : V → Cell) (v : V) : PeriodicLiteral V := ⟨v,gauge v,true⟩

theorem gauge_decode (gauge : V → Cell) (a : V → Cell → Bool) :
    decode (gaugeRead gauge) a = pushVariableGaugeAssignment gauge a := by
  funext v c
  rfl

theorem gaugeFactor (source : PeriodicCNF V) (gauge : V → Cell) :
    Factor source (source.variableGauge gauge) (gaugeRead gauge) Set.univ := by
  constructor
  · intro a ha c clause member
    obtain ⟨l,hl,value⟩ := ha c (clause.variableGauge gauge) (List.mem_map.mpr ⟨clause,member,rfl⟩)
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp hl
    refine ⟨original,originalMember,?_⟩
    rw [gauge_decode]
    exact (PeriodicCNF.literal_holds_pushVariableGaugeAssignment_iff gauge a c original).2 value
  · intro a ha
    refine ⟨pullVariableGaugeAssignment gauge a,?_,?_⟩
    · intro c clause member
      obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
      obtain ⟨l,hl,value⟩ := ha c original originalMember
      exact ⟨l.variableGauge gauge,List.mem_map.mpr ⟨l,hl,rfl⟩,
        (PeriodicCNF.variableGauge_literal_holds_iff gauge a c l).2 value⟩
    · intro v _ c
      simp [decode,gaugeRead,pullVariableGaugeAssignment,Cell.add,Cell.sub]

theorem gaugeRead_primrec [Primcodable V] {gauge : V → Cell} (computed : Primrec gauge) :
    Primrec (gaugeRead gauge) :=
  PeriodicLiteral.equivData_symm_primrec.comp
    (Primrec.pair Primrec.id (Primrec.pair computed (Primrec.const true)))

theorem Factor.congrTarget {W : Type} {source : PeriodicCNF V} {target other : PeriodicCNF W}
    {read : Read V W} {support : Set V} (factor : Factor source target read support)
    (same : ∀ a, target.Satisfies a ↔ other.Satisfies a) :
    Factor source other read support := by
  constructor
  · intro a ha
    exact factor.sound a ((same a).2 ha)
  · intro a ha
    obtain ⟨b,hb,inverse⟩ := factor.complete a ha
    exact ⟨b,(same b).1 hb,inverse⟩

end LeanTrominoes.PeriodicCNF.SignedDecoder
