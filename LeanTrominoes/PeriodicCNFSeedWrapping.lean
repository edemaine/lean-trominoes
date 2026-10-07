/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFSignedDecoderComposition
import LeanTrominoes.PeriodicCNFPlanarPeriodicizationComputability

/-! # Wrapping variable names preserves finite prescriptions -/
namespace LeanTrominoes.PeriodicCNF.SignedDecoder
open PeriodicOrthocrossing
variable {V : Type}

def wrapperRead (v : V) : PeriodicLiteral (WrappedPeriodicVariable V) := ⟨⟨v⟩,(0,0),true⟩

theorem wrapper_decode (a : WrappedPeriodicVariable V → Cell → Bool) :
    decode wrapperRead a = unwrapPeriodicPlanarSATAssignment a := by
  funext v c
  simp [decode,wrapperRead,unwrapPeriodicPlanarSATAssignment,Cell.add]

theorem wrapperFactor (source : PeriodicCNF V) :
    Factor source (wrapPeriodicPlanarSATFormula source) wrapperRead Set.univ := by
  constructor
  · intro a ha c clause member
    rw [wrapper_decode]
    exact (unwrap_wrapPeriodicPlanarSATClause_holds a c clause).1
      (ha c (wrapPeriodicPlanarSATClause clause) (List.mem_map.mpr ⟨clause,member,rfl⟩))
  · intro a ha
    refine ⟨wrapPeriodicPlanarSATAssignment a,?_,?_⟩
    · intro c clause member
      obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
      exact (wrapPeriodicPlanarSATClause_holds a c original).1 (ha c original originalMember)
    · intro v _ c
      simp [decode,wrapperRead,wrapPeriodicPlanarSATAssignment,Cell.add]

theorem wrapperRead_primrec [Primcodable V] : Primrec (@wrapperRead V) :=
  PeriodicLiteral.equivData_symm_primrec.comp
    (Primrec.pair WrappedPeriodicVariable.mk_primrec (Primrec.const ((0,0),true)))

end LeanTrominoes.PeriodicCNF.SignedDecoder
