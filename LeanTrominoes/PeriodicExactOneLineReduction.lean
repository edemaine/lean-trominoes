/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATLineReduction
import LeanTrominoes.PeriodicExactOneCNFLocality

/-! # Total reductions to local one-dimensional exact-one SAT

Forgetting the supplied planar drawing gives the ordinary exact-one and
occurrence-three exact-one languages. This module proves semantic and
primitive-recursive correctness, independently of encoded time bounds.
-/
noncomputable section
namespace LeanTrominoes.PeriodicExactOneCNF.LineReduction
open PeriodicPlanarSAT PeriodicCNFStripReduction
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 2048
local instance exactOneLineSourceDecidableEq : DecidableEq Variable := Classical.decEq _
abbrev Target := ExactOneEndpoint.Target Variable
local instance exactOneLineTargetDecidableEq : DecidableEq Target :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

def reduction (f : PeriodicCNF Nat) : PeriodicCNF Target :=
  (PeriodicPlanarSAT.LineReduction.exactOne f).1

theorem reduction_primrec : Primrec reduction :=
  Primrec.fst.comp PeriodicPlanarSAT.LineReduction.exactOne_primrec

theorem correct (f : PeriodicCNF Nat) :
    PeriodicCNF.LocalPeriodicCNF1DSAT f ↔ LocalOneDimensionalThreeSAT (reduction f) := by
  have full := PeriodicPlanarSAT.LineReduction.exactOne_correct f
  constructor
  · intro h
    obtain ⟨horizontal,_,locality,valid,_,sat⟩ := full.1 h
    exact ⟨valid.1,horizontal,locality,sat⟩
  · rintro ⟨_,_,_,sat⟩
    apply (sourceFormula_correct f).2
    exact (ExactOneEndpoint.correct (sourceFormula f)
      (sourceFormula_isLocal f) (sourceFormula_widthAtMostThree f)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq f)
      (sourceFormula_clausesNonempty f)).1 sat

theorem threeOccurrence_correct (f : PeriodicCNF Nat) :
    PeriodicCNF.LocalPeriodicCNF1DSAT f ↔ LocalOneDimensionalThreeSATThree (reduction f) := by
  constructor
  · intro h
    have full := (PeriodicPlanarSAT.LineReduction.exactOneThreeOccurrence_correct f).1 h
    exact ⟨PeriodicCNF.occurrencesAtMost_congr_beq _ _ _ _ 3 _ full.2.2.2.1,(correct f).1 h⟩
  · intro h
    exact (correct f).2 h.2
end LeanTrominoes.PeriodicExactOneCNF.LineReduction
