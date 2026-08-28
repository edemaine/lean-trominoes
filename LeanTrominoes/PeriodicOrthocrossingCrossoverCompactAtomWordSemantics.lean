/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarCrossoverNormalizationDegree
import LeanTrominoes.PeriodicOrthocrossingCrossoverCompactAtomWordRetagSemantics

/-! # Exact compact atom words of one canonical crossover -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CrossoverCompactAtomWords

open PeriodicCNFStripReduction.DirectSourceFinalAtomWords
open PlanarThreeSAT

/-- One role decoration of the canonical left source pair is exactly the
compact atom word of that role at the same crossing. -/
theorem word_crossingPair
    {Variable : Type*}
    (sourceWord : Variable → List Bool)
    (crossing : CrossingRecord) (role : CrossoverVariable) :
    word role
        (true :: CarrierNodeSourceKeys.word
          (RetainedCompactAtomWords.crossingPair crossing)) =
      [RetainedCompactAtomWords.word sourceWord
        ⟨normalizedCrossoverAtom crossing role⟩] := by
  cases role <;>
    simp [word, internal?, sourceSide, sourceSideIncrement,
      RetainedCompactAtomWords.word, normalizedCrossoverAtom]
  all_goals first
    | exact retagFirstSegment_crossingPair crossing .left
    | exact retagFirstSegment_crossingPair crossing .top
    | exact retagFirstSegment_crossingPair crossing .bottom
    | exact retagFirstSegment_crossingPair crossing .right

/-- Expanding the fixed clause-major role list gives the exact flattened
compact atom-word block of Figure 8(b). -/
theorem wordsForRoles_crossingPair
    {Variable : Type*}
    (sourceWord : Variable → List Bool)
    (crossing : CrossingRecord) :
    wordsForRoles
        (true :: CarrierNodeSourceKeys.word
          (RetainedCompactAtomWords.crossingPair crossing)) =
      crossoverFormula.flatMap fun clause =>
        clause.literals.map fun literal =>
          RetainedCompactAtomWords.word sourceWord
            ⟨normalizedCrossoverAtom crossing literal.1⟩ := by
  unfold wordsForRoles roles
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro clause _clauseMember
  rcases clause with ⟨position, literals⟩
  rw [List.flatMap_map]
  change literals.flatMap (fun literal =>
      word literal.1
        (true :: CarrierNodeSourceKeys.word
          (RetainedCompactAtomWords.crossingPair crossing))) =
    literals.map fun literal =>
      RetainedCompactAtomWords.word sourceWord
        ⟨normalizedCrossoverAtom crossing literal.1⟩
  clear _clauseMember
  induction literals with
  | nil => rfl
  | cons literal literals induction =>
      rw [List.flatMap_cons, List.map_cons,
        word_crossingPair, induction]
      rfl

end CrossoverCompactAtomWords
end LeanTrominoes.PeriodicOrthocrossing
