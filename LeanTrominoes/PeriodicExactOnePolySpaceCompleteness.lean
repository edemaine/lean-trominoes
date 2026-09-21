/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOneInThreePolyTimeCompiler
import LeanTrominoes.PeriodicOneInThreePolyTimeSemantics
import LeanTrominoes.PeriodicExactOneThreePolySpaceMembership

/-! # Native flat-encoded PSPACE-completeness of local 1D exact-one SAT -/
noncomputable section
namespace LeanTrominoes.PeriodicOneInThree.PolyTime
open Turing PeriodicCNF
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance exactOneCompletenessStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable def reductionComputableInPolyTime :
    TM2ComputableInPolyTime encoding.encode PeriodicCNFFlatEncoding.finEncoding.encode (reduction decider) :=
  TM2PolyTimeInputEncodingTransport.of_prepare encoding.encode (formulaComputableInPolyTime decider)
    (fun _ => rfl) (fun _ => rfl)

theorem reduction_occurrences (input : Input) : (reduction decider input).OccurrencesAtMost 3 :=
  Numeric.occurrences_three _
    (PeriodicThreeSATThree.Numeric.width_three _
      (PeriodicCNFStripReduction.formulaOfSymbols_widthAtMostThree decider (encoding.encode input)))
    (PeriodicThreeSATThree.Numeric.occurrences_three _)

theorem reduction_correct_without_occurrence_bound (input : Input) :
    language input ↔ PeriodicExactOneCNF.LocalOneDimensionalThreeSAT (reduction decider input) := by
  rw [reduction_correct decider input]
  exact and_iff_right (reduction_occurrences decider input)

include decider in
theorem manyOneThree : Complexity.PolyTimeManyOneReducible encoding PeriodicCNFFlatEncoding.finEncoding
    language PeriodicExactOneCNF.LocalOneDimensionalThreeSATThree := by
  refine ⟨reduction decider,?_,reduction_correct decider⟩
  exact ⟨Complexity.FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime
    (reductionComputableInPolyTime decider)⟩

include decider in
theorem manyOne : Complexity.PolyTimeManyOneReducible encoding PeriodicCNFFlatEncoding.finEncoding
    language PeriodicExactOneCNF.LocalOneDimensionalThreeSAT := by
  refine ⟨reduction decider,?_,reduction_correct_without_occurrence_bound decider⟩
  exact ⟨Complexity.FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime
    (reductionComputableInPolyTime decider)⟩

end LeanTrominoes.PeriodicOneInThree.PolyTime

namespace LeanTrominoes.PeriodicExactOneCNF

theorem localOneDimensionalThreeSAT_PSPACEHard :
    Complexity.PSPACEHard PeriodicCNFFlatEncoding.finEncoding LocalOneDimensionalThreeSAT := by
  intro Input encoding language h
  obtain ⟨decider⟩ := h
  exact PeriodicOneInThree.PolyTime.manyOne decider

theorem localOneDimensionalThreeSATThree_PSPACEHard :
    Complexity.PSPACEHard PeriodicCNFFlatEncoding.finEncoding LocalOneDimensionalThreeSATThree := by
  intro Input encoding language h
  obtain ⟨decider⟩ := h
  exact PeriodicOneInThree.PolyTime.manyOneThree decider

theorem localOneDimensionalThreeSAT_PSPACEComplete :
    Complexity.PSPACEComplete PeriodicCNFFlatEncoding.finEncoding LocalOneDimensionalThreeSAT :=
  ⟨localOneDimensionalThreeSAT_inPSPACE,localOneDimensionalThreeSAT_PSPACEHard⟩

theorem localOneDimensionalThreeSATThree_PSPACEComplete :
    Complexity.PSPACEComplete PeriodicCNFFlatEncoding.finEncoding LocalOneDimensionalThreeSATThree :=
  ⟨localOneDimensionalThreeSATThree_inPSPACE,localOneDimensionalThreeSATThree_PSPACEHard⟩

end LeanTrominoes.PeriodicExactOneCNF
