/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOneInThreePolyTimeProfiles
import LeanTrominoes.PeriodicThreeSATThreePolySpaceCompleteness
import LeanTrominoes.PeriodicExactOneCNFLocality

/-! # Numeric exact-one reduction semantics for every PSPACE source

This connects the compact numeric formula to the original language. The
polynomial-time compiler and completeness endpoints build on this equivalence.
-/
noncomputable section
namespace LeanTrominoes.PeriodicOneInThree.PolyTime
open PeriodicCNF
set_option maxHeartbeats 1000000
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance exactOneSemanticsStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

def reduction (input : Input) : PeriodicCNF Nat := formula decider (encoding.encode input)

private theorem numeric_correct (source : PeriodicCNF Nat) (hw : source.WidthAtMost 3)
    (ho : source.OccurrencesAtMost 3) (hf : source.IsForwardLocal) :
    PeriodicExactOneCNF.LocalOneDimensionalThreeSATThree (Numeric.formula source) ↔ source.Satisfiable := by
  have forward := Numeric.forward source hf
  have horizontal := isOneDimensional_of_isForwardLocal forward
  have locality := (isLocal_iff_isLocalOnLine horizontal).mpr (isLocalOnLine_of_isForwardLocal forward)
  simp only [PeriodicExactOneCNF.LocalOneDimensionalThreeSATThree,
    PeriodicExactOneCNF.LocalOneDimensionalThreeSAT,PeriodicExactOneCNF.LocalOneDimensionalSAT,
    Numeric.occurrences_three source hw ho,Numeric.width_three,horizontal,locality,true_and]
  exact Numeric.satisfiable_iff source hw

theorem reduction_correct (input : Input) :
    language input ↔ PeriodicExactOneCNF.LocalOneDimensionalThreeSATThree (reduction decider input) := by
  let symbols := encoding.encode input
  let base := PolySpaceCompiler.formulaOfSymbols decider symbols
  have sourceForward : (source decider symbols).IsForwardLocal :=
    PeriodicThreeSATThree.Numeric.forward base
      (PeriodicCNFStripReduction.formulaOfSymbols_isForwardLocal decider symbols)
  have sourceWidth : (source decider symbols).WidthAtMost 3 :=
    PeriodicThreeSATThree.Numeric.width_three base
      (PeriodicCNFStripReduction.formulaOfSymbols_widthAtMostThree decider symbols)
  have sourceOccurrences : (source decider symbols).OccurrencesAtMost 3 :=
    PeriodicThreeSATThree.Numeric.occurrences_three base
  have horizontal := isOneDimensional_of_isForwardLocal sourceForward
  have locality := isLocalOnLine_of_isForwardLocal sourceForward
  have accepted : language input ↔ LocalPeriodicThreeSATThree1DSAT (source decider symbols) :=
    PeriodicThreeSATThree.PolyTime.reduction_correct decider input
  have logic : LocalPeriodicThreeSATThree1DSAT (source decider symbols) ↔
      (source decider symbols).Satisfiable := by
    simp only [LocalPeriodicThreeSATThree1DSAT,LocalPeriodicThreeCNF1DSAT,
      LocalPeriodicCNF1DSAT,sourceOccurrences,sourceWidth,horizontal,locality,true_and]
    exact (satisfiable_iff_satisfiableOnLine horizontal).symm
  exact accepted.trans (logic.trans (numeric_correct _ sourceWidth sourceOccurrences sourceForward).symm)
end LeanTrominoes.PeriodicOneInThree.PolyTime
