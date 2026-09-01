/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalBendDirectChoiceFallback
import LeanTrominoes.RetainedAngularFanFinalBendIndexedOccurrence
import LeanTrominoes.RetainedAngularFinalRouteDecidableEqIrrelevance

/-! # Direct-choice rejection for indexed final retained bends -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicOrthocrossing
open PeriodicThreeSATThree

attribute [local instance]
  finalBendIndexedOccurrenceThreeOccurrenceDecidableEq

private def FinalBendIndexedOccurrence.taggedBendInput
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) :
    FinalBendTaggedBendInput occurrence.source occurrence.taggedBend
      occurrence.clauseIndex :=
  { sourceInput :=
      { sourceFacts :=
          { nonemptyFacts :=
              { widthFacts :=
                  { localFacts :=
                      { sourceLocal := occurrence.sourceLocal }
                    sourceWidth := occurrence.sourceWidth }
                sourceClausesNonempty := occurrence.sourceClausesNonempty }
            positiveOffsets := occurrence.positiveOffsets } }
    taggedBendIndexed := occurrence.taggedBendIndexed }

/-- Every indexed final retained-bend occurrence takes the fallback router. -/
theorem FinalBendIndexedOccurrence.routeChoice_eq_none
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) :
    retainedFinalDirectSourceRouteChoice? occurrence.retained
        occurrence.clauseIndex occurrence.literalIndex = none := by
  have rejected := occurrence.taggedBendInput.routeChoice_eq_none
    occurrence.literalIndex.val
  change retainedFinalDirectSourceRouteChoice?
      (PeriodicThreeSATThree.formula occurrence.source)
        occurrence.clauseIndex occurrence.literalIndex.val = none
  have choiceIrrel := decidableEq_application_irrel
    (fun equality : DecidableEq (ThreeOccurrenceVariable Variable) =>
      @retainedFinalDirectSourceRouteChoice?
        (ThreeOccurrenceVariable Variable) equality
        (PeriodicThreeSATThree.formula occurrence.source)
        occurrence.clauseIndex occurrence.literalIndex.val)
    finalBendDirectChoiceThreeOccurrenceDecidableEq
    finalBendIndexedOccurrenceThreeOccurrenceDecidableEq
  exact choiceIrrel.symm.trans rejected

end PeriodicEightOccurrenceSplit
end LeanTrominoes
