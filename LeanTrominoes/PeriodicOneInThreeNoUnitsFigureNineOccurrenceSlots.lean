/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineInheritedEndpoints
import LeanTrominoes.PeriodicOneInThreeVariableRouteOrderTransport

/-!
# Occurrence slots of twice-inherited Figure 9 incidences

The composed endpoint provenance stores one original-occurrence pair from
each exact-one transformation.  Composing those pairs shows that its recovered
source occurrence occupies the same presentation-order slot as the final
generated occurrence.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

private theorem occurrenceAt_eq_of_decidableEq
    {Variable : Type*}
    (firstEq secondEq : DecidableEq Variable)
    (source : PeriodicCNF Variable)
    (atom : Variable)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot) :
    @PeriodicOneInThreeToThreeDM.occurrenceAt
        Variable firstEq source atom slot =
      @PeriodicOneInThreeToThreeDM.occurrenceAt
        Variable secondEq source atom slot := by
  have equality : firstEq = secondEq := by
    funext first second
    exact Subsingleton.elim _ _
  cases equality
  rfl

private theorem pair_eq_of_mem_of_mem_of_fst_eq
    {First Second : Type*}
    (pairs : List (First × Second))
    (fstNodup : (pairs.map Prod.fst).Nodup)
    {first second : First × Second}
    (firstMember : first ∈ pairs)
    (secondMember : second ∈ pairs)
    (fstEq : first.1 = second.1) :
    first = second := by
  have pairsNodup : pairs.Nodup := fstNodup.of_map Prod.fst
  exact
    ((List.nodup_map_iff_inj_on pairsNodup).mp fstNodup)
      first firstMember second secondMember fstEq

/-- A variable of the twice-transformed formula that reaches the third
occurrence slot is inherited from the original formula through both layers. -/
theorem exists_sourceAtom_of_occurrenceAt_third
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (finalEq :
      DecidableEq
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable)))
    (outputAtom :
      OneInThreeNoUnitVariable (OneInThreeVariable Variable))
    (third :
      PeriodicOneInThreeToThreeDM.TaggedOccurrence
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable)))
    (lookup :
      @PeriodicOneInThreeToThreeDM.occurrenceAt
          (OneInThreeNoUnitVariable (OneInThreeVariable Variable))
          finalEq
          (PeriodicOneInThreeNoUnits.formula
            (PeriodicOneInThree.formula source))
          outputAtom .third = some third) :
    ∃ sourceAtom : Variable,
      outputAtom = .inl (.inl sourceAtom) := by
  letI : DecidableEq (OneInThreeVariable Variable) := inferInstance
  rcases
      PeriodicOneInThreeNoUnits.exists_original_of_occurrenceAt_third
        (PeriodicOneInThree.formula source) outputAtom third
        (by
          rw [occurrenceAt_eq_of_decidableEq _ finalEq
            (PeriodicOneInThreeNoUnits.formula
              (PeriodicOneInThree.formula source))
            outputAtom .third]
          exact lookup) with
    ⟨figureAtom, outputAtomEq⟩
  subst outputAtom
  rcases PeriodicOneInThreeNoUnits.exists_source_occurrenceAt
      (PeriodicOneInThree.formula source) figureAtom .third third
      (by
        rw [occurrenceAt_eq_of_decidableEq _ finalEq
          (PeriodicOneInThreeNoUnits.formula
            (PeriodicOneInThree.formula source))
          (.inl figureAtom) .third]
        exact lookup) with
    ⟨figureThird, figureThirdLookup, _thirdPair⟩
  rcases
      PeriodicOneInThree.exists_original_of_occurrenceAt_third
        source figureAtom figureThird figureThirdLookup with
    ⟨sourceAtom, figureAtomEq⟩
  subst figureAtom
  exact ⟨sourceAtom, rfl⟩

/-- A twice-inherited endpoint provenance record recovers the source
occurrence in exactly the same occurrence slot as its final incidence. -/
theorem InheritedEndpointProvenance.sourceOccurrenceAt
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    {clauseIndex literalIndex : Nat}
    (data :
      InheritedEndpointProvenance
        source sourcePlacement clauseIndex literalIndex)
    (finalEq :
      DecidableEq
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable)))
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot)
    (finalLookup :
      @PeriodicOneInThreeToThreeDM.occurrenceAt
          (OneInThreeNoUnitVariable (OneInThreeVariable Variable))
          finalEq
          (PeriodicOneInThreeNoUnits.formula
            (PeriodicOneInThree.formula source.erase))
          data.generatedLiteral.atom slot =
        some (data.generatedLiteral, clauseIndex, literalIndex)) :
    PeriodicOneInThreeToThreeDM.occurrenceAt
        source.erase data.sourceLiteral.atom slot =
      some
        (data.sourceLiteral, data.sourceClauseIndex,
          data.sourceLiteralIndex) := by
  letI : DecidableEq (OneInThreeVariable Variable) := inferInstance
  let standardFinalEq :
      DecidableEq
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable)) :=
    fun first second => instDecidableEqSum first second
  have finalAtom :
      data.generatedLiteral.atom = .inl data.figureNineLiteral.atom :=
    data.generatedLiteralAtom
  have finalLookup' :
      @PeriodicOneInThreeToThreeDM.occurrenceAt
          (OneInThreeNoUnitVariable (OneInThreeVariable Variable))
          finalEq
          (PeriodicOneInThreeNoUnits.formula
            (PeriodicOneInThree.formula source.erase))
          (.inl data.figureNineLiteral.atom) slot =
        some (data.generatedLiteral, clauseIndex, literalIndex) := by
    simpa [finalAtom] using finalLookup
  rcases PeriodicOneInThreeNoUnits.exists_source_occurrenceAt
      (PeriodicOneInThree.formula source.erase)
      data.figureNineLiteral.atom slot
      (data.generatedLiteral, clauseIndex, literalIndex)
      (by
        rw [
          occurrenceAt_eq_of_decidableEq
            _ finalEq
            (PeriodicOneInThreeNoUnits.formula
              (PeriodicOneInThree.formula source.erase))
            (.inl data.figureNineLiteral.atom) slot]
        exact finalLookup') with
    ⟨figureOccurrence, figureLookup, unitPair⟩
  let unitPairs :=
    PeriodicOneInThreeNoUnits.formulaOriginalOccurrencePairs
      (PeriodicOneInThree.formula source.erase)
      data.figureNineLiteral.atom
  have dataUnitPair :
      ((data.generatedLiteral, clauseIndex, literalIndex),
        (data.figureNineLiteral,
          data.unitMetadata.sourceClauseIndex,
          data.figureNineLiteralIndex)) ∈ unitPairs := by
    simpa [unitPairs, PeriodicOneInThreePositioned.erase_formula] using
      data.unitOriginalOccurrencePair
  have unitPairsFstNodup : (unitPairs.map Prod.fst).Nodup := by
    rw [show unitPairs.map Prod.fst = _ by
      simpa [unitPairs] using
        PeriodicOneInThreeNoUnits.formulaOriginalOccurrencePairs_fst
          (PeriodicOneInThree.formula source.erase)
          data.figureNineLiteral.atom]
    exact
      @PeriodicOneInThreeToThreeDM.occurrencesOf_nodup
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable))
        standardFinalEq _ _
  have unitPairEq :=
    pair_eq_of_mem_of_mem_of_fst_eq unitPairs unitPairsFstNodup
      dataUnitPair unitPair rfl
  have figureOccurrenceEq :
      (data.figureNineLiteral,
          data.unitMetadata.sourceClauseIndex,
          data.figureNineLiteralIndex) = figureOccurrence :=
    congrArg Prod.snd unitPairEq
  have figureLookup' :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (PeriodicOneInThree.formula source.erase)
          (.inl data.sourceLiteral.atom) slot =
        some
          (data.figureNineLiteral,
            data.unitMetadata.sourceClauseIndex,
            data.figureNineLiteralIndex) := by
    rw [← data.figureNineLiteralAtom]
    simpa [figureOccurrenceEq] using figureLookup
  rcases PeriodicOneInThree.exists_source_occurrenceAt
      source.erase sourceWidth data.sourceLiteral.atom slot
      (data.figureNineLiteral,
        data.unitMetadata.sourceClauseIndex,
        data.figureNineLiteralIndex)
      figureLookup' with
    ⟨sourceOccurrence, sourceLookup, figurePair⟩
  let figurePairs :=
    PeriodicOneInThree.formulaOriginalOccurrencePairs
      source.erase data.sourceLiteral.atom
  have dataFigurePair :
      ((data.figureNineLiteral,
          data.unitMetadata.sourceClauseIndex,
          data.figureNineLiteralIndex),
        (data.sourceLiteral, data.sourceClauseIndex,
          data.sourceLiteralIndex)) ∈ figurePairs := by
    simpa [figurePairs] using data.figureNineOriginalOccurrencePair
  have figurePairsFstNodup : (figurePairs.map Prod.fst).Nodup := by
    rw [show
      figurePairs.map Prod.fst =
        PeriodicOneInThreeToThreeDM.occurrencesOf
          (PeriodicOneInThree.formula source.erase)
          (.inl data.sourceLiteral.atom) by
      simpa [figurePairs] using
        PeriodicOneInThree.formulaOriginalOccurrencePairs_fst
          source.erase data.sourceLiteral.atom]
    exact PeriodicOneInThreeToThreeDM.occurrencesOf_nodup _ _
  have figurePairEq :=
    pair_eq_of_mem_of_mem_of_fst_eq figurePairs figurePairsFstNodup
      dataFigurePair figurePair rfl
  have sourceOccurrenceEq :
      (data.sourceLiteral, data.sourceClauseIndex,
          data.sourceLiteralIndex) = sourceOccurrence :=
    congrArg Prod.snd figurePairEq
  simpa [sourceOccurrenceEq] using sourceLookup

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
