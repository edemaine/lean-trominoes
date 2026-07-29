import LeanTrominoes.PeriodicOneInThreeNoUnitsOriginalOccurrenceOrder
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceFanRouteOrder

/-!
# Transporting variable route order through exact-one transformations

Both exact-one transformations preserve the occurrence slot of every
inherited variable.  This file packages the remaining geometric obligation:
each paired output route must retain its source route's terminal direction.
Under that pointwise condition, clockwise variable-route order transports
through Figure 7 and through unit elimination.

Fresh auxiliaries need no separate angular argument: any variable reaching
the third slot is already known to be an embedded source variable.
-/

namespace LeanTrominoes

namespace PeriodicOneInThreePositioned

def PreservesOriginalRouteTerminalDirections
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourceRoutes outputRoutes :
      PositionedPeriodicCNF.IncidenceRoutes) : Prop :=
  ∀ atom output sourceOccurrence,
    (output, sourceOccurrence) ∈
        PeriodicOneInThree.formulaOriginalOccurrencePairs
          source.erase atom →
      AxisDirection.polylineLastDirection
          (outputRoutes output.2.1 output.2.2) =
        AxisDirection.polylineLastDirection
          (sourceRoutes sourceOccurrence.2.1 sourceOccurrence.2.2)

theorem variableRoutesInOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceRoutes outputRoutes :
      PositionedPeriodicCNF.IncidenceRoutes)
    (sourceOrder :
      source.VariableRoutesInOccurrenceOrder sourceRoutes)
    (preserved :
      PreservesOriginalRouteTerminalDirections
        source sourceRoutes outputRoutes) :
    (formula source).VariableRoutesInOccurrenceOrder outputRoutes := by
  intro outputAtom first second third
    firstLookup secondLookup thirdLookup
  change
    PeriodicOneInThreeToThreeDM.occurrenceAt
        (formula source).erase outputAtom .first =
      some first at firstLookup
  change
    PeriodicOneInThreeToThreeDM.occurrenceAt
        (formula source).erase outputAtom .second =
      some second at secondLookup
  change
    PeriodicOneInThreeToThreeDM.occurrenceAt
        (formula source).erase outputAtom .third =
      some third at thirdLookup
  have thirdLookupErased :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (PeriodicOneInThree.formula source.erase)
          outputAtom .third = some third := by
    simpa only [erase_formula] using thirdLookup
  rcases
      PeriodicOneInThree.exists_original_of_occurrenceAt_third
        source.erase outputAtom third thirdLookupErased with
    ⟨atom, rfl⟩
  have firstLookupErased :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (PeriodicOneInThree.formula source.erase)
          (Sum.inl atom) .first = some first := by
    simpa only [erase_formula] using firstLookup
  have secondLookupErased :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (PeriodicOneInThree.formula source.erase)
          (Sum.inl atom) .second = some second := by
    simpa only [erase_formula] using secondLookup
  rcases PeriodicOneInThree.exists_source_occurrenceAt
      source.erase sourceWidth atom .first first firstLookupErased with
    ⟨sourceFirst, sourceFirstLookup, firstPair⟩
  rcases PeriodicOneInThree.exists_source_occurrenceAt
      source.erase sourceWidth atom .second second secondLookupErased with
    ⟨sourceSecond, sourceSecondLookup, secondPair⟩
  rcases PeriodicOneInThree.exists_source_occurrenceAt
      source.erase sourceWidth atom .third third thirdLookupErased with
    ⟨sourceThird, sourceThirdLookup, thirdPair⟩
  have clockwise :=
    sourceOrder atom sourceFirst sourceSecond sourceThird
      sourceFirstLookup sourceSecondLookup sourceThirdLookup
  rw [preserved atom first sourceFirst firstPair,
    preserved atom second sourceSecond secondPair,
    preserved atom third sourceThird thirdPair]
  exact clockwise

end PeriodicOneInThreePositioned

namespace PeriodicOneInThreeNoUnitsPositioned

def PreservesOriginalRouteTerminalDirections
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourceRoutes outputRoutes :
      PositionedPeriodicCNF.IncidenceRoutes) : Prop :=
  ∀ atom output sourceOccurrence,
    (output, sourceOccurrence) ∈
        PeriodicOneInThreeNoUnits.formulaOriginalOccurrencePairs
          source.erase atom →
      AxisDirection.polylineLastDirection
          (outputRoutes output.2.1 output.2.2) =
        AxisDirection.polylineLastDirection
          (sourceRoutes sourceOccurrence.2.1 sourceOccurrence.2.2)

theorem variableRoutesInOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourceRoutes outputRoutes :
      PositionedPeriodicCNF.IncidenceRoutes)
    (sourceOrder :
      source.VariableRoutesInOccurrenceOrder sourceRoutes)
    (preserved :
      PreservesOriginalRouteTerminalDirections
        source sourceRoutes outputRoutes) :
    (formula source).VariableRoutesInOccurrenceOrder outputRoutes := by
  intro outputAtom first second third
    firstLookup secondLookup thirdLookup
  change
    PeriodicOneInThreeToThreeDM.occurrenceAt
        (formula source).erase outputAtom .first =
      some first at firstLookup
  change
    PeriodicOneInThreeToThreeDM.occurrenceAt
        (formula source).erase outputAtom .second =
      some second at secondLookup
  change
    PeriodicOneInThreeToThreeDM.occurrenceAt
        (formula source).erase outputAtom .third =
      some third at thirdLookup
  have thirdLookupErased :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (PeriodicOneInThreeNoUnits.formula source.erase)
          outputAtom .third = some third := by
    simpa only [erase_formula] using thirdLookup
  rcases
      PeriodicOneInThreeNoUnits.exists_original_of_occurrenceAt_third
        source.erase outputAtom third thirdLookupErased with
    ⟨atom, rfl⟩
  have firstLookupErased :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (PeriodicOneInThreeNoUnits.formula source.erase)
          (Sum.inl atom) .first = some first := by
    simpa only [erase_formula] using firstLookup
  have secondLookupErased :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (PeriodicOneInThreeNoUnits.formula source.erase)
          (Sum.inl atom) .second = some second := by
    simpa only [erase_formula] using secondLookup
  rcases PeriodicOneInThreeNoUnits.exists_source_occurrenceAt
      source.erase atom .first first firstLookupErased with
    ⟨sourceFirst, sourceFirstLookup, firstPair⟩
  rcases PeriodicOneInThreeNoUnits.exists_source_occurrenceAt
      source.erase atom .second second secondLookupErased with
    ⟨sourceSecond, sourceSecondLookup, secondPair⟩
  rcases PeriodicOneInThreeNoUnits.exists_source_occurrenceAt
      source.erase atom .third third thirdLookupErased with
    ⟨sourceThird, sourceThirdLookup, thirdPair⟩
  have clockwise :=
    sourceOrder atom sourceFirst sourceSecond sourceThird
      sourceFirstLookup sourceSecondLookup sourceThirdLookup
  rw [preserved atom first sourceFirst firstPair,
    preserved atom second sourceSecond secondPair,
    preserved atom third sourceThird thirdPair]
  exact clockwise

end PeriodicOneInThreeNoUnitsPositioned

end LeanTrominoes
