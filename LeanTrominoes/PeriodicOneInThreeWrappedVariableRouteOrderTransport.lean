/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarFixedEightOneInThreeVariableRouteOrder
import LeanTrominoes.PositionedPeriodicCNFVariableRouteOrderRenaming

/-!
# Variable route order through the opaque Figure 9 wrapper

The logical hardness pipeline puts the clause-scoped Figure 9 variable type
behind a one-field opaque wrapper before eliminating unit clauses.  This file
packages the generic route-order and third-occurrence transport needed by
both the ordinary and retained fixed-eight pipelines.

The helper conclusions use classical equality on newly nested output types.
Keeping the source type abstract makes their later specializations cheap;
the exported concrete theorems can then transfer back to any lawful
decidable equality.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

/-- Figure 9 route-order transport composes with an opaque variable wrapper
when the wrapped occurrence lookup uses inexpensive classical equality. -/
theorem
    PeriodicOneInThreePositioned.variableRoutesInOccurrenceOrder_renameWrapped_classical
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceRoutes outputRoutes :
      PositionedPeriodicCNF.IncidenceRoutes)
    (sourceOrder :
      source.VariableRoutesInOccurrenceOrder sourceRoutes)
    (preserved :
      PeriodicOneInThreePositioned.PreservesOriginalRouteTerminalDirections
        source sourceRoutes outputRoutes) :
    @PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
      (WrappedPeriodicVariable (OneInThreeVariable Variable))
      (Classical.decEq _)
      ((PeriodicOneInThreePositioned.formula source).rename
        WrappedPeriodicVariable.mk)
      outputRoutes := by
  apply
    @PositionedPeriodicCNF.variableRoutesInOccurrenceOrder_rename
      (OneInThreeVariable Variable)
      (WrappedPeriodicVariable (OneInThreeVariable Variable))
      (Classical.decEq _) (Classical.decEq _)
      (PeriodicOneInThreePositioned.formula source)
      outputRoutes
      WrappedPeriodicVariable.mk WrappedPeriodicVariable.original
  · intro atom
    rfl
  · intro atom
    cases atom
    rfl
  · apply
      @PositionedPeriodicCNF.variableRoutesInOccurrenceOrder_of_decidableEq
        (OneInThreeVariable Variable)
        (inferInstance) (Classical.decEq _)
        (PeriodicOneInThreePositioned.formula source)
        outputRoutes
    exact
      PeriodicOneInThreePositioned.variableRoutesInOccurrenceOrder
        source sourceWidth sourceRoutes outputRoutes sourceOrder preserved

/-- A wrapped Figure 9 variable with a third occurrence is the wrapper of
an embedded source variable, not a fresh Figure 9 auxiliary. -/
theorem
    PeriodicOneInThreePositioned.exists_original_of_wrapped_occurrenceAt_third
    {Variable : Type*} [DecidableEq Variable]
    (rawEq : DecidableEq (OneInThreeVariable Variable))
    (wrappedEq :
      DecidableEq
        (WrappedPeriodicVariable (OneInThreeVariable Variable)))
    (source : PositionedPeriodicCNF Variable)
    (wrappedAtom :
      WrappedPeriodicVariable (OneInThreeVariable Variable))
    (third :
      PeriodicOneInThreeToThreeDM.TaggedOccurrence
        (WrappedPeriodicVariable (OneInThreeVariable Variable)))
    (thirdLookup :
      @PeriodicOneInThreeToThreeDM.occurrenceAt
          (WrappedPeriodicVariable (OneInThreeVariable Variable))
          wrappedEq
          ((PeriodicOneInThreePositioned.formula source).rename
            WrappedPeriodicVariable.mk).erase
          wrappedAtom .third = some third) :
    ∃ atom : Variable, wrappedAtom.original = .inl atom := by
  have wrapperInjective :
      Function.Injective
        (@WrappedPeriodicVariable.mk
          (OneInThreeVariable Variable)) :=
    fun _first _second equal =>
      congrArg WrappedPeriodicVariable.original equal
  rw [show wrappedAtom =
        WrappedPeriodicVariable.mk wrappedAtom.original by
      cases wrappedAtom
      rfl,
    (@PositionedPeriodicCNF.occurrenceAt_rename
      (OneInThreeVariable Variable)
      (WrappedPeriodicVariable (OneInThreeVariable Variable))
      rawEq wrappedEq
      (PeriodicOneInThreePositioned.formula source)
      WrappedPeriodicVariable.mk wrapperInjective)]
    at thirdLookup
  rcases Option.map_eq_some_iff.mp thirdLookup with
    ⟨rawThird, rawThirdLookup, _thirdEqual⟩
  apply
    PeriodicOneInThree.exists_original_of_occurrenceAt_third
      source.erase wrappedAtom.original rawThird
  rw [←
    PeriodicEightOccurrenceSplitPositioned.occurrenceAt_eq_of_decidableEq
      rawEq _
      (PeriodicOneInThree.formula source.erase)
      wrappedAtom.original .third]
  simpa only [PeriodicOneInThreePositioned.erase_formula] using
    rawThirdLookup

/-- Unit-elimination route-order transport with a cheap output equality
instance. -/
theorem
    PeriodicOneInThreeNoUnitsPositioned.variableRoutesInOccurrenceOrder_classical
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourceRoutes outputRoutes :
      PositionedPeriodicCNF.IncidenceRoutes)
    (sourceOrder :
      source.VariableRoutesInOccurrenceOrder sourceRoutes)
    (preserved :
      PeriodicOneInThreeNoUnitsPositioned.PreservesDegreeThreeOriginalRouteTerminalDirections
        source sourceRoutes outputRoutes) :
    @PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
      (OneInThreeNoUnitVariable Variable)
      (Classical.decEq _)
      (PeriodicOneInThreeNoUnitsPositioned.formula source)
      outputRoutes := by
  apply
    @PositionedPeriodicCNF.variableRoutesInOccurrenceOrder_of_decidableEq
      (OneInThreeNoUnitVariable Variable)
      (inferInstance) (Classical.decEq _)
      (PeriodicOneInThreeNoUnitsPositioned.formula source)
      outputRoutes
  exact
    PeriodicOneInThreeNoUnitsPositioned.variableRoutesInOccurrenceOrder_of_preservesDegreeThree
      source sourceRoutes outputRoutes sourceOrder preserved

end PeriodicOrthocrossing
end LeanTrominoes
