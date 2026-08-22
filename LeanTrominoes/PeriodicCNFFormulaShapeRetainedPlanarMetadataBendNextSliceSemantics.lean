/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendDescriptorData
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedVariablePositions

/-! # Canonical slice of retained bend links -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Changing the strictly interior local coordinate of a macrocell does not
change its quotient by a positive whole-macrocell period. -/
theorem macrocellCoordinate_ediv_period_eq_center_ediv
    {macroPeriod : Nat}
    (macroPeriodPositive : 0 < macroPeriod)
    {center localCoordinate : Int}
    (localNonnegative : 0 ≤ localCoordinate)
    (localSmall : localCoordinate < planarMacroScale) :
    (planarMacroScale * center + localCoordinate) /
        (planarMacroScale * macroPeriod) =
      center / macroPeriod := by
  have macroPeriodPositiveInt : (0 : Int) < macroPeriod := by
    exact_mod_cast macroPeriodPositive
  have macroPeriodNe : (macroPeriod : Int) ≠ 0 :=
    ne_of_gt macroPeriodPositiveInt
  have scaledPeriodPositive :
      (0 : Int) < planarMacroScale * macroPeriod :=
    mul_pos (by norm_num [planarMacroScale]) macroPeriodPositiveInt
  have scaledPeriodNe :
      (planarMacroScale * (macroPeriod : Int)) ≠ 0 :=
    ne_of_gt scaledPeriodPositive
  have remainderNonnegative :
      0 ≤ center % (macroPeriod : Int) :=
    Int.emod_nonneg center macroPeriodNe
  have remainderSmall :
      center % (macroPeriod : Int) < macroPeriod :=
    Int.emod_lt_of_pos center macroPeriodPositiveInt
  have baseQuotient :
      (planarMacroScale * (center % (macroPeriod : Int)) +
          localCoordinate) /
          (planarMacroScale * macroPeriod) = 0 := by
    apply Int.ediv_eq_zero_of_lt
    · nlinarith [show (0 : Int) < planarMacroScale by
        norm_num [planarMacroScale]]
    · nlinarith [show (0 : Int) < planarMacroScale by
        norm_num [planarMacroScale]]
  have centerDivision :=
    Int.emod_add_mul_ediv center (macroPeriod : Int)
  calc
    (planarMacroScale * center + localCoordinate) /
          (planarMacroScale * macroPeriod) =
        ((planarMacroScale * (center % (macroPeriod : Int)) +
            localCoordinate) +
          (center / (macroPeriod : Int)) *
            (planarMacroScale * macroPeriod)) /
          (planarMacroScale * macroPeriod) := by
            congr 1
            nlinarith
    _ =
        (planarMacroScale * (center % (macroPeriod : Int)) +
            localCoordinate) /
            (planarMacroScale * macroPeriod) +
          center / (macroPeriod : Int) := by
            rw [Int.add_mul_ediv_right _ _ scaledPeriodNe]
    _ = center / macroPeriod := by rw [baseQuotient, zero_add]

/-- The two routed-SAT terminal prototypes incident to one bend receive the
same canonical variable gauge. -/
theorem bendEndpointGauges_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routeBend : RouteBend) :
    retainedDrawingWrappedPeriodicPlanarSATVariableGauge source
        ⟨.terminal routeBend.incomingTerminal.indexed .finish⟩ =
      retainedDrawingWrappedPeriodicPlanarSATVariableGauge source
        ⟨.terminal routeBend.outgoingTerminal.indexed .start⟩ := by
  have periodPositive :=
    drawingGridSize_pos (PeriodicCNF.incidenceGraph source)
  have incomingBounds :=
    periodicPlanarSATVariableLocalPosition_in_macrocell
      (.terminal routeBend.incomingTerminal.indexed .finish :
        PeriodicPlanarSATVariable Variable)
  have outgoingBounds :=
    periodicPlanarSATVariableLocalPosition_in_macrocell
      (.terminal routeBend.outgoingTerminal.indexed .start :
        PeriodicPlanarSATVariable Variable)
  have incomingXQuotient :=
    macrocellCoordinate_ediv_period_eq_center_ediv
      periodPositive
      (center :=
        (periodicPlanarSATVariableDrawingPoint source
          (.terminal routeBend.incomingTerminal.indexed .finish)).1)
      (localCoordinate :=
        (periodicPlanarSATVariableLocalPosition
          (.terminal routeBend.incomingTerminal.indexed .finish :
            PeriodicPlanarSATVariable Variable)).1)
      (le_of_lt incomingBounds.1) incomingBounds.2.1
  have outgoingXQuotient :=
    macrocellCoordinate_ediv_period_eq_center_ediv
      periodPositive
      (center :=
        (periodicPlanarSATVariableDrawingPoint source
          (.terminal routeBend.outgoingTerminal.indexed .start)).1)
      (localCoordinate :=
        (periodicPlanarSATVariableLocalPosition
          (.terminal routeBend.outgoingTerminal.indexed .start :
            PeriodicPlanarSATVariable Variable)).1)
      (le_of_lt outgoingBounds.1) outgoingBounds.2.1
  have incomingYQuotient :=
    macrocellCoordinate_ediv_period_eq_center_ediv
      periodPositive
      (center :=
        (periodicPlanarSATVariableDrawingPoint source
          (.terminal routeBend.incomingTerminal.indexed .finish)).2)
      (localCoordinate :=
        (periodicPlanarSATVariableLocalPosition
          (.terminal routeBend.incomingTerminal.indexed .finish :
            PeriodicPlanarSATVariable Variable)).2)
      (le_of_lt incomingBounds.2.2.1) incomingBounds.2.2.2
  have outgoingYQuotient :=
    macrocellCoordinate_ediv_period_eq_center_ediv
      periodPositive
      (center :=
        (periodicPlanarSATVariableDrawingPoint source
          (.terminal routeBend.outgoingTerminal.indexed .start)).2)
      (localCoordinate :=
        (periodicPlanarSATVariableLocalPosition
          (.terminal routeBend.outgoingTerminal.indexed .start :
            PeriodicPlanarSATVariable Variable)).2)
      (le_of_lt outgoingBounds.2.2.1) outgoingBounds.2.2.2
  norm_num [planarMacroScale] at incomingXQuotient outgoingXQuotient incomingYQuotient outgoingYQuotient
  apply Prod.ext
  · change
      (drawingPeriodicPlanarSATVariablePosition source
          (.terminal routeBend.incomingTerminal.indexed .finish)).1 /
            (drawingPeriodicPlanarSATPlacement source).period =
        (drawingPeriodicPlanarSATVariablePosition source
          (.terminal routeBend.outgoingTerminal.indexed .start)).1 /
            (drawingPeriodicPlanarSATPlacement source).period
    rw [drawingPeriodicPlanarSATVariablePosition_eq_scale_add_local,
      drawingPeriodicPlanarSATVariablePosition_eq_scale_add_local]
    simp only [Cell.add, Cell.scale, drawingPeriodicPlanarSATPlacement]
    norm_num [planarMacroScale]
    rw [incomingXQuotient, outgoingXQuotient]
    rfl
  · change
      (drawingPeriodicPlanarSATVariablePosition source
          (.terminal routeBend.incomingTerminal.indexed .finish)).2 /
            (drawingPeriodicPlanarSATPlacement source).period =
        (drawingPeriodicPlanarSATVariablePosition source
          (.terminal routeBend.outgoingTerminal.indexed .start)).2 /
            (drawingPeriodicPlanarSATPlacement source).period
    rw [drawingPeriodicPlanarSATVariablePosition_eq_scale_add_local,
      drawingPeriodicPlanarSATVariablePosition_eq_scale_add_local]
    simp only [Cell.add, Cell.scale, drawingPeriodicPlanarSATPlacement]
    norm_num [planarMacroScale]
    rw [incomingYQuotient, outgoingYQuotient]
    rfl

/-- Canonical variable gauging preserves the zero relative offset across a
bend: its endpoint gauges cancel together with their common route shift. -/
@[simp]
theorem RouteBend.carrierWrappedVariableNormalization_relativeOffset
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routeBend : RouteBend) :
    (PeriodicEquality.normalizeLink
      (carrierWrappedVariableNormalization source)
      (routeBend.equalityLink source.incidenceGraph)).relativeOffset =
        (0, 0) := by
  have gaugesEqual := bendEndpointGauges_eq source routeBend
  change
    Cell.sub
        (Cell.add routeBend.translate
          (retainedDrawingWrappedPeriodicPlanarSATVariableGauge source
            ⟨.terminal routeBend.outgoingTerminal.indexed .start⟩))
        (Cell.add routeBend.translate
          (retainedDrawingWrappedPeriodicPlanarSATVariableGauge source
            ⟨.terminal routeBend.incomingTerminal.indexed .finish⟩)) =
      (0, 0)
  rw [gaugesEqual]
  simp [Cell.sub, Cell.add]

/-- A bend link never crosses into the next normalized horizontal slice. -/
@[simp]
theorem bendLinkNextSlice_eq_false
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routeBend : RouteBend) :
    bendLinkNextSlice source routeBend = false := by
  simp [bendLinkNextSlice, carrierLinkNextSlice]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
