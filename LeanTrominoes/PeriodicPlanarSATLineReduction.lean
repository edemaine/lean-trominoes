/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATOneDimensional
import LeanTrominoes.PeriodicCNFStripOneDimensional
import LeanTrominoes.PeriodicCNFStripSourceFormulaComputability

/-! # Total reductions to the four local one-dimensional planar SAT languages

The source guard handles malformed and empty-clause inputs. These are
primitive-recursive reductions; encoded polynomial-time bounds are separate.
-/
noncomputable section
namespace LeanTrominoes.PeriodicPlanarSAT.LineReduction
open PeriodicCNFStripReduction
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 2048
local instance lineSourceDecidableEq : DecidableEq Variable := Classical.decEq _
local instance lineExactOneTargetDecidableEq : DecidableEq (ExactOneEndpoint.Target Variable) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

def ordinary (f : PeriodicCNF Nat) : Input (ThreeOccurrenceGeometry.Target Variable) :=
  ThreeOccurrenceGeometry.input (sourceFormula f)

def exactOne (f : PeriodicCNF Nat) : Input (ExactOneEndpoint.Target Variable) :=
  ExactOneEndpoint.input (sourceFormula f)

theorem ordinary_primrec : Primrec ordinary :=
  ThreeOccurrenceGeometry.input_primrec.comp sourceFormula_primrec

theorem exactOne_primrec : Primrec exactOne :=
  ExactOneEndpoint.input_primrec.comp sourceFormula_primrec

theorem ordinary_correct (f : PeriodicCNF Nat) :
    PeriodicCNF.LocalPeriodicCNF1DSAT f ↔ Orbit.LocalOneDimensionalProblem (ordinary f) :=
  (sourceFormula_correct f).trans
    (ThreeOccurrenceGeometry.localOneDimensional_correct (sourceFormula f)
      (sourceFormula_isLocal f) (sourceFormula_widthAtMostThree f)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq f)
      (sourceFormula_clausesNonempty f) (sourceFormula_isOneDimensional f)).symm

theorem ordinaryThreeOccurrence_correct (f : PeriodicCNF Nat) :
    PeriodicCNF.LocalPeriodicCNF1DSAT f ↔
      Orbit.LocalOneDimensionalThreeOccurrenceProblem (ordinary f) :=
  (sourceFormula_correct f).trans
    (ThreeOccurrenceGeometry.localOneDimensionalThreeOccurrence_correct (sourceFormula f)
      (sourceFormula_isLocal f) (sourceFormula_widthAtMostThree f)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq f)
      (sourceFormula_clausesNonempty f) (sourceFormula_isOneDimensional f)).symm

theorem exactOne_correct (f : PeriodicCNF Nat) :
    PeriodicCNF.LocalPeriodicCNF1DSAT f ↔
      Unbounded.LocalOneDimensionalExactOneProblem (exactOne f) :=
  (sourceFormula_correct f).trans
    (ExactOneEndpoint.localOneDimensional_correct (sourceFormula f)
      (sourceFormula_isLocal f) (sourceFormula_widthAtMostThree f)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq f)
      (sourceFormula_clausesNonempty f) (sourceFormula_isOneDimensional f)).symm

theorem exactOneThreeOccurrence_correct (f : PeriodicCNF Nat) :
    PeriodicCNF.LocalPeriodicCNF1DSAT f ↔
      Unbounded.LocalOneDimensionalExactOneThreeOccurrenceProblem (exactOne f) :=
  (sourceFormula_correct f).trans
    (ExactOneEndpoint.localOneDimensionalThreeOccurrence_correct (sourceFormula f)
      (sourceFormula_isLocal f) (sourceFormula_widthAtMostThree f)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq f)
      (sourceFormula_clausesNonempty f) (sourceFormula_isOneDimensional f)).symm
end LeanTrominoes.PeriodicPlanarSAT.LineReduction
