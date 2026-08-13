/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecFlatSavitchContextSpace
import LeanTrominoes.PartrecFrontierIndexDecodeSpace
import LeanTrominoes.PartrecFlatStripFrontierContext
import LeanTrominoes.PartrecFlatPackedLookupColumnBound

/-!
# Evaluator-space certificate for the recovered flat strip frontier context

This module fits the strip-suffix projections, the two frontier-index
decodings, and the fixed assembly of the native seven-field transition
context while retaining the original coordinate stream.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes
open LeanTrominoes.FiniteState

namespace EvaluatorCodeFits

def flatStripFieldCost
    (fieldIndex context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) : Nat :=
  let suffix := PeriodicStripFlatEncoding.stripFields periodicStrip
  getCost fieldIndex suffix +
    flatContextCost context stateCount state suffix

theorem flatStripField
    (fieldIndex context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits
      (FlatStripEdgePartrec.stripFieldCode fieldIndex)
      (divideEvalProgramList context stateCount state ++
        PeriodicStripFlatEncoding.stripFields periodicStrip)
      [(PeriodicStripFlatEncoding.stripFields periodicStrip)[fieldIndex]?.getD 0]
      (flatStripFieldCost fieldIndex context stateCount state periodicStrip) := by
  have result := comp
    (get fieldIndex (PeriodicStripFlatEncoding.stripFields periodicStrip))
    (flatContext context stateCount state
      (PeriodicStripFlatEncoding.stripFields periodicStrip))
  simpa [FlatStripEdgePartrec.stripFieldCode, flatStripFieldCost] using result

def flatStripPairArgumentsTailCost
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) : Nat :=
  let values := divideEvalProgramList context stateCount state ++
    PeriodicStripFlatEncoding.stripFields periodicStrip
  prependCost values [state.query.first] [state.query.last]
    (getCost 5 values) (getCost 6 values)

theorem flatStripPairArgumentsTail
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    let values := divideEvalProgramList context stateCount state ++
      PeriodicStripFlatEncoding.stripFields periodicStrip
    EvaluatorCodeFits (Code.prepend (Code.get 5) (Code.get 6)) values
      [state.query.first, state.query.last]
      (flatStripPairArgumentsTailCost
        context stateCount state periodicStrip) := by
  simp only
  let values := divideEvalProgramList context stateCount state ++
    PeriodicStripFlatEncoding.stripFields periodicStrip
  have result := prepend (get 5 values) (get 6 values)
  simpa [flatStripPairArgumentsTailCost, values,
    divideEvalProgramList, DivideEvalState.toNatList, prependCost] using result

def flatStripPairArgumentsCost
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) : Nat :=
  let values := divideEvalProgramList context stateCount state ++
    PeriodicStripFlatEncoding.stripFields periodicStrip
  prependCost values [periodicStrip.period]
    [state.query.first, state.query.last]
    (flatStripFieldCost 1 context stateCount state periodicStrip)
    (flatStripPairArgumentsTailCost context stateCount state periodicStrip)

theorem flatStripPairArguments
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits FlatStripEdgePartrec.pairArgumentsCode
      (divideEvalProgramList context stateCount state ++
        PeriodicStripFlatEncoding.stripFields periodicStrip)
      [periodicStrip.period, state.query.first, state.query.last]
      (flatStripPairArgumentsCost context stateCount state periodicStrip) := by
  have result := prepend
    (flatStripField 1 context stateCount state periodicStrip)
    (flatStripPairArgumentsTail context stateCount state periodicStrip)
  simpa [FlatStripEdgePartrec.pairArgumentsCode,
    flatStripPairArgumentsCost, flatStripPairArgumentsTailCost,
    flatStripFieldCost, PeriodicStripFlatEncoding.stripFields,
    prependCost] using result

def flatStripPairViewCost
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) : Nat :=
  frontierPairViewCost periodicStrip.period state.query.first state.query.last +
    flatStripPairArgumentsCost context stateCount state periodicStrip

theorem flatStripPairView
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits FlatStripEdgePartrec.pairViewCode
      (divideEvalProgramList context stateCount state ++
        PeriodicStripFlatEncoding.stripFields periodicStrip)
      [state.query.first / periodicStrip.period,
        state.query.first % periodicStrip.period,
        state.query.last / periodicStrip.period,
        state.query.last % periodicStrip.period]
      (flatStripPairViewCost context stateCount state periodicStrip) := by
  have result := comp
    (frontierPairView periodicStrip.period state.query.first state.query.last)
    (flatStripPairArguments context stateCount state periodicStrip)
  simpa [FlatStripEdgePartrec.pairViewCode,
    flatStripPairViewCost] using result

def flatStripPairFieldCost
    (fieldIndex context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) : Nat :=
  getCost fieldIndex
      [state.query.first / periodicStrip.period,
        state.query.first % periodicStrip.period,
        state.query.last / periodicStrip.period,
        state.query.last % periodicStrip.period] +
    flatStripPairViewCost context stateCount state periodicStrip

theorem flatStripPairField
    (fieldIndex context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits
      (FlatStripEdgePartrec.pairFieldCode fieldIndex)
      (divideEvalProgramList context stateCount state ++
        PeriodicStripFlatEncoding.stripFields periodicStrip)
      [[state.query.first / periodicStrip.period,
          state.query.first % periodicStrip.period,
          state.query.last / periodicStrip.period,
          state.query.last % periodicStrip.period][fieldIndex]?.getD 0]
      (flatStripPairFieldCost fieldIndex context stateCount state periodicStrip) := by
  have result := comp
    (get fieldIndex
      [state.query.first / periodicStrip.period,
        state.query.first % periodicStrip.period,
        state.query.last / periodicStrip.period,
        state.query.last % periodicStrip.period])
    (flatStripPairView context stateCount state periodicStrip)
  simpa [FlatStripEdgePartrec.pairFieldCode,
    flatStripPairFieldCost] using result

def flatStripCoordinatesCost
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) : Nat :=
  let suffix := PeriodicStripFlatEncoding.stripFields periodicStrip
  dropCost 3 suffix + flatContextCost context stateCount state suffix

theorem flatStripCoordinates
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits FlatStripEdgePartrec.coordinatesCode
      (divideEvalProgramList context stateCount state ++
        PeriodicStripFlatEncoding.stripFields periodicStrip)
      (periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields)
      (flatStripCoordinatesCost context stateCount state periodicStrip) := by
  have result := comp
    (drop 3 (PeriodicStripFlatEncoding.stripFields periodicStrip))
    (flatContext context stateCount state
      (PeriodicStripFlatEncoding.stripFields periodicStrip))
  simpa [FlatStripEdgePartrec.coordinatesCode, flatStripCoordinatesCost,
    PeriodicStripFlatEncoding.stripFields] using result

def flatStripContextCost
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) : Nat :=
  let values := divideEvalProgramList context stateCount state ++
    PeriodicStripFlatEncoding.stripFields periodicStrip
  let coordinates := periodicStrip.motif.flatMap
    PeriodicStripFlatEncoding.cellFields
  let firstWord := state.query.first / periodicStrip.period
  let firstPhase := state.query.first % periodicStrip.period
  let lastWord := state.query.last / periodicStrip.period
  let lastPhase := state.query.last % periodicStrip.period
  let costLastPhase := prependCost values [lastPhase] coordinates
    (flatStripPairFieldCost 3 context stateCount state periodicStrip)
    (flatStripCoordinatesCost context stateCount state periodicStrip)
  let costLastWord := prependCost values [lastWord] (lastPhase :: coordinates)
    (flatStripPairFieldCost 2 context stateCount state periodicStrip)
    costLastPhase
  let costFirstPhase := prependCost values [firstPhase]
    (lastWord :: lastPhase :: coordinates)
    (flatStripPairFieldCost 1 context stateCount state periodicStrip)
    costLastWord
  let costFirstWord := prependCost values [firstWord]
    (firstPhase :: lastWord :: lastPhase :: coordinates)
    (flatStripPairFieldCost 0 context stateCount state periodicStrip)
    costFirstPhase
  let costLength := prependCost values [periodicStrip.motif.length]
    (firstWord :: firstPhase :: lastWord :: lastPhase :: coordinates)
    (flatStripFieldCost 2 context stateCount state periodicStrip)
    costFirstWord
  let costPeriod := prependCost values [periodicStrip.period]
    (periodicStrip.motif.length :: firstWord :: firstPhase ::
      lastWord :: lastPhase :: coordinates)
    (flatStripFieldCost 1 context stateCount state periodicStrip)
    costLength
  prependCost values [periodicStrip.width]
    (periodicStrip.period :: periodicStrip.motif.length ::
      firstWord :: firstPhase :: lastWord :: lastPhase :: coordinates)
    (flatStripFieldCost 0 context stateCount state periodicStrip)
    costPeriod

/-- Exact fitted certificate for the complete seven-field flat transition
context reconstructed at a Savitch leaf. -/
theorem flatStripContext
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits FlatStripEdgePartrec.contextCode
      (divideEvalProgramList context stateCount state ++
        PeriodicStripFlatEncoding.stripFields periodicStrip)
      ([periodicStrip.width, periodicStrip.period,
          periodicStrip.motif.length,
          state.query.first / periodicStrip.period,
          state.query.first % periodicStrip.period,
          state.query.last / periodicStrip.period,
          state.query.last % periodicStrip.period] ++
        periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields)
      (flatStripContextCost context stateCount state periodicStrip) := by
  let values := divideEvalProgramList context stateCount state ++
    PeriodicStripFlatEncoding.stripFields periodicStrip
  have result := prepend (flatStripField 0 context stateCount state periodicStrip) <|
    prepend (flatStripField 1 context stateCount state periodicStrip) <|
      prepend (flatStripField 2 context stateCount state periodicStrip) <|
        prepend (flatStripPairField 0 context stateCount state periodicStrip) <|
          prepend (flatStripPairField 1 context stateCount state periodicStrip) <|
            prepend (flatStripPairField 2 context stateCount state periodicStrip) <|
              prepend (flatStripPairField 3 context stateCount state periodicStrip)
                (flatStripCoordinates context stateCount state periodicStrip)
  simpa [FlatStripEdgePartrec.contextCode, flatStripContextCost,
    flatStripFieldCost, flatStripPairFieldCost, flatStripPairViewCost,
    flatStripPairArgumentsCost, flatStripPairArgumentsTailCost,
    flatStripCoordinatesCost, PeriodicStripFlatEncoding.stripFields,
    values, prependCost] using result

/-! ## Native input-space bound -/

/-- Shared native workspace unit.  The first summand is the exact flat
Savitch input footprint; the second is the arithmetic unit already proved
for decoding the two frontier indices. -/
def flatStripContextSpaceUnit
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) : Nat :=
  encodedListSpace
      (divideEvalProgramList context stateCount state ++
        PeriodicStripFlatEncoding.stripFields periodicStrip) +
    frontierPairPolynomialSpaceUnit periodicStrip.period
      state.query.first state.query.last + 10

private theorem flatStripContextSpaceUnit_large
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    10 ≤ flatStripContextSpaceUnit context stateCount state periodicStrip := by
  simp [flatStripContextSpaceUnit]

private theorem flatStripContextInputSpace_le_unit
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    encodedListSpace
        (divideEvalProgramList context stateCount state ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) ≤
      flatStripContextSpaceUnit context stateCount state periodicStrip := by
  simp only [flatStripContextSpaceUnit]
  omega

private theorem flatStripContextPairUnit_le_unit
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    frontierPairPolynomialSpaceUnit periodicStrip.period
        state.query.first state.query.last ≤
      flatStripContextSpaceUnit context stateCount state periodicStrip := by
  simp only [flatStripContextSpaceUnit]
  omega

private theorem flatStripContextRecoveryUnit_le_unit
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    flatContextSpaceUnit context stateCount state
        (PeriodicStripFlatEncoding.stripFields periodicStrip) ≤
      flatStripContextSpaceUnit context stateCount state periodicStrip := by
  simp [flatContextSpaceUnit, flatStripContextSpaceUnit]

private theorem flatStripContextSuffixSpace_le_unit
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    encodedListSpace (PeriodicStripFlatEncoding.stripFields periodicStrip) ≤
      flatStripContextSpaceUnit context stateCount state periodicStrip := by
  have raw := flatLookupEncodedListSpace_suffix_le
    (divideEvalProgramList context stateCount state)
    (PeriodicStripFlatEncoding.stripFields periodicStrip)
  exact raw.trans
    (flatStripContextInputSpace_le_unit context stateCount state periodicStrip)

private theorem flatStripContextCoordinatesSpace_le_unit
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    encodedListSpace
        (periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields) ≤
      flatStripContextSpaceUnit context stateCount state periodicStrip := by
  have raw := flatLookupEncodedListSpace_suffix_le
    [periodicStrip.width, periodicStrip.period, periodicStrip.motif.length]
    (periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields)
  have suffix := flatStripContextSuffixSpace_le_unit
    context stateCount state periodicStrip
  simpa [PeriodicStripFlatEncoding.stripFields] using raw.trans suffix

private theorem flatStripContextInputFieldSpace_le_unit
    (field context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip)
    (member : field ∈
      divideEvalProgramList context stateCount state ++
        PeriodicStripFlatEncoding.stripFields periodicStrip) :
    encodedListSpace [field] ≤
      flatStripContextSpaceUnit context stateCount state periodicStrip := by
  have raw := flatLookupEncodedFieldSpace_le_of_mem field
    (divideEvalProgramList context stateCount state ++
      PeriodicStripFlatEncoding.stripFields periodicStrip) member
  have input := flatStripContextInputSpace_le_unit
    context stateCount state periodicStrip
  simpa [encodedListSpace_cons, encodedListSpace_nil] using raw.trans input

private theorem flatStripContextWidthSpace_le_unit
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    encodedListSpace [periodicStrip.width] ≤
      flatStripContextSpaceUnit context stateCount state periodicStrip := by
  apply flatStripContextInputFieldSpace_le_unit
  simp [PeriodicStripFlatEncoding.stripFields]

private theorem flatStripContextPeriodSpace_le_unit
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    encodedListSpace [periodicStrip.period] ≤
      flatStripContextSpaceUnit context stateCount state periodicStrip := by
  apply flatStripContextInputFieldSpace_le_unit
  simp [PeriodicStripFlatEncoding.stripFields]

private theorem flatStripContextMotifLengthSpace_le_unit
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    encodedListSpace [periodicStrip.motif.length] ≤
      flatStripContextSpaceUnit context stateCount state periodicStrip := by
  apply flatStripContextInputFieldSpace_le_unit
  simp [PeriodicStripFlatEncoding.stripFields]

private theorem flatStripContextFirstSpace_le_unit
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    encodedListSpace [state.query.first] ≤
      flatStripContextSpaceUnit context stateCount state periodicStrip := by
  apply flatStripContextInputFieldSpace_le_unit
  rcases state with ⟨⟨depth, first, last⟩, stack, answer⟩
  simp [divideEvalProgramList, DivideEvalState.toNatList]

private theorem flatStripContextLastSpace_le_unit
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    encodedListSpace [state.query.last] ≤
      flatStripContextSpaceUnit context stateCount state periodicStrip := by
  apply flatStripContextInputFieldSpace_le_unit
  rcases state with ⟨⟨depth, first, last⟩, stack, answer⟩
  simp [divideEvalProgramList, DivideEvalState.toNatList]

private theorem flatStripContextPairValueSpace_le_unit
    (value context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip)
    (bound : value ≤ frontierPairPolynomialSpaceLimit
      periodicStrip.period state.query.first state.query.last) :
    encodedListSpace [value] ≤
      flatStripContextSpaceUnit context stateCount state periodicStrip := by
  have bits := encodeNat_length_mono bound
  have pairUnit := flatStripContextPairUnit_le_unit
    context stateCount state periodicStrip
  simp only [encodedListSpace_cons, encodedListSpace_nil] at bits ⊢
  simp [frontierPairPolynomialSpaceUnit] at pairUnit
  omega

private theorem flatStripContextFirstWordSpace_le_unit
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    encodedListSpace [state.query.first / periodicStrip.period] ≤
      flatStripContextSpaceUnit context stateCount state periodicStrip := by
  apply flatStripContextPairValueSpace_le_unit
  exact (Nat.div_le_self _ _).trans (by
    simp only [frontierPairPolynomialSpaceLimit]
    omega)

private theorem flatStripContextFirstPhaseSpace_le_unit
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    encodedListSpace [state.query.first % periodicStrip.period] ≤
      flatStripContextSpaceUnit context stateCount state periodicStrip := by
  apply flatStripContextPairValueSpace_le_unit
  exact (Nat.mod_le _ _).trans (by
    simp only [frontierPairPolynomialSpaceLimit]
    omega)

private theorem flatStripContextLastWordSpace_le_unit
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    encodedListSpace [state.query.last / periodicStrip.period] ≤
      flatStripContextSpaceUnit context stateCount state periodicStrip := by
  apply flatStripContextPairValueSpace_le_unit
  exact (Nat.div_le_self _ _).trans (by
    simp only [frontierPairPolynomialSpaceLimit]
    omega)

private theorem flatStripContextLastPhaseSpace_le_unit
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    encodedListSpace [state.query.last % periodicStrip.period] ≤
      flatStripContextSpaceUnit context stateCount state periodicStrip := by
  apply flatStripContextPairValueSpace_le_unit
  exact (Nat.mod_le _ _).trans (by
    simp only [frontierPairPolynomialSpaceLimit]
    omega)

private theorem flatStripContextPairOutputSpace_le
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    encodedListSpace
        [state.query.first / periodicStrip.period,
          state.query.first % periodicStrip.period,
          state.query.last / periodicStrip.period,
          state.query.last % periodicStrip.period] ≤
      4 * flatStripContextSpaceUnit context stateCount state periodicStrip := by
  have firstWord := flatStripContextFirstWordSpace_le_unit
    context stateCount state periodicStrip
  have firstPhase := flatStripContextFirstPhaseSpace_le_unit
    context stateCount state periodicStrip
  have lastWord := flatStripContextLastWordSpace_le_unit
    context stateCount state periodicStrip
  have lastPhase := flatStripContextLastPhaseSpace_le_unit
    context stateCount state periodicStrip
  simp only [encodedListSpace_cons, encodedListSpace_nil] at *
  omega

theorem flatStripContextOutputSpace_le
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    encodedListSpace
        ([periodicStrip.width, periodicStrip.period,
            periodicStrip.motif.length,
            state.query.first / periodicStrip.period,
            state.query.first % periodicStrip.period,
            state.query.last / periodicStrip.period,
            state.query.last % periodicStrip.period] ++
          periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields) ≤
      8 * flatStripContextSpaceUnit context stateCount state periodicStrip := by
  have width := flatStripContextWidthSpace_le_unit
    context stateCount state periodicStrip
  have period := flatStripContextPeriodSpace_le_unit
    context stateCount state periodicStrip
  have motifLength := flatStripContextMotifLengthSpace_le_unit
    context stateCount state periodicStrip
  have firstWord := flatStripContextFirstWordSpace_le_unit
    context stateCount state periodicStrip
  have firstPhase := flatStripContextFirstPhaseSpace_le_unit
    context stateCount state periodicStrip
  have lastWord := flatStripContextLastWordSpace_le_unit
    context stateCount state periodicStrip
  have lastPhase := flatStripContextLastPhaseSpace_le_unit
    context stateCount state periodicStrip
  have coordinates := flatStripContextCoordinatesSpace_le_unit
    context stateCount state periodicStrip
  simp only [List.cons_append, List.nil_append,
    encodedListSpace_cons, encodedListSpace_nil] at *
  omega

/-- One envelope containing suffix recovery, pair decoding, and every
fixed-width projection used by the context adapter. -/
def flatStripContextBaseSpaceBound
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) : Nat :=
  flatContextSpaceBound context stateCount state
      (PeriodicStripFlatEncoding.stripFields periodicStrip) +
    1000000000000000000000000000000 *
      frontierPairPolynomialSpaceUnit periodicStrip.period
        state.query.first state.query.last +
    1000000000 *
      flatStripContextSpaceUnit context stateCount state periodicStrip

private theorem flatStripContextRecoveryCost_le_base
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    flatContextCost context stateCount state
        (PeriodicStripFlatEncoding.stripFields periodicStrip) ≤
      flatStripContextBaseSpaceBound
        context stateCount state periodicStrip := by
  have bound := flatContextCost_le_bound context stateCount state
    (PeriodicStripFlatEncoding.stripFields periodicStrip)
  simp only [flatStripContextBaseSpaceBound]
  omega

private theorem flatStripContextPairCost_le_base
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    frontierPairViewCost periodicStrip.period
        state.query.first state.query.last ≤
      flatStripContextBaseSpaceBound
        context stateCount state periodicStrip := by
  have bound := frontierPairViewCost_le_linear periodicStrip.period
    state.query.first state.query.last
  simp only [flatStripContextBaseSpaceBound]
  omega

private theorem flatStripFieldCost_le_base
    (fieldIndex context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) (fieldBound : fieldIndex ≤ 2) :
    flatStripFieldCost fieldIndex context stateCount state periodicStrip ≤
      flatStripContextBaseSpaceBound
        context stateCount state periodicStrip := by
  let suffix := PeriodicStripFlatEncoding.stripFields periodicStrip
  let unit := flatStripContextSpaceUnit context stateCount state periodicStrip
  have suffixSpace : encodedListSpace suffix ≤ unit := by
    simpa [suffix, unit] using flatStripContextSuffixSpace_le_unit
      context stateCount state periodicStrip
  have unitLarge : 10 ≤ unit := by
    simpa [unit] using flatStripContextSpaceUnit_large
      context stateCount state periodicStrip
  have getRaw := listCodeGetCost_le_linear fieldIndex suffix
  have getBound : getCost fieldIndex suffix ≤ 100000 * unit := by
    calc
      getCost fieldIndex suffix ≤
          (10000 * (fieldIndex + 1)) * (encodedListSpace suffix + 1) := getRaw
      _ ≤ (10000 * 3) * (unit + 1) := Nat.mul_le_mul
        (Nat.mul_le_mul_left 10000 (by omega)) (by omega)
      _ ≤ 100000 * unit := by omega
  have recovery := flatContextCost_le_bound context stateCount state
    (PeriodicStripFlatEncoding.stripFields periodicStrip)
  have getBound' : getCost fieldIndex
      (PeriodicStripFlatEncoding.stripFields periodicStrip) ≤ 100000 * unit := by
    simpa [suffix] using getBound
  simp only [flatStripFieldCost]
  simp only [flatStripContextBaseSpaceBound]
  omega

theorem flatStripPairArgumentsTailCost_le_base
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    flatStripPairArgumentsTailCost context stateCount state periodicStrip ≤
      flatStripContextBaseSpaceBound
        context stateCount state periodicStrip := by
  let values := divideEvalProgramList context stateCount state ++
    PeriodicStripFlatEncoding.stripFields periodicStrip
  let unit := flatStripContextSpaceUnit context stateCount state periodicStrip
  have valuesSpace : encodedListSpace values ≤ unit := by
    simpa [values, unit] using flatStripContextInputSpace_le_unit
      context stateCount state periodicStrip
  have firstSpace : encodedListSpace [state.query.first] ≤ unit := by
    simpa [unit] using flatStripContextFirstSpace_le_unit
      context stateCount state periodicStrip
  have lastSpace : encodedListSpace [state.query.last] ≤ unit := by
    simpa [unit] using flatStripContextLastSpace_le_unit
      context stateCount state periodicStrip
  have pairSpace : encodedListSpace [state.query.first, state.query.last] ≤
      2 * unit := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at *
    omega
  have unitLarge : 10 ≤ unit := by
    simpa [unit] using flatStripContextSpaceUnit_large
      context stateCount state periodicStrip
  have get5Raw := listCodeGetCost_le_linear 5 values
  have get6Raw := listCodeGetCost_le_linear 6 values
  have get5 : getCost 5 values ≤ 1000000 * unit := by omega
  have get6 : getCost 6 values ≤ 1000000 * unit := by omega
  have estimate := listCodePrependCost_le_of values [state.query.first]
    [state.query.last] (getCost 5 values) (getCost 6 values) (2 * unit)
    (by omega) (by omega) (by
      simpa only [List.headI_cons] using pairSpace)
  change prependCost values [state.query.first] [state.query.last]
      (getCost 5 values) (getCost 6 values) ≤ _
  simp only [flatStripContextBaseSpaceBound]
  omega

private theorem flatStripPairArgumentsCost_le
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    flatStripPairArgumentsCost context stateCount state periodicStrip ≤
      3 * flatStripContextBaseSpaceBound
        context stateCount state periodicStrip := by
  let values := divideEvalProgramList context stateCount state ++
    PeriodicStripFlatEncoding.stripFields periodicStrip
  let unit := flatStripContextSpaceUnit context stateCount state periodicStrip
  let base := flatStripContextBaseSpaceBound
    context stateCount state periodicStrip
  have valuesSpace : encodedListSpace values ≤ unit := by
    simpa [values, unit] using flatStripContextInputSpace_le_unit
      context stateCount state periodicStrip
  have periodSpace : encodedListSpace [periodicStrip.period] ≤ unit := by
    simpa [unit] using flatStripContextPeriodSpace_le_unit
      context stateCount state periodicStrip
  have firstSpace : encodedListSpace [state.query.first] ≤ unit := by
    simpa [unit] using flatStripContextFirstSpace_le_unit
      context stateCount state periodicStrip
  have lastSpace : encodedListSpace [state.query.last] ≤ unit := by
    simpa [unit] using flatStripContextLastSpace_le_unit
      context stateCount state periodicStrip
  have tailSpace : encodedListSpace [state.query.first, state.query.last] ≤
      3 * unit := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at *
    omega
  have outputSpace : encodedListSpace
      [periodicStrip.period, state.query.first, state.query.last] ≤
        3 * unit := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at *
    omega
  have fieldCost : flatStripFieldCost 1 context stateCount state periodicStrip ≤
      base := by
    simpa [base] using flatStripFieldCost_le_base 1 context stateCount state
      periodicStrip (by omega)
  have restCost := flatStripPairArgumentsTailCost_le_base
    context stateCount state periodicStrip
  have restCost' : flatStripPairArgumentsTailCost
      context stateCount state periodicStrip ≤ base := by
    simpa [base] using restCost
  have estimate := listCodePrependCost_le_of values [periodicStrip.period]
    [state.query.first, state.query.last]
    (flatStripFieldCost 1 context stateCount state periodicStrip)
    (flatStripPairArgumentsTailCost context stateCount state periodicStrip)
    (3 * unit) (by omega) (by omega) (by
      simpa only [List.headI_cons] using outputSpace)
  have unitLarge : 10 ≤ unit := by
    simpa [unit] using flatStripContextSpaceUnit_large
      context stateCount state periodicStrip
  have baseLarge : 1000000000 * unit ≤ base := by
    simp only [base, flatStripContextBaseSpaceBound]
    omega
  change prependCost values [periodicStrip.period]
      [state.query.first, state.query.last]
      (flatStripFieldCost 1 context stateCount state periodicStrip)
      (flatStripPairArgumentsTailCost context stateCount state periodicStrip) ≤ _
  omega

private theorem flatStripPairViewCost_le
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    flatStripPairViewCost context stateCount state periodicStrip ≤
      4 * flatStripContextBaseSpaceBound
        context stateCount state periodicStrip := by
  have pair := flatStripContextPairCost_le_base
    context stateCount state periodicStrip
  have arguments := flatStripPairArgumentsCost_le
    context stateCount state periodicStrip
  simp only [flatStripPairViewCost]
  omega

private theorem flatStripPairFieldCost_le
    (fieldIndex context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) (fieldBound : fieldIndex ≤ 3) :
    flatStripPairFieldCost fieldIndex context stateCount state periodicStrip ≤
      5 * flatStripContextBaseSpaceBound
        context stateCount state periodicStrip := by
  let pairOutput :=
    [state.query.first / periodicStrip.period,
      state.query.first % periodicStrip.period,
      state.query.last / periodicStrip.period,
      state.query.last % periodicStrip.period]
  let unit := flatStripContextSpaceUnit context stateCount state periodicStrip
  let base := flatStripContextBaseSpaceBound
    context stateCount state periodicStrip
  have outputSpace : encodedListSpace pairOutput ≤ 4 * unit := by
    simpa [pairOutput, unit] using flatStripContextPairOutputSpace_le
      context stateCount state periodicStrip
  have getRaw := listCodeGetCost_le_linear fieldIndex pairOutput
  have getBound : getCost fieldIndex pairOutput ≤ 1000000 * unit := by
    calc
      getCost fieldIndex pairOutput ≤
          (10000 * (fieldIndex + 1)) *
            (encodedListSpace pairOutput + 1) := getRaw
      _ ≤ (10000 * 4) * (4 * unit + 1) := Nat.mul_le_mul
        (Nat.mul_le_mul_left 10000 (by omega)) (by omega)
      _ ≤ 1000000 * unit := by
        have unitLarge := flatStripContextSpaceUnit_large
          context stateCount state periodicStrip
        simpa [unit] using (show
          (10000 * 4) * (4 * flatStripContextSpaceUnit
              context stateCount state periodicStrip + 1) ≤
            1000000 * flatStripContextSpaceUnit
              context stateCount state periodicStrip by omega)
  have pairView := flatStripPairViewCost_le
    context stateCount state periodicStrip
  have pairView' : flatStripPairViewCost
      context stateCount state periodicStrip ≤ 4 * base := by
    simpa [base] using pairView
  have baseLarge : 1000000000 * unit ≤ base := by
    simp only [base, flatStripContextBaseSpaceBound]
    omega
  simp only [flatStripPairFieldCost]
  dsimp only [pairOutput] at getBound
  omega

private theorem flatStripCoordinatesCost_le_base
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    flatStripCoordinatesCost context stateCount state periodicStrip ≤
      flatStripContextBaseSpaceBound
        context stateCount state periodicStrip := by
  let suffix := PeriodicStripFlatEncoding.stripFields periodicStrip
  let unit := flatStripContextSpaceUnit context stateCount state periodicStrip
  have suffixSpace : encodedListSpace suffix ≤ unit := by
    simpa [suffix, unit] using flatStripContextSuffixSpace_le_unit
      context stateCount state periodicStrip
  have dropRaw := flatLookupDropCost_le_linear 3 suffix
  have unitLarge : 10 ≤ unit := by
    simpa [unit] using flatStripContextSpaceUnit_large
      context stateCount state periodicStrip
  have dropBound : dropCost 3 suffix ≤ 1000000 * unit := by
    calc
      dropCost 3 suffix ≤
          (10000 * (3 + 1)) * (encodedListSpace suffix + 1) := dropRaw
      _ ≤ 1000000 * unit := by omega
  have recovery := flatContextCost_le_bound context stateCount state
    (PeriodicStripFlatEncoding.stripFields periodicStrip)
  have dropBound' : dropCost 3
      (PeriodicStripFlatEncoding.stripFields periodicStrip) ≤ 1000000 * unit := by
    simpa [suffix] using dropBound
  simp only [flatStripCoordinatesCost]
  simp only [flatStripContextBaseSpaceBound]
  omega

/-- Linear native-field evaluator bound for reconstructing the complete flat
strip transition context at a Savitch leaf. -/
def flatStripContextSpaceBound
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) : Nat :=
  100 * flatStripContextBaseSpaceBound
    context stateCount state periodicStrip

set_option maxHeartbeats 1200000 in
theorem flatStripContextCost_le_bound
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    flatStripContextCost context stateCount state periodicStrip ≤
      flatStripContextSpaceBound context stateCount state periodicStrip := by
  let values := divideEvalProgramList context stateCount state ++
    PeriodicStripFlatEncoding.stripFields periodicStrip
  let coordinates := periodicStrip.motif.flatMap
    PeriodicStripFlatEncoding.cellFields
  let firstWord := state.query.first / periodicStrip.period
  let firstPhase := state.query.first % periodicStrip.period
  let lastWord := state.query.last / periodicStrip.period
  let lastPhase := state.query.last % periodicStrip.period
  let unit := flatStripContextSpaceUnit context stateCount state periodicStrip
  let base := flatStripContextBaseSpaceBound
    context stateCount state periodicStrip
  have valuesSpace : encodedListSpace values ≤ 8 * unit := by
    have raw := flatStripContextInputSpace_le_unit
      context stateCount state periodicStrip
    simpa [values, unit] using raw.trans (by omega)
  have widthSpace : encodedListSpace [periodicStrip.width] ≤ 8 * unit := by
    exact (flatStripContextWidthSpace_le_unit
      context stateCount state periodicStrip).trans (by omega)
  have periodSpace : encodedListSpace [periodicStrip.period] ≤ 8 * unit := by
    exact (flatStripContextPeriodSpace_le_unit
      context stateCount state periodicStrip).trans (by omega)
  have lengthSpace : encodedListSpace [periodicStrip.motif.length] ≤ 8 * unit := by
    exact (flatStripContextMotifLengthSpace_le_unit
      context stateCount state periodicStrip).trans (by omega)
  have firstWordSpace : encodedListSpace [firstWord] ≤ 8 * unit := by
    exact (flatStripContextFirstWordSpace_le_unit
      context stateCount state periodicStrip).trans (by
        simp only [unit, firstWord]
        omega)
  have firstPhaseSpace : encodedListSpace [firstPhase] ≤ 8 * unit := by
    exact (flatStripContextFirstPhaseSpace_le_unit
      context stateCount state periodicStrip).trans (by
        simp only [unit, firstPhase]
        omega)
  have lastWordSpace : encodedListSpace [lastWord] ≤ 8 * unit := by
    exact (flatStripContextLastWordSpace_le_unit
      context stateCount state periodicStrip).trans (by
        simp only [unit, lastWord]
        omega)
  have lastPhaseSpace : encodedListSpace [lastPhase] ≤ 8 * unit := by
    exact (flatStripContextLastPhaseSpace_le_unit
      context stateCount state periodicStrip).trans (by
        simp only [unit, lastPhase]
        omega)
  have coordinatesSpace : encodedListSpace coordinates ≤ 8 * unit := by
    have raw := flatStripContextCoordinatesSpace_le_unit
      context stateCount state periodicStrip
    simpa [coordinates, unit] using raw.trans (by omega)
  have outputSpace : encodedListSpace
      ([periodicStrip.width, periodicStrip.period,
          periodicStrip.motif.length, firstWord, firstPhase,
          lastWord, lastPhase] ++ coordinates) ≤ 8 * unit := by
    simpa [firstWord, firstPhase, lastWord, lastPhase, coordinates, unit] using
      flatStripContextOutputSpace_le context stateCount state periodicStrip
  have lastPhaseOutput : encodedListSpace (lastPhase :: coordinates) ≤
      8 * unit := by
    have suffix := flatLookupEncodedListSpace_suffix_le
      [periodicStrip.width, periodicStrip.period,
        periodicStrip.motif.length, firstWord, firstPhase, lastWord]
      (lastPhase :: coordinates)
    exact suffix.trans (by simpa using outputSpace)
  have lastWordOutput : encodedListSpace
      (lastWord :: lastPhase :: coordinates) ≤ 8 * unit := by
    have suffix := flatLookupEncodedListSpace_suffix_le
      [periodicStrip.width, periodicStrip.period,
        periodicStrip.motif.length, firstWord, firstPhase]
      (lastWord :: lastPhase :: coordinates)
    exact suffix.trans (by simpa using outputSpace)
  have firstPhaseOutput : encodedListSpace
      (firstPhase :: lastWord :: lastPhase :: coordinates) ≤ 8 * unit := by
    have suffix := flatLookupEncodedListSpace_suffix_le
      [periodicStrip.width, periodicStrip.period,
        periodicStrip.motif.length, firstWord]
      (firstPhase :: lastWord :: lastPhase :: coordinates)
    exact suffix.trans (by simpa using outputSpace)
  have firstWordOutput : encodedListSpace
      (firstWord :: firstPhase :: lastWord :: lastPhase :: coordinates) ≤
        8 * unit := by
    have suffix := flatLookupEncodedListSpace_suffix_le
      [periodicStrip.width, periodicStrip.period,
        periodicStrip.motif.length]
      (firstWord :: firstPhase :: lastWord :: lastPhase :: coordinates)
    exact suffix.trans (by simpa using outputSpace)
  have lengthOutput : encodedListSpace
      (periodicStrip.motif.length :: firstWord :: firstPhase ::
        lastWord :: lastPhase :: coordinates) ≤ 8 * unit := by
    have suffix := flatLookupEncodedListSpace_suffix_le
      [periodicStrip.width, periodicStrip.period]
      (periodicStrip.motif.length :: firstWord :: firstPhase ::
        lastWord :: lastPhase :: coordinates)
    exact suffix.trans (by simpa using outputSpace)
  have periodOutput : encodedListSpace
      (periodicStrip.period :: periodicStrip.motif.length ::
        firstWord :: firstPhase :: lastWord :: lastPhase :: coordinates) ≤
        8 * unit := by
    have suffix := flatLookupEncodedListSpace_suffix_le
      [periodicStrip.width]
      (periodicStrip.period :: periodicStrip.motif.length ::
        firstWord :: firstPhase :: lastWord :: lastPhase :: coordinates)
    exact suffix.trans (by simpa using outputSpace)
  have strip0 : flatStripFieldCost 0 context stateCount state periodicStrip ≤ base := by
    simpa [base] using flatStripFieldCost_le_base 0 context stateCount state
      periodicStrip (by omega)
  have strip1 : flatStripFieldCost 1 context stateCount state periodicStrip ≤ base := by
    simpa [base] using flatStripFieldCost_le_base 1 context stateCount state
      periodicStrip (by omega)
  have strip2 : flatStripFieldCost 2 context stateCount state periodicStrip ≤ base := by
    simpa [base] using flatStripFieldCost_le_base 2 context stateCount state
      periodicStrip (by omega)
  have pair0 : flatStripPairFieldCost 0 context stateCount state periodicStrip ≤
      5 * base := by
    simpa [base] using flatStripPairFieldCost_le 0 context stateCount state
      periodicStrip (by omega)
  have pair1 : flatStripPairFieldCost 1 context stateCount state periodicStrip ≤
      5 * base := by
    simpa [base] using flatStripPairFieldCost_le 1 context stateCount state
      periodicStrip (by omega)
  have pair2 : flatStripPairFieldCost 2 context stateCount state periodicStrip ≤
      5 * base := by
    simpa [base] using flatStripPairFieldCost_le 2 context stateCount state
      periodicStrip (by omega)
  have pair3 : flatStripPairFieldCost 3 context stateCount state periodicStrip ≤
      5 * base := by
    simpa [base] using flatStripPairFieldCost_le 3 context stateCount state
      periodicStrip (by omega)
  have coordinatesCost : flatStripCoordinatesCost
      context stateCount state periodicStrip ≤ base := by
    simpa [base] using flatStripCoordinatesCost_le_base
      context stateCount state periodicStrip
  have unitBase : 1000000000 * unit ≤ base := by
    simp only [base, flatStripContextBaseSpaceBound]
    omega
  have unitLarge : 10 ≤ unit := by
    simpa [unit] using flatStripContextSpaceUnit_large
      context stateCount state periodicStrip
  have estimateLastPhase := listCodePrependCost_le_of values [lastPhase]
    coordinates (flatStripPairFieldCost 3 context stateCount state periodicStrip)
    (flatStripCoordinatesCost context stateCount state periodicStrip) (8 * unit)
    valuesSpace lastPhaseSpace (by
      simpa only [List.headI_cons] using lastPhaseOutput)
  have estimateLastWord := listCodePrependCost_le_of values [lastWord]
    (lastPhase :: coordinates)
    (flatStripPairFieldCost 2 context stateCount state periodicStrip)
    (prependCost values [lastPhase] coordinates
      (flatStripPairFieldCost 3 context stateCount state periodicStrip)
      (flatStripCoordinatesCost context stateCount state periodicStrip)) (8 * unit)
    valuesSpace lastWordSpace (by
      simpa only [List.headI_cons] using lastWordOutput)
  have estimateFirstPhase := listCodePrependCost_le_of values [firstPhase]
    (lastWord :: lastPhase :: coordinates)
    (flatStripPairFieldCost 1 context stateCount state periodicStrip)
    (prependCost values [lastWord] (lastPhase :: coordinates)
      (flatStripPairFieldCost 2 context stateCount state periodicStrip)
      (prependCost values [lastPhase] coordinates
        (flatStripPairFieldCost 3 context stateCount state periodicStrip)
        (flatStripCoordinatesCost context stateCount state periodicStrip))) (8 * unit)
    valuesSpace firstPhaseSpace (by
      simpa only [List.headI_cons] using firstPhaseOutput)
  have estimateFirstWord := listCodePrependCost_le_of values [firstWord]
    (firstPhase :: lastWord :: lastPhase :: coordinates)
    (flatStripPairFieldCost 0 context stateCount state periodicStrip)
    (prependCost values [firstPhase] (lastWord :: lastPhase :: coordinates)
      (flatStripPairFieldCost 1 context stateCount state periodicStrip)
      (prependCost values [lastWord] (lastPhase :: coordinates)
        (flatStripPairFieldCost 2 context stateCount state periodicStrip)
        (prependCost values [lastPhase] coordinates
          (flatStripPairFieldCost 3 context stateCount state periodicStrip)
          (flatStripCoordinatesCost context stateCount state periodicStrip)))) (8 * unit)
    valuesSpace firstWordSpace (by
      simpa only [List.headI_cons] using firstWordOutput)
  have estimateLength := listCodePrependCost_le_of values
    [periodicStrip.motif.length]
    (firstWord :: firstPhase :: lastWord :: lastPhase :: coordinates)
    (flatStripFieldCost 2 context stateCount state periodicStrip)
    (prependCost values [firstWord]
      (firstPhase :: lastWord :: lastPhase :: coordinates)
      (flatStripPairFieldCost 0 context stateCount state periodicStrip)
      (prependCost values [firstPhase] (lastWord :: lastPhase :: coordinates)
        (flatStripPairFieldCost 1 context stateCount state periodicStrip)
        (prependCost values [lastWord] (lastPhase :: coordinates)
          (flatStripPairFieldCost 2 context stateCount state periodicStrip)
          (prependCost values [lastPhase] coordinates
            (flatStripPairFieldCost 3 context stateCount state periodicStrip)
            (flatStripCoordinatesCost context stateCount state periodicStrip)))))
    (8 * unit) valuesSpace lengthSpace (by
      simpa only [List.headI_cons] using lengthOutput)
  have estimatePeriod := listCodePrependCost_le_of values [periodicStrip.period]
    (periodicStrip.motif.length :: firstWord :: firstPhase ::
      lastWord :: lastPhase :: coordinates)
    (flatStripFieldCost 1 context stateCount state periodicStrip)
    (prependCost values [periodicStrip.motif.length]
      (firstWord :: firstPhase :: lastWord :: lastPhase :: coordinates)
      (flatStripFieldCost 2 context stateCount state periodicStrip)
      (prependCost values [firstWord]
        (firstPhase :: lastWord :: lastPhase :: coordinates)
        (flatStripPairFieldCost 0 context stateCount state periodicStrip)
        (prependCost values [firstPhase] (lastWord :: lastPhase :: coordinates)
          (flatStripPairFieldCost 1 context stateCount state periodicStrip)
          (prependCost values [lastWord] (lastPhase :: coordinates)
            (flatStripPairFieldCost 2 context stateCount state periodicStrip)
            (prependCost values [lastPhase] coordinates
              (flatStripPairFieldCost 3 context stateCount state periodicStrip)
              (flatStripCoordinatesCost context stateCount state periodicStrip))))))
    (8 * unit) valuesSpace periodSpace (by
      simpa only [List.headI_cons] using periodOutput)
  have estimateWidth := listCodePrependCost_le_of values [periodicStrip.width]
    (periodicStrip.period :: periodicStrip.motif.length ::
      firstWord :: firstPhase :: lastWord :: lastPhase :: coordinates)
    (flatStripFieldCost 0 context stateCount state periodicStrip)
    (prependCost values [periodicStrip.period]
      (periodicStrip.motif.length :: firstWord :: firstPhase ::
        lastWord :: lastPhase :: coordinates)
      (flatStripFieldCost 1 context stateCount state periodicStrip)
      (prependCost values [periodicStrip.motif.length]
        (firstWord :: firstPhase :: lastWord :: lastPhase :: coordinates)
        (flatStripFieldCost 2 context stateCount state periodicStrip)
        (prependCost values [firstWord]
          (firstPhase :: lastWord :: lastPhase :: coordinates)
          (flatStripPairFieldCost 0 context stateCount state periodicStrip)
          (prependCost values [firstPhase] (lastWord :: lastPhase :: coordinates)
            (flatStripPairFieldCost 1 context stateCount state periodicStrip)
            (prependCost values [lastWord] (lastPhase :: coordinates)
              (flatStripPairFieldCost 2 context stateCount state periodicStrip)
              (prependCost values [lastPhase] coordinates
                (flatStripPairFieldCost 3 context stateCount state periodicStrip)
                (flatStripCoordinatesCost context stateCount state periodicStrip)))))))
    (8 * unit) valuesSpace widthSpace (by
      simpa only [List.headI_cons, List.cons_append,
        List.nil_append] using outputSpace)
  let costLastPhase := prependCost values [lastPhase] coordinates
    (flatStripPairFieldCost 3 context stateCount state periodicStrip)
    (flatStripCoordinatesCost context stateCount state periodicStrip)
  let costLastWord := prependCost values [lastWord]
    (lastPhase :: coordinates)
    (flatStripPairFieldCost 2 context stateCount state periodicStrip)
    costLastPhase
  let costFirstPhase := prependCost values [firstPhase]
    (lastWord :: lastPhase :: coordinates)
    (flatStripPairFieldCost 1 context stateCount state periodicStrip)
    costLastWord
  let costFirstWord := prependCost values [firstWord]
    (firstPhase :: lastWord :: lastPhase :: coordinates)
    (flatStripPairFieldCost 0 context stateCount state periodicStrip)
    costFirstPhase
  let costLength := prependCost values [periodicStrip.motif.length]
    (firstWord :: firstPhase :: lastWord :: lastPhase :: coordinates)
    (flatStripFieldCost 2 context stateCount state periodicStrip)
    costFirstWord
  let costPeriod := prependCost values [periodicStrip.period]
    (periodicStrip.motif.length :: firstWord :: firstPhase ::
      lastWord :: lastPhase :: coordinates)
    (flatStripFieldCost 1 context stateCount state periodicStrip)
    costLength
  let costWidth := prependCost values [periodicStrip.width]
    (periodicStrip.period :: periodicStrip.motif.length ::
      firstWord :: firstPhase :: lastWord :: lastPhase :: coordinates)
    (flatStripFieldCost 0 context stateCount state periodicStrip)
    costPeriod
  have lastPhaseEstimate : costLastPhase ≤
      flatStripPairFieldCost 3 context stateCount state periodicStrip +
        flatStripCoordinatesCost context stateCount state periodicStrip +
          3 * (8 * unit) + 2 := by
    simpa [costLastPhase] using estimateLastPhase
  have lastPhaseBound : costLastPhase ≤ 10 * base := by omega
  have lastWordEstimate : costLastWord ≤
      flatStripPairFieldCost 2 context stateCount state periodicStrip +
        costLastPhase + 3 * (8 * unit) + 2 := by
    simpa [costLastWord, costLastPhase] using estimateLastWord
  have lastWordBound : costLastWord ≤ 20 * base := by omega
  have firstPhaseEstimate : costFirstPhase ≤
      flatStripPairFieldCost 1 context stateCount state periodicStrip +
        costLastWord + 3 * (8 * unit) + 2 := by
    simpa [costFirstPhase, costLastWord, costLastPhase] using estimateFirstPhase
  have firstPhaseBound : costFirstPhase ≤ 30 * base := by omega
  have firstWordEstimate : costFirstWord ≤
      flatStripPairFieldCost 0 context stateCount state periodicStrip +
        costFirstPhase + 3 * (8 * unit) + 2 := by
    simpa [costFirstWord, costFirstPhase, costLastWord, costLastPhase] using
      estimateFirstWord
  have firstWordBound : costFirstWord ≤ 40 * base := by omega
  have lengthEstimate : costLength ≤
      flatStripFieldCost 2 context stateCount state periodicStrip +
        costFirstWord + 3 * (8 * unit) + 2 := by
    simpa [costLength, costFirstWord, costFirstPhase, costLastWord,
      costLastPhase] using estimateLength
  have lengthBound : costLength ≤ 50 * base := by omega
  have periodEstimate : costPeriod ≤
      flatStripFieldCost 1 context stateCount state periodicStrip +
        costLength + 3 * (8 * unit) + 2 := by
    simpa [costPeriod, costLength, costFirstWord, costFirstPhase,
      costLastWord, costLastPhase] using estimatePeriod
  have periodBound : costPeriod ≤ 60 * base := by omega
  have widthEstimate : costWidth ≤
      flatStripFieldCost 0 context stateCount state periodicStrip +
        costPeriod + 3 * (8 * unit) + 2 := by
    simpa [costWidth, costPeriod, costLength, costFirstWord, costFirstPhase,
      costLastWord, costLastPhase] using estimateWidth
  have widthBound : costWidth ≤ 70 * base := by omega
  have finalBound : costWidth ≤ 100 * base := widthBound.trans (by omega)
  simpa [flatStripContextCost, flatStripContextSpaceBound, values, coordinates,
    firstWord, firstPhase, lastWord, lastPhase, costLastPhase, costLastWord,
    costFirstPhase, costFirstWord, costLength, costPeriod, costWidth, base] using
    finalBound

/-- Bounded fitted certificate for the complete seven-field flat transition
context. -/
theorem flatStripContextBounded
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits FlatStripEdgePartrec.contextCode
      (divideEvalProgramList context stateCount state ++
        PeriodicStripFlatEncoding.stripFields periodicStrip)
      ([periodicStrip.width, periodicStrip.period,
          periodicStrip.motif.length,
          state.query.first / periodicStrip.period,
          state.query.first % periodicStrip.period,
          state.query.last / periodicStrip.period,
          state.query.last % periodicStrip.period] ++
        periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields)
      (flatStripContextSpaceBound context stateCount state periodicStrip) :=
  (flatStripContext context stateCount state periodicStrip).mono
    (flatStripContextCost_le_bound context stateCount state periodicStrip)

end EvaluatorCodeFits
end PartrecToTM2
end Turing
