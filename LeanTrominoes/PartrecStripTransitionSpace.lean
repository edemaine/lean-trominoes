import LeanTrominoes.PartrecPackedTransitionSpace
import LeanTrominoes.PartrecStripFrontierContextSpace
import LeanTrominoes.PartrecStripTransition

/-!
# Evaluator-space certificate for the indexed strip transition

The fitted strip-context decoder feeds the fitted packed transition through
one fixed-width field permutation.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes
open LeanTrominoes.PeriodicStrip

namespace EvaluatorCodeFits

def stripPackedTransitionArgumentsCost
    (periodicStrip : PeriodicStrip) (first last : Nat) : Nat :=
  let values :=
    [periodicStrip.width, periodicStrip.period,
      Encodable.encode periodicStrip.motif,
      first / periodicStrip.period,
      first % periodicStrip.period,
      last / periodicStrip.period,
      last % periodicStrip.period]
  let nextFields := prependCost values
    [last % periodicStrip.period]
    [last / periodicStrip.period]
    (getCost 6 values) (getCost 5 values)
  let currentWord := prependCost values
    [first / periodicStrip.period]
    [last % periodicStrip.period, last / periodicStrip.period]
    (getCost 3 values) nextFields
  let motif := prependCost values
    [Encodable.encode periodicStrip.motif]
    [first / periodicStrip.period,
      last % periodicStrip.period, last / periodicStrip.period]
    (getCost 2 values) currentWord
  let currentPhase := prependCost values
    [first % periodicStrip.period]
    [Encodable.encode periodicStrip.motif,
      first / periodicStrip.period,
      last % periodicStrip.period, last / periodicStrip.period]
    (getCost 4 values) motif
  prependCost values [periodicStrip.period]
    [first % periodicStrip.period,
      Encodable.encode periodicStrip.motif,
      first / periodicStrip.period,
      last % periodicStrip.period, last / periodicStrip.period]
    (getCost 1 values) currentPhase

theorem stripPackedTransitionArguments
    (periodicStrip : PeriodicStrip) (first last : Nat) :
    EvaluatorCodeFits Code.stripPackedTransitionArgumentsCode
      [periodicStrip.width, periodicStrip.period,
        Encodable.encode periodicStrip.motif,
        first / periodicStrip.period,
        first % periodicStrip.period,
        last / periodicStrip.period,
        last % periodicStrip.period]
      [periodicStrip.period, first % periodicStrip.period,
        Encodable.encode periodicStrip.motif,
        first / periodicStrip.period,
        last % periodicStrip.period,
        last / periodicStrip.period]
      (stripPackedTransitionArgumentsCost
        periodicStrip first last) := by
  let values :=
    [periodicStrip.width, periodicStrip.period,
      Encodable.encode periodicStrip.motif,
      first / periodicStrip.period,
      first % periodicStrip.period,
      last / periodicStrip.period,
      last % periodicStrip.period]
  have nextFields := prepend (get 6 values) (get 5 values)
  have currentWord := prepend (get 3 values) nextFields
  have motif := prepend (get 2 values) currentWord
  have currentPhase := prepend (get 4 values) motif
  have result := prepend (get 1 values) currentPhase
  simpa [Code.stripPackedTransitionArgumentsCode,
    stripPackedTransitionArgumentsCost,
    prependCost, values] using result

def stripPackedTransitionCost
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat) : Nat :=
  let current := PackedWindowState.ofIndex periodicStrip first
  let next := PackedWindowState.ofIndex periodicStrip last
  packedTransitionCost tromino periodicStrip current next +
    stripPackedTransitionArgumentsCost periodicStrip first last

theorem stripPackedTransition
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first last : Nat) :
    EvaluatorCodeFits (Code.stripPackedTransitionCode tromino)
      [periodicStrip.width, periodicStrip.period,
        Encodable.encode periodicStrip.motif,
        first / periodicStrip.period,
        first % periodicStrip.period,
        last / periodicStrip.period,
        last % periodicStrip.period]
      [((PackedWindowState.ofIndex periodicStrip first).transitionBool
        tromino periodicStrip
          (PackedWindowState.ofIndex periodicStrip last)).toNat]
      (stripPackedTransitionCost
        tromino periodicStrip first last) := by
  let current := PackedWindowState.ofIndex periodicStrip first
  let next := PackedWindowState.ofIndex periodicStrip last
  simpa [Code.stripPackedTransitionCode,
    stripPackedTransitionCost, Code.packedTransitionInput,
    current, next, PackedWindowState.ofIndex] using
    comp (packedTransition
      tromino periodicStrip wellFormed current next)
      (stripPackedTransitionArguments periodicStrip first last)

set_option maxHeartbeats 1000000 in
/-- The fixed permutation from the seven-field strip context to the six-field
packed-transition input uses workspace linear in the encoded strip and two
frontier indices. -/
theorem stripPackedTransitionArgumentsCost_le_polynomialSpaceBound
    (periodicStrip : PeriodicStrip) (first last : Nat) :
    stripPackedTransitionArgumentsCost periodicStrip first last ≤
      10000000 * stripFrontierContextPolynomialSpaceUnit
        periodicStrip first last := by
  let stripCode := Encodable.encode periodicStrip
  let motifCode := Encodable.encode periodicStrip.motif
  let limit := stripFrontierContextPolynomialSpaceLimit
    periodicStrip first last
  let unit := stripFrontierContextPolynomialSpaceUnit
    periodicStrip first last
  have stripBound : stripCode ≤ limit := by
    simp only [stripCode, limit,
      stripFrontierContextPolynomialSpaceLimit]
    omega
  have firstBound : first ≤ limit := by
    simp only [limit, stripFrontierContextPolynomialSpaceLimit]
    omega
  have lastBound : last ≤ limit := by
    simp only [limit, stripFrontierContextPolynomialSpaceLimit]
    omega
  have widthStrip : periodicStrip.width ≤ stripCode := by
    simp only [stripCode, PeriodicStrip.encode_eq_pair]
    exact Nat.left_le_pair _ _
  have restStrip :
      Nat.pair periodicStrip.period motifCode ≤ stripCode := by
    simp only [stripCode, motifCode, PeriodicStrip.encode_eq_pair]
    exact Nat.right_le_pair _ _
  have periodStrip : periodicStrip.period ≤ stripCode :=
    (Nat.left_le_pair _ _).trans restStrip
  have motifStrip : motifCode ≤ stripCode :=
    (Nat.right_le_pair _ _).trans restStrip
  have widthBound := widthStrip.trans stripBound
  have periodBound := periodStrip.trans stripBound
  have motifBound := motifStrip.trans stripBound
  have firstQuotientBound : first / periodicStrip.period ≤ limit :=
    (Nat.div_le_self first periodicStrip.period).trans firstBound
  have firstRemainderBound : first % periodicStrip.period ≤ limit :=
    (Nat.mod_le first periodicStrip.period).trans firstBound
  have lastQuotientBound : last / periodicStrip.period ≤ limit :=
    (Nat.div_le_self last periodicStrip.period).trans lastBound
  have lastRemainderBound : last % periodicStrip.period ≤ limit :=
    (Nat.mod_le last periodicStrip.period).trans lastBound
  have widthBits := encodeNat_length_mono widthBound
  have periodBits := encodeNat_length_mono periodBound
  have motifBits := encodeNat_length_mono motifBound
  have firstQuotientBits := encodeNat_length_mono firstQuotientBound
  have firstRemainderBits := encodeNat_length_mono firstRemainderBound
  have lastQuotientBits := encodeNat_length_mono lastQuotientBound
  have lastRemainderBits := encodeNat_length_mono lastRemainderBound
  have widthSuccBits := encodeNat_length_mono
    (show periodicStrip.width + 1 ≤ limit by
      simp only [limit, stripFrontierContextPolynomialSpaceLimit]
      omega)
  have periodSuccBits := encodeNat_length_mono
    (show periodicStrip.period + 1 ≤ limit by
      simp only [limit, stripFrontierContextPolynomialSpaceLimit]
      omega)
  have motifSuccBits := encodeNat_length_mono
    (show motifCode + 1 ≤ limit by
      simp only [limit, stripFrontierContextPolynomialSpaceLimit,
        motifCode]
      omega)
  have firstQuotientSuccBits := encodeNat_length_mono
    (show first / periodicStrip.period + 1 ≤ limit by
      have raw := Nat.div_le_self first periodicStrip.period
      simp only [limit, stripFrontierContextPolynomialSpaceLimit]
      omega)
  have firstRemainderSuccBits := encodeNat_length_mono
    (show first % periodicStrip.period + 1 ≤ limit by
      have raw := Nat.mod_le first periodicStrip.period
      simp only [limit, stripFrontierContextPolynomialSpaceLimit]
      omega)
  have lastQuotientSuccBits := encodeNat_length_mono
    (show last / periodicStrip.period + 1 ≤ limit by
      have raw := Nat.div_le_self last periodicStrip.period
      simp only [limit, stripFrontierContextPolynomialSpaceLimit]
      omega)
  have lastRemainderSuccBits := encodeNat_length_mono
    (show last % periodicStrip.period + 1 ≤ limit by
      have raw := Nat.mod_le last periodicStrip.period
      simp only [limit, stripFrontierContextPolynomialSpaceLimit]
      omega)
  have motifBitsRaw :
      (Computability.encodeNat
        (Encodable.encode periodicStrip.motif)).length ≤
        (Computability.encodeNat limit).length := by
    simpa only [motifCode] using motifBits
  have motifSuccBitsRaw :
      (Computability.encodeNat
        (Encodable.encode periodicStrip.motif + 1)).length ≤
        (Computability.encodeNat limit).length := by
    simpa only [motifCode] using motifSuccBits
  have unitEq :
      unit = (Computability.encodeNat limit).length + 2 := by
    simp [unit, limit, stripFrontierContextPolynomialSpaceUnit,
      encodedListSpace_cons, encodedListSpace_nil]
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  simp [stripPackedTransitionArgumentsCost,
    prependCost, getCost, dropCost, headCost, idCost,
    nilCost, tailCost, zeroPrimeCost, succCost,
    encodedListSpace_cons, encodedListSpace_nil,
    zeroBits]
  clear * - widthBits periodBits motifBits
    firstQuotientBits firstRemainderBits
    lastQuotientBits lastRemainderBits
    widthSuccBits periodSuccBits motifSuccBits
    firstQuotientSuccBits firstRemainderSuccBits
    lastQuotientSuccBits lastRemainderSuccBits unitEq
    motifBitsRaw motifSuccBitsRaw
  omega

/-- The four native fields used by center validation occupy only a constant
multiple of the common strip-context workspace. -/
theorem stripPackedNormalizationInputUnit_le_contextUnit
    (periodicStrip : PeriodicStrip) (first last : Nat) :
    packedNormalizationInputUnit periodicStrip
        (PackedWindowState.ofIndex periodicStrip first) ≤
      10 * stripFrontierContextPolynomialSpaceUnit
        periodicStrip first last := by
  let stripCode := Encodable.encode periodicStrip
  let motifCode := Encodable.encode periodicStrip.motif
  let limit := stripFrontierContextPolynomialSpaceLimit
    periodicStrip first last
  have stripBound : stripCode ≤ limit := by
    simp only [stripCode, limit,
      stripFrontierContextPolynomialSpaceLimit]
    omega
  have firstBound : first ≤ limit := by
    simp only [limit, stripFrontierContextPolynomialSpaceLimit]
    omega
  have restStrip :
      Nat.pair periodicStrip.period motifCode ≤ stripCode := by
    simp only [stripCode, motifCode, PeriodicStrip.encode_eq_pair]
    exact Nat.right_le_pair _ _
  have periodBound : periodicStrip.period ≤ limit :=
    (Nat.left_le_pair _ _).trans (restStrip.trans stripBound)
  have motifBound : motifCode ≤ limit :=
    (Nat.right_le_pair _ _).trans (restStrip.trans stripBound)
  have phaseBound : first % periodicStrip.period ≤ limit :=
    (Nat.mod_le first periodicStrip.period).trans firstBound
  have wordBound : first / periodicStrip.period ≤ limit :=
    (Nat.div_le_self first periodicStrip.period).trans firstBound
  have periodBits := encodeNat_length_mono periodBound
  have phaseBits := encodeNat_length_mono phaseBound
  have motifBits := encodeNat_length_mono motifBound
  have wordBits := encodeNat_length_mono wordBound
  have motifBitsRaw :
      (Computability.encodeNat
        (Encodable.encode periodicStrip.motif)).length ≤
        (Computability.encodeNat limit).length := by
    simpa only [motifCode] using motifBits
  have contextEq :
      stripFrontierContextPolynomialSpaceUnit
          periodicStrip first last =
        (Computability.encodeNat limit).length + 2 := by
    simp [limit, stripFrontierContextPolynomialSpaceUnit,
      encodedListSpace_cons, encodedListSpace_nil]
  simp only [packedNormalizationInputUnit,
    PackedWindowState.ofIndex, encodedListSpace_cons,
    encodedListSpace_nil]
  rw [contextEq]
  omega

/-- The five-column normalization envelope remains linear in the encoded
strip and the two queried frontier indices. -/
theorem stripPackedNormalizationAllUnit_le_contextUnit
    (periodicStrip : PeriodicStrip) (first last : Nat) :
    packedNormalizationAllUnit periodicStrip
        (PackedWindowState.ofIndex periodicStrip first) ≤
      100 * stripFrontierContextPolynomialSpaceUnit
        periodicStrip first last := by
  let stripCode := Encodable.encode periodicStrip
  let motifCode := Encodable.encode periodicStrip.motif
  let limit := stripFrontierContextPolynomialSpaceLimit
    periodicStrip first last
  have stripBound : stripCode ≤ limit := by
    simp only [stripCode, limit,
      stripFrontierContextPolynomialSpaceLimit]
    omega
  have firstBound : first ≤ limit := by
    simp only [limit, stripFrontierContextPolynomialSpaceLimit]
    omega
  have restStrip :
      Nat.pair periodicStrip.period motifCode ≤ stripCode := by
    simp only [stripCode, motifCode, PeriodicStrip.encode_eq_pair]
    exact Nat.right_le_pair _ _
  have periodBound : periodicStrip.period ≤ limit :=
    (Nat.left_le_pair _ _).trans (restStrip.trans stripBound)
  have motifBound : motifCode ≤ limit :=
    (Nat.right_le_pair _ _).trans (restStrip.trans stripBound)
  have phaseBound : first % periodicStrip.period ≤ limit :=
    (Nat.mod_le first periodicStrip.period).trans firstBound
  have wordBound : first / periodicStrip.period ≤ limit :=
    (Nat.div_le_self first periodicStrip.period).trans firstBound
  have limitLarge : 1000 ≤ limit := by
    simp only [limit, stripFrontierContextPolynomialSpaceLimit]
    omega
  have rawBound :
      packedNormalizationAllLimit periodicStrip
          (PackedWindowState.ofIndex periodicStrip first) ≤
        1000000 * limit := by
    simp only [packedNormalizationAllLimit,
      PackedWindowState.ofIndex]
    simp only [motifCode] at motifBound
    omega
  have rawBits := encodeNat_length_mono rawBound
  have scaledBits := encodeNat_mul_length_le_sum 1000000 limit
  have coefficientBits :
      (Computability.encodeNat 1000000).length = 20 := by native_decide
  have contextEq :
      stripFrontierContextPolynomialSpaceUnit
          periodicStrip first last =
        (Computability.encodeNat limit).length + 2 := by
    simp [limit, stripFrontierContextPolynomialSpaceUnit,
      encodedListSpace_cons, encodedListSpace_nil]
  simp only [packedNormalizationAllUnit,
    encodedListSpace_cons, encodedListSpace_nil]
  rw [contextEq]
  rw [coefficientBits] at scaledBits
  omega

/-- The four-column overlap envelope remains linear in the encoded strip and
the two queried frontier indices. -/
theorem stripPackedOverlapColumnsUnit_le_contextUnit
    (periodicStrip : PeriodicStrip) (first last : Nat) :
    packedOverlapColumnsUnit periodicStrip
        (PackedWindowState.ofIndex periodicStrip first)
        (PackedWindowState.ofIndex periodicStrip last) ≤
      100 * stripFrontierContextPolynomialSpaceUnit
        periodicStrip first last := by
  let stripCode := Encodable.encode periodicStrip
  let motifCode := Encodable.encode periodicStrip.motif
  let limit := stripFrontierContextPolynomialSpaceLimit
    periodicStrip first last
  have stripBound : stripCode ≤ limit := by
    simp only [stripCode, limit,
      stripFrontierContextPolynomialSpaceLimit]
    omega
  have firstBound : first ≤ limit := by
    simp only [limit, stripFrontierContextPolynomialSpaceLimit]
    omega
  have lastBound : last ≤ limit := by
    simp only [limit, stripFrontierContextPolynomialSpaceLimit]
    omega
  have motifStrip : motifCode ≤ stripCode := by
    simp only [stripCode, motifCode, PeriodicStrip.encode_eq_pair]
    exact (Nat.right_le_pair _ _).trans (Nat.right_le_pair _ _)
  have motifBound := motifStrip.trans stripBound
  have firstWordBound : first / periodicStrip.period ≤ limit :=
    (Nat.div_le_self first periodicStrip.period).trans firstBound
  have lastWordBound : last / periodicStrip.period ≤ limit :=
    (Nat.div_le_self last periodicStrip.period).trans lastBound
  have limitLarge : 1000 ≤ limit := by
    simp only [limit, stripFrontierContextPolynomialSpaceLimit]
    omega
  have rawBound :
      packedOverlapColumnsLimit periodicStrip
          (PackedWindowState.ofIndex periodicStrip first)
          (PackedWindowState.ofIndex periodicStrip last) ≤
        1000000 * limit := by
    simp only [packedOverlapColumnsLimit,
      PackedWindowState.ofIndex]
    simp only [motifCode] at motifBound
    omega
  have rawBits := encodeNat_length_mono rawBound
  have scaledBits := encodeNat_mul_length_le_sum 1000000 limit
  have coefficientBits :
      (Computability.encodeNat 1000000).length = 20 := by native_decide
  have contextEq :
      stripFrontierContextPolynomialSpaceUnit
          periodicStrip first last =
        (Computability.encodeNat limit).length + 2 := by
    simp [limit, stripFrontierContextPolynomialSpaceUnit,
      encodedListSpace_cons, encodedListSpace_nil]
  simp only [packedOverlapColumnsUnit,
    encodedListSpace_cons, encodedListSpace_nil]
  rw [contextEq]
  rw [coefficientBits] at scaledBits
  omega

/-- The native packed-transition envelope remains linear in the encoded strip
and the two queried frontier indices. -/
theorem stripPackedTransitionNativeSpaceUnit_le_contextUnit
    (periodicStrip : PeriodicStrip) (first last : Nat) :
    packedTransitionNativeSpaceUnit periodicStrip
        (PackedWindowState.ofIndex periodicStrip first)
        (PackedWindowState.ofIndex periodicStrip last) ≤
      100 * stripFrontierContextPolynomialSpaceUnit
        periodicStrip first last := by
  let stripCode := Encodable.encode periodicStrip
  let motifCode := Encodable.encode periodicStrip.motif
  let limit := stripFrontierContextPolynomialSpaceLimit
    periodicStrip first last
  have stripBound : stripCode ≤ limit := by
    simp only [stripCode, limit,
      stripFrontierContextPolynomialSpaceLimit]
    omega
  have firstBound : first ≤ limit := by
    simp only [limit, stripFrontierContextPolynomialSpaceLimit]
    omega
  have lastBound : last ≤ limit := by
    simp only [limit, stripFrontierContextPolynomialSpaceLimit]
    omega
  have restStrip :
      Nat.pair periodicStrip.period motifCode ≤ stripCode := by
    simp only [stripCode, motifCode, PeriodicStrip.encode_eq_pair]
    exact Nat.right_le_pair _ _
  have periodBound : periodicStrip.period ≤ limit :=
    (Nat.left_le_pair _ _).trans (restStrip.trans stripBound)
  have motifBound : motifCode ≤ limit :=
    (Nat.right_le_pair _ _).trans (restStrip.trans stripBound)
  have firstPhaseBound : first % periodicStrip.period ≤ limit :=
    (Nat.mod_le first periodicStrip.period).trans firstBound
  have firstWordBound : first / periodicStrip.period ≤ limit :=
    (Nat.div_le_self first periodicStrip.period).trans firstBound
  have lastPhaseBound : last % periodicStrip.period ≤ limit :=
    (Nat.mod_le last periodicStrip.period).trans lastBound
  have lastWordBound : last / periodicStrip.period ≤ limit :=
    (Nat.div_le_self last periodicStrip.period).trans lastBound
  have limitLarge : 1000 ≤ limit := by
    simp only [limit, stripFrontierContextPolynomialSpaceLimit]
    omega
  have rawBound :
      packedTransitionPolynomialSpaceLimit periodicStrip
          (PackedWindowState.ofIndex periodicStrip first)
          (PackedWindowState.ofIndex periodicStrip last) ≤
        1000000 * limit := by
    simp only [packedTransitionPolynomialSpaceLimit,
      PackedWindowState.ofIndex]
    simp only [motifCode] at motifBound
    omega
  have rawBits := encodeNat_length_mono rawBound
  have scaledBits := encodeNat_mul_length_le_sum 1000000 limit
  have coefficientBits :
      (Computability.encodeNat 1000000).length = 20 := by native_decide
  have contextEq :
      stripFrontierContextPolynomialSpaceUnit
          periodicStrip first last =
        (Computability.encodeNat limit).length + 2 := by
    simp [limit, stripFrontierContextPolynomialSpaceUnit,
      encodedListSpace_cons, encodedListSpace_nil]
  simp only [packedTransitionNativeSpaceUnit,
    encodedListSpace_cons, encodedListSpace_nil]
  rw [contextEq]
  rw [coefficientBits] at scaledBits
  omega

/-- Constant coefficient that absorbs every primitive leaf of one packed
transition into the common strip-context unit. -/
def stripPackedTransitionComponentSpaceCoefficient
    (tromino : Tromino) : Nat :=
  10000000000000000000000000000000000000000000000000000 * 100 +
    packedCenterValidPolynomialSpaceBoundLinearCoefficient tromino * 10 +
    10000000000000000000000000000000000000000000000 * 100 +
    100000000000000000000000000000000 * 100 +
    10000000 * 100 + 1

private theorem scaledSucc_le_scaledUnit
    (value coefficient unit : Nat)
    (bounded : value ≤ coefficient * unit)
    (unitPositive : 1 ≤ unit) :
    1000 * (value + 1) ≤
      (1000 * (coefficient + 1)) * unit := by
  calc
    1000 * (value + 1) ≤
        1000 * (coefficient * unit + unit) := by
      exact Nat.mul_le_mul_left _
        (Nat.add_le_add bounded unitPositive)
    _ = (1000 * (coefficient + 1)) * unit := by ring

/-- The complete primitive-leaf sum of a packed indexed transition is linear
in the common strip-context workspace. -/
theorem stripPackedTransitionComponentSpaceBound_le_contextUnit
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    packedTransitionComponentSpaceBound tromino periodicStrip
        (PackedWindowState.ofIndex periodicStrip first)
        (PackedWindowState.ofIndex periodicStrip last) ≤
      stripPackedTransitionComponentSpaceCoefficient tromino *
        stripFrontierContextPolynomialSpaceUnit
          periodicStrip first last := by
  let unit := stripFrontierContextPolynomialSpaceUnit
    periodicStrip first last
  have unitPositive : 1 ≤ unit := by
    simp [unit, stripFrontierContextPolynomialSpaceUnit]
  have normalization :=
    stripPackedNormalizationAllUnit_le_contextUnit
      periodicStrip first last
  have centerInput :=
    stripPackedNormalizationInputUnit_le_contextUnit
      periodicStrip first last
  have centerRaw :=
    packedCenterValidPolynomialSpaceBound_le_input tromino periodicStrip
      (PackedWindowState.ofIndex periodicStrip first)
  have center :
      packedCenterValidPolynomialSpaceBound tromino periodicStrip
          (PackedWindowState.ofIndex periodicStrip first) ≤
        (packedCenterValidPolynomialSpaceBoundLinearCoefficient tromino * 10) *
          unit := by
    calc
      _ ≤ packedCenterValidPolynomialSpaceBoundLinearCoefficient tromino *
            packedNormalizationInputUnit periodicStrip
              (PackedWindowState.ofIndex periodicStrip first) := centerRaw
      _ ≤ packedCenterValidPolynomialSpaceBoundLinearCoefficient tromino *
            (10 * unit) := Nat.mul_le_mul_left _ centerInput
      _ = _ := by ring
  have overlap := stripPackedOverlapColumnsUnit_le_contextUnit
    periodicStrip first last
  have native := stripPackedTransitionNativeSpaceUnit_le_contextUnit
    periodicStrip first last
  simp only [packedTransitionComponentSpaceBound]
  change _ ≤ stripPackedTransitionComponentSpaceCoefficient tromino * unit
  calc
    _ ≤
        10000000000000000000000000000000000000000000000000000 *
            (100 * unit) +
          (packedCenterValidPolynomialSpaceBoundLinearCoefficient tromino * 10) *
            unit +
          10000000000000000000000000000000000000000000000 *
            (100 * unit) +
          100000000000000000000000000000000 * (100 * unit) +
          10000000 * (100 * unit) + unit := by
      gcongr
    _ = stripPackedTransitionComponentSpaceCoefficient tromino * unit := by
      simp only [stripPackedTransitionComponentSpaceCoefficient]
      ring

/-- Constant coefficient for all three Boolean-combinator layers of a packed
transition. -/
def stripPackedTransitionSpaceCoefficient (tromino : Tromino) : Nat :=
  1000 *
    (1000 *
      (1000 *
        (stripPackedTransitionComponentSpaceCoefficient tromino + 1) + 1) +
      1)

/-- The complete packed indexed-transition evaluator envelope is linear in
the common strip-context workspace. -/
theorem packedTransitionPolynomialSpaceBound_le_stripContextUnit
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    packedTransitionPolynomialSpaceBound tromino periodicStrip
        (PackedWindowState.ofIndex periodicStrip first)
        (PackedWindowState.ofIndex periodicStrip last) ≤
      stripPackedTransitionSpaceCoefficient tromino *
        stripFrontierContextPolynomialSpaceUnit
          periodicStrip first last := by
  let unit := stripFrontierContextPolynomialSpaceUnit
    periodicStrip first last
  have unitPositive : 1 ≤ unit := by
    simp [unit, stripFrontierContextPolynomialSpaceUnit]
  have component :=
    stripPackedTransitionComponentSpaceBound_le_contextUnit
      tromino periodicStrip first last
  have overlap := scaledSucc_le_scaledUnit
    (packedTransitionComponentSpaceBound tromino periodicStrip
      (PackedWindowState.ofIndex periodicStrip first)
      (PackedWindowState.ofIndex periodicStrip last))
    (stripPackedTransitionComponentSpaceCoefficient tromino)
    unit component unitPositive
  have tail := scaledSucc_le_scaledUnit
    (packedTransitionOverlapSpaceBound tromino periodicStrip
      (PackedWindowState.ofIndex periodicStrip first)
      (PackedWindowState.ofIndex periodicStrip last))
    (1000 * (stripPackedTransitionComponentSpaceCoefficient tromino + 1))
    unit (by simpa [packedTransitionOverlapSpaceBound] using overlap)
    unitPositive
  have whole := scaledSucc_le_scaledUnit
    (packedTransitionTailSpaceBound tromino periodicStrip
      (PackedWindowState.ofIndex periodicStrip first)
      (PackedWindowState.ofIndex periodicStrip last))
    (1000 *
      (1000 *
        (stripPackedTransitionComponentSpaceCoefficient tromino + 1) + 1))
    unit (by simpa [packedTransitionTailSpaceBound] using tail)
    unitPositive
  simpa [packedTransitionPolynomialSpaceBound,
    stripPackedTransitionSpaceCoefficient, unit] using whole

/-- Polynomial-space envelope for the packed transition after its fixed
seven-to-six-field adapter. -/
def stripPackedTransitionPolynomialSpaceBound
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat) : Nat :=
  packedTransitionPolynomialSpaceBound tromino periodicStrip
      (PackedWindowState.ofIndex periodicStrip first)
      (PackedWindowState.ofIndex periodicStrip last) +
    10000000 * stripFrontierContextPolynomialSpaceUnit
      periodicStrip first last

/-- Constant coefficient for the packed transition together with its fixed
seven-to-six-field argument adapter. -/
def stripPackedTransitionPolynomialSpaceCoefficient
    (tromino : Tromino) : Nat :=
  stripPackedTransitionSpaceCoefficient tromino + 10000000

theorem stripPackedTransitionPolynomialSpaceBound_le_contextUnit
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    stripPackedTransitionPolynomialSpaceBound
        tromino periodicStrip first last ≤
      stripPackedTransitionPolynomialSpaceCoefficient tromino *
        stripFrontierContextPolynomialSpaceUnit
          periodicStrip first last := by
  have packed :=
    packedTransitionPolynomialSpaceBound_le_stripContextUnit
      tromino periodicStrip first last
  simp only [stripPackedTransitionPolynomialSpaceBound,
    stripPackedTransitionPolynomialSpaceCoefficient]
  calc
    _ ≤ stripPackedTransitionSpaceCoefficient tromino *
          stripFrontierContextPolynomialSpaceUnit periodicStrip first last +
        10000000 *
          stripFrontierContextPolynomialSpaceUnit periodicStrip first last :=
      Nat.add_le_add_right packed _
    _ = _ := by ring

theorem stripPackedTransitionCost_le_polynomialSpaceBound
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    stripPackedTransitionCost tromino periodicStrip first last ≤
      stripPackedTransitionPolynomialSpaceBound
        tromino periodicStrip first last := by
  have transition := packedTransitionCost_le_polynomialSpaceBound
    tromino periodicStrip
    (PackedWindowState.ofIndex periodicStrip first)
    (PackedWindowState.ofIndex periodicStrip last)
  have arguments :=
    stripPackedTransitionArgumentsCost_le_polynomialSpaceBound
      periodicStrip first last
  simp only [stripPackedTransitionCost,
    stripPackedTransitionPolynomialSpaceBound]
  omega

def stripTransitionCost
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat) : Nat :=
  stripPackedTransitionCost tromino periodicStrip first last +
    stripFrontierContextCost periodicStrip first last

/-- Exact fitted certificate for the explicit indexed strip edge. -/
theorem stripTransition
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first last : Nat) :
    EvaluatorCodeFits (Code.stripTransitionCode tromino)
      [Encodable.encode periodicStrip, first, last]
      [(RawWindowState.indexedTransitionRawBool
        tromino periodicStrip first last).toNat]
      (stripTransitionCost
        tromino periodicStrip first last) := by
  rw [PackedWindowState.indexedTransitionRawBool_eq_packed]
  simpa [Code.stripTransitionCode,
    stripTransitionCost] using
    comp (stripPackedTransition
      tromino periodicStrip wellFormed first last)
      (stripFrontierContext periodicStrip first last)

/-- Complete polynomial-space envelope for the explicit indexed strip edge. -/
def stripTransitionPolynomialSpaceBound
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat) : Nat :=
  stripPackedTransitionPolynomialSpaceBound
      tromino periodicStrip first last +
    1000000000000000000000000000000000000000000000 *
      stripFrontierContextPolynomialSpaceUnit periodicStrip first last

/-- Constant coefficient for the complete indexed strip edge. -/
def stripTransitionPolynomialSpaceCoefficient
    (tromino : Tromino) : Nat :=
  stripPackedTransitionPolynomialSpaceCoefficient tromino +
    1000000000000000000000000000000000000000000000

theorem stripTransitionPolynomialSpaceBound_le_contextUnit
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    stripTransitionPolynomialSpaceBound
        tromino periodicStrip first last ≤
      stripTransitionPolynomialSpaceCoefficient tromino *
        stripFrontierContextPolynomialSpaceUnit
          periodicStrip first last := by
  have packed :=
    stripPackedTransitionPolynomialSpaceBound_le_contextUnit
      tromino periodicStrip first last
  simp only [stripTransitionPolynomialSpaceBound,
    stripTransitionPolynomialSpaceCoefficient]
  calc
    _ ≤ stripPackedTransitionPolynomialSpaceCoefficient tromino *
          stripFrontierContextPolynomialSpaceUnit periodicStrip first last +
        1000000000000000000000000000000000000000000000 *
          stripFrontierContextPolynomialSpaceUnit periodicStrip first last :=
      Nat.add_le_add_right packed _
    _ = _ := by ring

theorem stripTransitionCost_le_polynomialSpaceBound
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    stripTransitionCost tromino periodicStrip first last ≤
      stripTransitionPolynomialSpaceBound
        tromino periodicStrip first last := by
  have transition := stripPackedTransitionCost_le_polynomialSpaceBound
    tromino periodicStrip first last
  have context := stripFrontierContextCost_le_polynomialSpaceBound
    periodicStrip first last
  simp only [stripTransitionCost,
    stripTransitionPolynomialSpaceBound]
  omega

def stripTransitionEqualityArgumentsCost
    (periodicStrip : PeriodicStrip) (first last : Nat) : Nat :=
  let values := [Encodable.encode periodicStrip, first, last]
  prependCost values [first] [last]
    (getCost 1 values) (getCost 2 values)

theorem stripTransitionEqualityArguments
    (periodicStrip : PeriodicStrip) (first last : Nat) :
    EvaluatorCodeFits Code.stripTransitionEqualityArgumentsCode
      [Encodable.encode periodicStrip, first, last]
      [first, last]
      (stripTransitionEqualityArgumentsCost
        periodicStrip first last) := by
  simpa [Code.stripTransitionEqualityArgumentsCode,
    stripTransitionEqualityArgumentsCost, prependCost] using
    prepend
      (get 1 [Encodable.encode periodicStrip, first, last])
      (get 2 [Encodable.encode periodicStrip, first, last])

def stripTransitionEqualityCost
    (periodicStrip : PeriodicStrip) (first last : Nat) : Nat :=
  natEqCost first last +
    stripTransitionEqualityArgumentsCost periodicStrip first last

theorem stripTransitionEquality
    (periodicStrip : PeriodicStrip) (first last : Nat) :
    EvaluatorCodeFits Code.stripTransitionEqualityCode
      [Encodable.encode periodicStrip, first, last]
      [(decide (first = last)).toNat]
      (stripTransitionEqualityCost periodicStrip first last) := by
  have result := comp (natEq first last)
    (stripTransitionEqualityArguments periodicStrip first last)
  have tagEq :
      (decide (first = last)).toNat =
        if first = last then 1 else 0 := by
    by_cases equal : first = last <;> simp [equal]
  rw [tagEq]
  simpa [Code.stripTransitionEqualityCode,
    stripTransitionEqualityCost] using result

private theorem stripTransitionInputSpace_le_contextUnit
    (periodicStrip : PeriodicStrip) (first last : Nat) :
    encodedListSpace [Encodable.encode periodicStrip, first, last] ≤
      10 * stripFrontierContextPolynomialSpaceUnit
        periodicStrip first last := by
  let limit := stripFrontierContextPolynomialSpaceLimit
    periodicStrip first last
  let unit := stripFrontierContextPolynomialSpaceUnit
    periodicStrip first last
  have stripBits := encodeNat_length_mono
    (show Encodable.encode periodicStrip ≤ limit by
      simp only [limit, stripFrontierContextPolynomialSpaceLimit]
      omega)
  have firstBits := encodeNat_length_mono
    (show first ≤ limit by
      simp only [limit, stripFrontierContextPolynomialSpaceLimit]
      omega)
  have lastBits := encodeNat_length_mono
    (show last ≤ limit by
      simp only [limit, stripFrontierContextPolynomialSpaceLimit]
      omega)
  have unitEq :
      unit = (Computability.encodeNat limit).length + 2 := by
    simp [unit, limit, stripFrontierContextPolynomialSpaceUnit,
      encodedListSpace_cons, encodedListSpace_nil]
  simp only [encodedListSpace_cons, encodedListSpace_nil]
  rw [show stripFrontierContextPolynomialSpaceUnit
      periodicStrip first last = unit by rfl, unitEq]
  omega

private theorem stripTransitionInputHeadSpace_le_contextUnit
    (periodicStrip : PeriodicStrip) (first last : Nat) :
    (Computability.encodeNat
      [Encodable.encode periodicStrip, first, last].headI).length ≤
      10 * stripFrontierContextPolynomialSpaceUnit
        periodicStrip first last := by
  have raw := stripTransitionInputSpace_le_contextUnit
    periodicStrip first last
  simp at raw ⊢
  omega

private theorem stripTransitionInputHeadSuccSpace_le_contextUnit
    (periodicStrip : PeriodicStrip) (first last : Nat) :
    (Computability.encodeNat
      ([Encodable.encode periodicStrip, first, last].headI + 1)).length ≤
      20 * stripFrontierContextPolynomialSpaceUnit
        periodicStrip first last := by
  have headBits := stripTransitionInputHeadSpace_le_contextUnit
    periodicStrip first last
  have successor := encodeNat_succ_length_le
    [Encodable.encode periodicStrip, first, last].headI
  have successor' :
      (Computability.encodeNat
        ([Encodable.encode periodicStrip, first, last].headI + 1)).length ≤
      (Computability.encodeNat
        [Encodable.encode periodicStrip, first, last].headI).length + 1 := by
    simpa [Nat.succ_eq_add_one] using successor
  have unitPositive :
      1 ≤ stripFrontierContextPolynomialSpaceUnit
        periodicStrip first last := by
    simp [stripFrontierContextPolynomialSpaceUnit]
  omega

set_option maxHeartbeats 800000 in
theorem stripTransitionEqualityArgumentsCost_le_polynomialSpaceBound
    (periodicStrip : PeriodicStrip) (first last : Nat) :
    stripTransitionEqualityArgumentsCost periodicStrip first last ≤
      1000000 * stripFrontierContextPolynomialSpaceUnit
        periodicStrip first last := by
  let limit := stripFrontierContextPolynomialSpaceLimit
    periodicStrip first last
  let unit := stripFrontierContextPolynomialSpaceUnit
    periodicStrip first last
  have inputSpace := stripTransitionInputSpace_le_contextUnit
    periodicStrip first last
  simp only [encodedListSpace_cons, encodedListSpace_nil] at inputSpace
  have firstBits := encodeNat_length_mono
    (show first ≤ limit by
      simp only [limit, stripFrontierContextPolynomialSpaceLimit]
      omega)
  have lastBits := encodeNat_length_mono
    (show last ≤ limit by
      simp only [limit, stripFrontierContextPolynomialSpaceLimit]
      omega)
  have firstSuccBits := encodeNat_length_mono
    (show first + 1 ≤ limit by
      simp only [limit, stripFrontierContextPolynomialSpaceLimit]
      omega)
  have lastSuccBits := encodeNat_length_mono
    (show last + 1 ≤ limit by
      simp only [limit, stripFrontierContextPolynomialSpaceLimit]
      omega)
  have stripPairBitsRaw := encodeNat_length_mono
    (show Nat.pair periodicStrip.width
        (Nat.pair periodicStrip.period
          (Encodable.encode periodicStrip.motif)) ≤ limit by
      simpa only [PeriodicStrip.encode_eq_pair] using
        (show Encodable.encode periodicStrip ≤ limit by
          simp only [limit, stripFrontierContextPolynomialSpaceLimit]
          omega))
  have unitEq :
      unit = (Computability.encodeNat limit).length + 2 := by
    simp [unit, limit, stripFrontierContextPolynomialSpaceUnit,
      encodedListSpace_cons, encodedListSpace_nil]
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  simp [stripTransitionEqualityArgumentsCost,
    prependCost, getCost, dropCost, headCost, idCost,
    nilCost, tailCost, zeroPrimeCost, succCost,
    encodedListSpace_cons, encodedListSpace_nil, zeroBits]
  clear * - inputSpace firstBits lastBits firstSuccBits lastSuccBits
    stripPairBitsRaw unitEq
  omega

theorem stripTransitionEqualityCost_le_polynomialSpaceBound
    (periodicStrip : PeriodicStrip) (first last : Nat) :
    stripTransitionEqualityCost periodicStrip first last ≤
      10000000000000000000000 *
        stripFrontierContextPolynomialSpaceUnit
          periodicStrip first last := by
  let limit := stripFrontierContextPolynomialSpaceLimit
    periodicStrip first last
  let unit := stripFrontierContextPolynomialSpaceUnit
    periodicStrip first last
  have equality := natEqCost_le_linear first last
  have equalityLimit : 2 * (first + last) + 4 ≤ limit := by
    simp only [limit, stripFrontierContextPolynomialSpaceLimit]
    omega
  have equalityBits := encodeNat_length_mono equalityLimit
  have arguments :=
    stripTransitionEqualityArgumentsCost_le_polynomialSpaceBound
      periodicStrip first last
  have equalityUnitLe :
      encodedListSpace [2 * (first + last) + 4] + 1 ≤ unit := by
    simpa [unit, limit, stripFrontierContextPolynomialSpaceUnit,
      encodedListSpace_cons, encodedListSpace_nil] using equalityBits
  have equalityGlobal :
      natEqCost first last ≤ 10000000000 * unit :=
    equality.trans (Nat.mul_le_mul_left _ equalityUnitLe)
  simp only [stripTransitionEqualityCost]
  clear * - equalityGlobal arguments
  omega

private theorem boolOr_fit_bool
    {leftCode rightCode : Code} {values : List Nat}
    {leftCost rightCost : Nat}
    (left right : Bool)
    (leftFit : EvaluatorCodeFits leftCode values
      [left.toNat] leftCost)
    (rightFit : EvaluatorCodeFits rightCode values
      [right.toNat] rightCost) :
    EvaluatorCodeFits (Code.boolOr leftCode rightCode) values
      [(left || right).toNat]
      (boolOrCost values left.toNat right.toNat
        leftCost rightCost) := by
  have combined := boolOr leftFit rightFit
  cases left <;> cases right <;> simpa using combined

def stripBaseTransitionCost
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat) : Nat :=
  let values := [Encodable.encode periodicStrip, first, last]
  let equal := decide (first = last)
  let edge := RawWindowState.indexedTransitionRawBool
    tromino periodicStrip first last
  boolOrCost values equal.toNat edge.toNat
    (stripTransitionEqualityCost periodicStrip first last)
    (stripTransitionCost tromino periodicStrip first last)

/-- Common budget for equality, the indexed edge, and their shared input. -/
def stripBaseTransitionComponentSpaceBound
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat) : Nat :=
  stripTransitionPolynomialSpaceBound
      tromino periodicStrip first last +
    10000000000000000000000 *
      stripFrontierContextPolynomialSpaceUnit periodicStrip first last +
    10000000 *
      stripFrontierContextPolynomialSpaceUnit periodicStrip first last + 1

/-- Constant coefficient absorbing the equality test, edge test, and their
shared native input. -/
def stripBaseTransitionComponentSpaceCoefficient
    (tromino : Tromino) : Nat :=
  stripTransitionPolynomialSpaceCoefficient tromino +
    10000000000000000000000 + 10000000 + 1

theorem stripBaseTransitionComponentSpaceBound_le_contextUnit
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    stripBaseTransitionComponentSpaceBound
        tromino periodicStrip first last ≤
      stripBaseTransitionComponentSpaceCoefficient tromino *
        stripFrontierContextPolynomialSpaceUnit
          periodicStrip first last := by
  let unit := stripFrontierContextPolynomialSpaceUnit
    periodicStrip first last
  have unitPositive : 1 ≤ unit := by
    simp [unit, stripFrontierContextPolynomialSpaceUnit]
  have transition := stripTransitionPolynomialSpaceBound_le_contextUnit
    tromino periodicStrip first last
  simp only [stripBaseTransitionComponentSpaceBound]
  change _ ≤ stripBaseTransitionComponentSpaceCoefficient tromino * unit
  calc
    _ ≤ stripTransitionPolynomialSpaceCoefficient tromino * unit +
          10000000000000000000000 * unit + 10000000 * unit + unit := by
      gcongr
    _ = stripBaseTransitionComponentSpaceCoefficient tromino * unit := by
      simp only [stripBaseTransitionComponentSpaceCoefficient]
      ring

/-- Polynomial-space envelope for the reflexive-or-edge Savitch leaf. -/
def stripBaseTransitionPolynomialSpaceBound
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat) : Nat :=
  1000 * (stripBaseTransitionComponentSpaceBound
    tromino periodicStrip first last + 1)

/-- Constant coefficient for the complete reflexive-or-edge Savitch leaf. -/
def stripBaseTransitionPolynomialSpaceCoefficient
    (tromino : Tromino) : Nat :=
  1000 * (stripBaseTransitionComponentSpaceCoefficient tromino + 1)

theorem stripBaseTransitionPolynomialSpaceBound_le_contextUnit
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    stripBaseTransitionPolynomialSpaceBound
        tromino periodicStrip first last ≤
      stripBaseTransitionPolynomialSpaceCoefficient tromino *
        stripFrontierContextPolynomialSpaceUnit
          periodicStrip first last := by
  let unit := stripFrontierContextPolynomialSpaceUnit
    periodicStrip first last
  have unitPositive : 1 ≤ unit := by
    simp [unit, stripFrontierContextPolynomialSpaceUnit]
  have component :=
    stripBaseTransitionComponentSpaceBound_le_contextUnit
      tromino periodicStrip first last
  simpa [stripBaseTransitionPolynomialSpaceBound,
    stripBaseTransitionPolynomialSpaceCoefficient, unit] using
      scaledSucc_le_scaledUnit
        (stripBaseTransitionComponentSpaceBound
          tromino periodicStrip first last)
        (stripBaseTransitionComponentSpaceCoefficient tromino)
        unit component unitPositive

/-- Exact fitted certificate for the explicit depth-zero Savitch predicate. -/
theorem stripBaseTransition
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first last : Nat) :
    EvaluatorCodeFits (Code.stripBaseTransitionCode tromino)
      [Encodable.encode periodicStrip, first, last]
      [((decide (first = last)) ||
        RawWindowState.indexedTransitionRawBool
          tromino periodicStrip first last).toNat]
      (stripBaseTransitionCost
        tromino periodicStrip first last) := by
  let equal := decide (first = last)
  let edge := RawWindowState.indexedTransitionRawBool
    tromino periodicStrip first last
  have result := boolOr_fit_bool equal edge
    (by simpa [equal] using
      (stripTransitionEquality periodicStrip first last))
    (by simpa [edge] using
      (stripTransition tromino periodicStrip wellFormed first last))
  simpa [Code.stripBaseTransitionCode,
    stripBaseTransitionCost, equal, edge] using result

set_option maxHeartbeats 1000000 in
theorem stripBaseTransitionCost_le_polynomialSpaceBound
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    stripBaseTransitionCost tromino periodicStrip first last ≤
      stripBaseTransitionPolynomialSpaceBound
        tromino periodicStrip first last := by
  let values := [Encodable.encode periodicStrip, first, last]
  let equal := decide (first = last)
  let edge := RawWindowState.indexedTransitionRawBool
    tromino periodicStrip first last
  let budget := stripBaseTransitionComponentSpaceBound
    tromino periodicStrip first last
  have equalTag : equal.toNat ≤ 1 := by
    cases equal <;> simp
  have edgeTag : edge.toNat ≤ 1 := by
    cases edge <;> simp
  have valuesNative := stripTransitionInputSpace_le_contextUnit
    periodicStrip first last
  have headNative := stripTransitionInputHeadSpace_le_contextUnit
    periodicStrip first last
  have headSuccNative :=
    stripTransitionInputHeadSuccSpace_le_contextUnit
      periodicStrip first last
  have valuesBound : encodedListSpace values ≤ budget := by
    simp only [values, budget,
      stripBaseTransitionComponentSpaceBound] at valuesNative ⊢
    omega
  have headBound :
      (Computability.encodeNat values.headI).length ≤ budget := by
    simp only [values, budget,
      stripBaseTransitionComponentSpaceBound] at headNative ⊢
    omega
  have headSuccBound :
      (Computability.encodeNat (values.headI + 1)).length ≤ budget := by
    simp only [values, budget,
      stripBaseTransitionComponentSpaceBound] at headSuccNative ⊢
    omega
  have equalityCost :=
    stripTransitionEqualityCost_le_polynomialSpaceBound
      periodicStrip first last
  have transitionCost := stripTransitionCost_le_polynomialSpaceBound
    tromino periodicStrip first last
  have equalityBound :
      stripTransitionEqualityCost periodicStrip first last ≤ budget := by
    simp only [budget, stripBaseTransitionComponentSpaceBound]
    omega
  have transitionBound :
      stripTransitionCost tromino periodicStrip first last ≤ budget := by
    simp only [budget, stripBaseTransitionComponentSpaceBound]
    omega
  have positive : 1 ≤ budget := by
    simp [budget, stripBaseTransitionComponentSpaceBound]
  have bound := boolOrCost_le_budget values
    equal.toNat edge.toNat
    (stripTransitionEqualityCost periodicStrip first last)
    (stripTransitionCost tromino periodicStrip first last)
    budget equalTag edgeTag valuesBound headBound headSuccBound
    equalityBound transitionBound positive
  simpa [stripBaseTransitionCost,
    stripBaseTransitionPolynomialSpaceBound,
    values, equal, edge, budget] using bound

end EvaluatorCodeFits

end PartrecToTM2
end Turing
