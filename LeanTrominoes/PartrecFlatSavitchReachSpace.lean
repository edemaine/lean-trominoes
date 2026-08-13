import LeanTrominoes.PartrecFlatSavitchStepSpace
import LeanTrominoes.PeriodicStripFlatEncodingSize

/-!
# Native-input bounds for flat Savitch reachability

The legacy strip driver chooses its recursion depth from a recursively paired
encoding.  This module instead fixes the same sufficient linear depth from the
target flat encoding, proves that its power-of-two ambient graph contains the
sparse frontier graph, and bounds every reachable serialized DFS state while
retaining the complete native strip suffix.  It then absorbs context recovery,
the reconstructed edge oracle, and every structural branch into one uniform
input-polynomial step allowance.
-/

namespace LeanTrominoes
namespace PeriodicStrip
namespace RawWindowState

open Computability
open Turing.PartrecToTM2

/-- Sufficient Savitch depth measured in the target flat strip encoding. -/
def flatStripSearchDepth (periodicStrip : PeriodicStrip) : Nat :=
  21 * (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length + 1

/-- Power-of-two ambient graph count associated with the flat input. -/
def flatStripStateBound (periodicStrip : PeriodicStrip) : Nat :=
  2 ^ flatStripSearchDepth periodicStrip

theorem indexCount_le_pow_flatStripSearchDepth
    (periodicStrip : PeriodicStrip) :
    indexCount periodicStrip ≤ 2 ^ flatStripSearchDepth periodicStrip := by
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  rw [indexCount_eq]
  calc
    periodicStrip.period * 9 ^ (5 * periodicStrip.motif.length) ≤
        2 ^ Nat.clog 2 periodicStrip.period *
          (2 ^ 4) ^ (5 * periodicStrip.motif.length) :=
      Nat.mul_le_mul
        (Nat.le_pow_clog Nat.one_lt_two periodicStrip.period)
        (Nat.pow_le_pow_left (by omega) _)
    _ = 2 ^ (Nat.clog 2 periodicStrip.period +
        20 * periodicStrip.motif.length) := by
      rw [← pow_mul, ← pow_add]
      congr 2
      omega
    _ ≤ 2 ^ (21 * inputLength + 1) := by
      apply Nat.pow_le_pow_right (by omega)
      have periodBound :=
        PeriodicStripFlatEncoding.clog_period_le_encoding_length periodicStrip
      have motifBound :=
        PeriodicStripFlatEncoding.motif_length_le_encoding_length periodicStrip
      dsimp only [inputLength] at periodBound motifBound ⊢
      omega
    _ = 2 ^ flatStripSearchDepth periodicStrip := by
      simp [flatStripSearchDepth, inputLength]

theorem indexCount_le_flatStripStateBound
    (periodicStrip : PeriodicStrip) :
    indexCount periodicStrip ≤ flatStripStateBound periodicStrip := by
  exact indexCount_le_pow_flatStripSearchDepth periodicStrip

theorem flatStripStateBound_le_pow_depth_succ
    (periodicStrip : PeriodicStrip) :
    flatStripStateBound periodicStrip ≤
      2 ^ (flatStripSearchDepth periodicStrip + 1) := by
  simp [flatStripStateBound]
  exact Nat.pow_le_pow_right (by omega) (Nat.le_succ _)

theorem flatStripSearchDepth_lt_pow_succ
    (periodicStrip : PeriodicStrip) :
    flatStripSearchDepth periodicStrip <
      2 ^ (flatStripSearchDepth periodicStrip + 1) := by
  exact (flatStripSearchDepth periodicStrip).lt_two_pow_self.trans_le
    (Nat.pow_le_pow_right (by omega) (Nat.le_succ _))

/-- Every reachable DFS state has quadratic native-list space in the flat
input length, including a power-of-two ambient graph count. -/
theorem flatStripDivideEvalIterate_encodedListSpace_le
    (periodicStrip : PeriodicStrip)
    (relation : Nat → Nat → Bool)
    (first last steps : Nat)
    (firstBelow : first < flatStripStateBound periodicStrip)
    (lastBelow : last < flatStripStateBound periodicStrip) :
    encodedListSpace
        (((FiniteState.divideEvalStep
          (flatStripStateBound periodicStrip) relation)^[steps])
          (FiniteState.divideEvalInitial
            (flatStripSearchDepth periodicStrip) first last)).toNatList ≤
      stripDFSPartrecSpaceBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  have generic :=
    FiniteState.divideEvalIterate_encodedListSpace_le
      (flatStripStateBound periodicStrip)
      (flatStripSearchDepth periodicStrip)
      (flatStripSearchDepth periodicStrip + 1)
      first last steps relation firstBelow lastBelow
      (flatStripStateBound_le_pow_depth_succ periodicStrip)
      (flatStripSearchDepth_lt_pow_succ periodicStrip)
  simpa [flatStripSearchDepth, stripDFSPartrecSpaceBound] using generic

/-- Uniform native-list footprint for a reachable DFS state followed by the
unchanged flat strip fields. -/
def flatStripReachStateSpaceBound (inputLength : Nat) : Nat :=
  stripDFSPartrecSpaceBound inputLength + 43 * inputLength + 10

theorem flatStripReachStateSpace_le
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last steps : Nat)
    (firstBelow : first < flatStripStateBound periodicStrip)
    (lastBelow : last < flatStripStateBound periodicStrip) :
    let state :=
      ((FiniteState.divideEvalStep (flatStripStateBound periodicStrip)
        (indexedTransitionRawBool tromino periodicStrip))^[steps])
          (FiniteState.divideEvalInitial
            (flatStripSearchDepth periodicStrip) first last)
    encodedListSpace
        (FiniteState.divideEvalProgramList 0
          (flatStripStateBound periodicStrip) state ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) ≤
      flatStripReachStateSpaceBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  dsimp only
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  let depth := flatStripSearchDepth periodicStrip
  let state :=
    ((FiniteState.divideEvalStep (flatStripStateBound periodicStrip)
      (indexedTransitionRawBool tromino periodicStrip))^[steps])
        (FiniteState.divideEvalInitial depth first last)
  have stateSpace := flatStripDivideEvalIterate_encodedListSpace_le
    periodicStrip (indexedTransitionRawBool tromino periodicStrip)
    first last steps firstBelow lastBelow
  have countBits :
      (Computability.encodeNat (flatStripStateBound periodicStrip)).length ≤
        depth + 1 := by
    apply FiniteState.encodeNat_length_le_of_lt_pow
    simpa [depth, flatStripStateBound] using
      (Nat.pow_lt_pow_right (show 1 < 2 by omega)
        (show flatStripSearchDepth periodicStrip <
          flatStripSearchDepth periodicStrip + 1 by omega))
  have stackLength : state.stack.length ≤ depth := by
    exact FiniteState.divideEvalIterate_stack_length_le_depth
      (flatStripStateBound periodicStrip) depth first last steps
      (indexedTransitionRawBool tromino periodicStrip)
  have stackBits :
      (Computability.encodeNat state.stack.length).length ≤ depth + 1 := by
    apply FiniteState.encodeNat_length_le_of_lt_pow
    exact stackLength.trans_lt
      (flatStripSearchDepth_lt_pow_succ periodicStrip)
  have suffixSpace :
      encodedListSpace (PeriodicStripFlatEncoding.stripFields periodicStrip) =
        inputLength := by
    dsimp only [inputLength]
    rw [encodedListSpace_eq_sum]
    exact (PeriodicStripFlatEncoding.finEncoding_encode_length
      periodicStrip).symm
  have depthEq : depth = 21 * inputLength + 1 := by
    simp [depth, inputLength, flatStripSearchDepth]
  have stateSpace' : encodedListSpace state.toNatList ≤
      stripDFSPartrecSpaceBound inputLength := by
    simpa [state, depth, inputLength] using stateSpace
  change encodedListSpace
    ((0 :: flatStripStateBound periodicStrip :: state.stack.length ::
      state.toNatList) ++
        PeriodicStripFlatEncoding.stripFields periodicStrip) ≤ _
  rw [FiniteState.encodedListSpace_append, suffixSpace]
  simp only [encodedListSpace_cons]
  change _ ≤ flatStripReachStateSpaceBound inputLength
  simp only [flatStripReachStateSpaceBound]
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  rw [zeroBits]
  omega

/-- Exact-fuel bit allowance for the native flat search parameters. -/
def flatStripFuelBits (inputLength : Nat) : Nat :=
  (21 * inputLength + 2) * (21 * inputLength + 5) + 1

theorem flatStripFuel_encodeNat_length_le
    (periodicStrip : PeriodicStrip) :
    (Computability.encodeNat
      (FiniteState.divideEvalFuel
        (flatStripStateBound periodicStrip)
        (flatStripSearchDepth periodicStrip))).length ≤
      flatStripFuelBits
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  let depth := flatStripSearchDepth periodicStrip
  let bits := depth + 1
  have fuelBound := FiniteState.divideEvalFuel_lt_pow_succ
    (flatStripStateBound periodicStrip) depth bits
    (by simpa [bits, depth] using
      flatStripStateBound_le_pow_depth_succ periodicStrip)
  have encodedBound :=
    FiniteState.encodeNat_length_le_of_lt_pow _ _ fuelBound
  simpa [inputLength, depth, bits, flatStripSearchDepth,
    flatStripFuelBits] using encodedBound

/-- Common bound for a remaining fuel counter and a reachable native-suffix
DFS payload. -/
def flatStripReachPayloadSpaceBound (inputLength : Nat) : Nat :=
  flatStripReachStateSpaceBound inputLength + flatStripFuelBits inputLength + 2

theorem flatStripReachCountdownSpace_le
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last steps remaining : Nat)
    (firstBelow : first < flatStripStateBound periodicStrip)
    (lastBelow : last < flatStripStateBound periodicStrip)
    (remainingBound : remaining ≤ FiniteState.divideEvalFuel
      (flatStripStateBound periodicStrip)
      (flatStripSearchDepth periodicStrip)) :
    let state :=
      ((FiniteState.divideEvalStep (flatStripStateBound periodicStrip)
        (indexedTransitionRawBool tromino periodicStrip))^[steps])
          (FiniteState.divideEvalInitial
            (flatStripSearchDepth periodicStrip) first last)
    encodedListSpace
        (remaining ::
          (FiniteState.divideEvalProgramList 0
            (flatStripStateBound periodicStrip) state ++
            PeriodicStripFlatEncoding.stripFields periodicStrip)) ≤
      flatStripReachPayloadSpaceBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  dsimp only
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  let state :=
    ((FiniteState.divideEvalStep (flatStripStateBound periodicStrip)
      (indexedTransitionRawBool tromino periodicStrip))^[steps])
        (FiniteState.divideEvalInitial
          (flatStripSearchDepth periodicStrip) first last)
  have stateSpace := flatStripReachStateSpace_le tromino periodicStrip
    first last steps firstBelow lastBelow
  have fuelBits := flatStripFuel_encodeNat_length_le periodicStrip
  have remainingBits := encodeNat_length_mono remainingBound
  have stateSpace' :
      encodedListSpace
          (FiniteState.divideEvalProgramList 0
            (flatStripStateBound periodicStrip) state ++
            PeriodicStripFlatEncoding.stripFields periodicStrip) ≤
        flatStripReachStateSpaceBound inputLength := by
    simpa [state, inputLength] using stateSpace
  have fuelBits' :
      (Computability.encodeNat
        (FiniteState.divideEvalFuel
          (flatStripStateBound periodicStrip)
          (flatStripSearchDepth periodicStrip))).length ≤
        flatStripFuelBits inputLength := by
    simpa [inputLength] using fuelBits
  have remainingBits' :
      (Computability.encodeNat remaining).length ≤
        flatStripFuelBits inputLength :=
    remainingBits.trans fuelBits'
  have totalSpace :
      (Computability.encodeNat remaining).length + 1 +
          encodedListSpace
            (FiniteState.divideEvalProgramList 0
              (flatStripStateBound periodicStrip) state ++
              PeriodicStripFlatEncoding.stripFields periodicStrip) ≤
        flatStripReachPayloadSpaceBound inputLength := by
    simp only [flatStripReachPayloadSpaceBound]
    omega
  simpa [state, inputLength, encodedListSpace_cons] using totalSpace

/-! ## Uniform bound for one reachable flat Savitch step -/

open Turing.PartrecToTM2.EvaluatorCodeFits

theorem flatStripCounter_encodeNat_length_le
    (periodicStrip : PeriodicStrip) (counter : Nat)
    (counterBound : counter < flatStripStateBound periodicStrip) :
    (Computability.encodeNat counter).length ≤
      21 * (PeriodicStripFlatEncoding.finEncoding.encode
        periodicStrip).length + 1 := by
  have encoded := FiniteState.encodeNat_length_le_of_lt_pow
    counter (flatStripSearchDepth periodicStrip) (by
      simpa [flatStripStateBound] using counterBound)
  simpa [flatStripSearchDepth] using encoded

/-- Both bounded frontier indices and the native period fit in one linear
arithmetic-decoding unit. -/
theorem frontierPairPolynomialSpaceUnit_le_flat_input
    (periodicStrip : PeriodicStrip) (first last : Nat)
    (firstBound : first < flatStripStateBound periodicStrip)
    (lastBound : last < flatStripStateBound periodicStrip) :
    frontierPairPolynomialSpaceUnit periodicStrip.period first last ≤
      100 * (PeriodicStripFlatEncoding.finEncoding.encode
        periodicStrip).length + 100 := by
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  let limit := frontierPairPolynomialSpaceLimit
    periodicStrip.period first last
  have periodBits :=
    PeriodicStripFlatEncoding.period_encodeNat_length_le_encoding_length
      periodicStrip
  have firstBits := flatStripCounter_encodeNat_length_le
    periodicStrip first firstBound
  have lastBits := flatStripCounter_encodeNat_length_le
    periodicStrip last lastBound
  have sum1 := encodeNat_add_length_le_sum periodicStrip.period first
  have sum2 := encodeNat_add_length_le_sum
    (periodicStrip.period + first) last
  have sum3 := encodeNat_add_length_le_sum
    (periodicStrip.period + first + last) 20
  have scaled := encodeNat_mul_length_le_sum 16
    (periodicStrip.period + first + last + 20)
  have final := encodeNat_add_length_le_sum
    (16 * (periodicStrip.period + first + last + 20)) 100
  have sixteenBits : (Computability.encodeNat 16).length = 5 := by
    native_decide
  have twentyBits : (Computability.encodeNat 20).length = 5 := by
    native_decide
  have hundredBits : (Computability.encodeNat 100).length = 7 := by
    native_decide
  have limitEq :
      limit = 16 * (periodicStrip.period + first + last + 20) + 100 := by
    simp [limit, frontierPairPolynomialSpaceLimit]
  rw [← limitEq] at final
  rw [sixteenBits] at scaled
  rw [twentyBits] at sum3
  rw [hundredBits] at final
  have unitEq :
      frontierPairPolynomialSpaceUnit periodicStrip.period first last =
        (Computability.encodeNat limit).length + 2 := by
    simp [limit, frontierPairPolynomialSpaceUnit,
      encodedListSpace_cons, encodedListSpace_nil]
  rw [unitEq]
  change (Computability.encodeNat limit).length + 2 ≤
    100 * inputLength + 100
  dsimp only [inputLength] at periodBits firstBits lastBits ⊢
  omega

/-- Master local footprint for a reachable DFS payload and its two decoded
frontier indices. -/
def flatStripLeafSpaceUnit (inputLength : Nat) : Nat :=
  flatStripReachStateSpaceBound inputLength + 100 * inputLength + 120

theorem flatStripContextSpaceUnit_le_leaf
    (periodicStrip : PeriodicStrip) (state : FiniteState.DivideEvalState)
    (indices : state.IndicesBelow (flatStripStateBound periodicStrip))
    (stateSpace :
      encodedListSpace
          (FiniteState.divideEvalProgramList 0
            (flatStripStateBound periodicStrip) state ++
            PeriodicStripFlatEncoding.stripFields periodicStrip) ≤
        flatStripReachStateSpaceBound
          (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length) :
    flatStripContextSpaceUnit 0 (flatStripStateBound periodicStrip)
        state periodicStrip ≤
      flatStripLeafSpaceUnit
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  have pair := frontierPairPolynomialSpaceUnit_le_flat_input periodicStrip
    state.query.first state.query.last indices.1.1 indices.1.2
  have stateSpace' :
      encodedListSpace
          (FiniteState.divideEvalProgramList 0
            (flatStripStateBound periodicStrip) state ++
            PeriodicStripFlatEncoding.stripFields periodicStrip) ≤
        flatStripReachStateSpaceBound inputLength := by
    simpa [inputLength] using stateSpace
  have pair' : frontierPairPolynomialSpaceUnit periodicStrip.period
      state.query.first state.query.last ≤ 100 * inputLength + 100 := by
    simpa [inputLength] using pair
  change _ ≤ flatStripLeafSpaceUnit inputLength
  simp only [flatStripContextSpaceUnit, flatStripLeafSpaceUnit]
  omega

/-- Context-recovery and seven-field reconstruction allowance after replacing
all state-dependent units by `flatStripLeafSpaceUnit`. -/
def flatStripContextUniformSpaceBound (inputLength : Nat) : Nat :=
  let unit := flatStripLeafSpaceUnit inputLength
  1000000000000000000000000000000000000000000000000000000000000000 * unit +
    1000000000000000000000000000000 * unit +
    1000000000 * unit

theorem flatStripContextBaseSpaceBound_le_uniform
    (periodicStrip : PeriodicStrip) (state : FiniteState.DivideEvalState)
    (indices : state.IndicesBelow (flatStripStateBound periodicStrip))
    (stateSpace :
      encodedListSpace
          (FiniteState.divideEvalProgramList 0
            (flatStripStateBound periodicStrip) state ++
            PeriodicStripFlatEncoding.stripFields periodicStrip) ≤
        flatStripReachStateSpaceBound
          (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length) :
    flatStripContextBaseSpaceBound 0 (flatStripStateBound periodicStrip)
        state periodicStrip ≤
      flatStripContextUniformSpaceBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  let unit := flatStripLeafSpaceUnit inputLength
  have contextUnit := flatStripContextSpaceUnit_le_leaf periodicStrip state
    indices stateSpace
  have pair := frontierPairPolynomialSpaceUnit_le_flat_input periodicStrip
    state.query.first state.query.last indices.1.1 indices.1.2
  have pair' : frontierPairPolynomialSpaceUnit periodicStrip.period
      state.query.first state.query.last ≤ 100 * inputLength + 100 := by
    simpa [inputLength] using pair
  have pairUnit : frontierPairPolynomialSpaceUnit periodicStrip.period
      state.query.first state.query.last ≤ unit := by
    simp only [unit, flatStripLeafSpaceUnit]
    omega
  have recoveryUnit :
      flatContextSpaceUnit 0 (flatStripStateBound periodicStrip) state
          (PeriodicStripFlatEncoding.stripFields periodicStrip) ≤ unit := by
    simp only [flatContextSpaceUnit]
    have localState : encodedListSpace
        (FiniteState.divideEvalProgramList 0
          (flatStripStateBound periodicStrip) state ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) ≤
        flatStripReachStateSpaceBound inputLength := by
      simpa [inputLength] using stateSpace
    simp only [unit, flatStripLeafSpaceUnit]
    omega
  simp only [flatStripContextBaseSpaceBound, flatContextSpaceBound,
    flatStripContextUniformSpaceBound]
  simpa [unit, inputLength] using (show
    1000000000000000000000000000000000000000000000000000000000000000 *
          flatContextSpaceUnit 0 (flatStripStateBound periodicStrip) state
            (PeriodicStripFlatEncoding.stripFields periodicStrip) +
        1000000000000000000000000000000 *
          frontierPairPolynomialSpaceUnit periodicStrip.period
            state.query.first state.query.last +
        1000000000 *
          flatStripContextSpaceUnit 0 (flatStripStateBound periodicStrip)
            state periodicStrip ≤
      1000000000000000000000000000000000000000000000000000000000000000 * unit +
        1000000000000000000000000000000 * unit +
        1000000000 * unit by
    gcongr)

def flatStripPackedTransitionUnitBound (inputLength : Nat) : Nat :=
  8 * flatStripLeafSpaceUnit inputLength + 10

def flatStripPackedTransitionUniformSpaceBound (inputLength : Nat) : Nat :=
  flatPackedTransitionSpaceEnvelope
    (flatStripPackedTransitionUnitBound inputLength)

theorem flatPackedTransitionSpaceBound_le_flat_uniform
    (periodicStrip : PeriodicStrip) (state : FiniteState.DivideEvalState)
    (indices : state.IndicesBelow (flatStripStateBound periodicStrip))
    (stateSpace :
      encodedListSpace
          (FiniteState.divideEvalProgramList 0
            (flatStripStateBound periodicStrip) state ++
            PeriodicStripFlatEncoding.stripFields periodicStrip) ≤
        flatStripReachStateSpaceBound
          (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length) :
    flatPackedTransitionSpaceBound periodicStrip
        (PackedWindowState.ofIndex periodicStrip state.query.first)
        (PackedWindowState.ofIndex periodicStrip state.query.last) ≤
      flatStripPackedTransitionUniformSpaceBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  let current := PackedWindowState.ofIndex periodicStrip state.query.first
  let next := PackedWindowState.ofIndex periodicStrip state.query.last
  have localUnit := flatStripContextSpaceUnit_le_leaf periodicStrip state
    indices stateSpace
  have localUnit' : flatStripContextSpaceUnit 0
      (flatStripStateBound periodicStrip) state periodicStrip ≤
      flatStripLeafSpaceUnit inputLength := by
    simpa [inputLength] using localUnit
  have output := flatStripContextOutputSpace_le 0
    (flatStripStateBound periodicStrip) state periodicStrip
  have packedUnit : flatPackedTransitionContextUnit periodicStrip current next ≤
      flatStripPackedTransitionUnitBound inputLength := by
    simp only [flatPackedTransitionContextUnit,
      flatStripPackedTransitionUnitBound]
    have output' : encodedListSpace
        (Turing.ToPartrec.Code.flatPackedTransitionContext periodicStrip
          current next) ≤
        8 * flatStripContextSpaceUnit 0
          (flatStripStateBound periodicStrip) state periodicStrip := by
      simpa [current, next, Turing.ToPartrec.Code.flatPackedTransitionContext,
        PackedWindowState.ofIndex] using output
    omega
  rw [flatPackedTransitionSpaceBound_eq_envelope]
  exact flatPackedTransitionSpaceEnvelope_mono packedUnit

private theorem flatStripEqualityArgumentSpace_le_leaf
    (periodicStrip : PeriodicStrip) (state : FiniteState.DivideEvalState)
    (indices : state.IndicesBelow (flatStripStateBound periodicStrip)) :
    encodedListSpace
        [2 * (state.query.first + state.query.last) + 4] + 1 ≤
      flatStripLeafSpaceUnit
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  have pair := frontierPairPolynomialSpaceUnit_le_flat_input periodicStrip
    state.query.first state.query.last indices.1.1 indices.1.2
  have numeric : 2 * (state.query.first + state.query.last) + 4 ≤
      frontierPairPolynomialSpaceLimit periodicStrip.period
        state.query.first state.query.last := by
    simp only [frontierPairPolynomialSpaceLimit]
    omega
  have bits := encodeNat_length_mono numeric
  have toPair : encodedListSpace
        [2 * (state.query.first + state.query.last) + 4] + 1 ≤
      frontierPairPolynomialSpaceUnit periodicStrip.period
        state.query.first state.query.last := by
    simp only [frontierPairPolynomialSpaceUnit, encodedListSpace_cons,
      encodedListSpace_nil] at bits ⊢
    omega
  exact toPair.trans (pair.trans (by
    simp [flatStripLeafSpaceUnit]
    omega))

/-- Uniform complete depth-zero oracle allowance on every reachable native
Savitch state. -/
def flatStripBaseUniformSpaceBound (inputLength : Nat) : Nat :=
  let unit := flatStripLeafSpaceUnit inputLength
  let context := flatStripContextUniformSpaceBound inputLength
  let equality := 10000000000 * unit + context
  let transition :=
    flatStripPackedTransitionUniformSpaceBound inputLength + 100 * context
  1000 *
    (equality + transition + flatStripReachStateSpaceBound inputLength +
      12 + 1)

theorem flatStripBaseSpaceBound_le_uniform
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (state : FiniteState.DivideEvalState)
    (indices : state.IndicesBelow (flatStripStateBound periodicStrip))
    (stateSpace :
      encodedListSpace
          (FiniteState.divideEvalProgramList 0
            (flatStripStateBound periodicStrip) state ++
            PeriodicStripFlatEncoding.stripFields periodicStrip) ≤
        flatStripReachStateSpaceBound
          (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length) :
    flatStripBaseSpaceBound tromino 0 (flatStripStateBound periodicStrip)
        state periodicStrip ≤
      flatStripBaseUniformSpaceBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  change flatStripBaseSpaceBound tromino 0
      (flatStripStateBound periodicStrip) state periodicStrip ≤
    flatStripBaseUniformSpaceBound inputLength
  have contextBase : flatStripContextBaseSpaceBound 0
      (flatStripStateBound periodicStrip) state periodicStrip ≤
      flatStripContextUniformSpaceBound inputLength := by
    simpa only [inputLength] using
      flatStripContextBaseSpaceBound_le_uniform
        periodicStrip state indices stateSpace
  have contextBound : flatStripContextSpaceBound 0
      (flatStripStateBound periodicStrip) state periodicStrip ≤
      100 * flatStripContextUniformSpaceBound inputLength := by
    simp only [flatStripContextSpaceBound]
    exact Nat.mul_le_mul_left 100 contextBase
  have packed : flatPackedTransitionSpaceBound periodicStrip
      (PackedWindowState.ofIndex periodicStrip state.query.first)
      (PackedWindowState.ofIndex periodicStrip state.query.last) ≤
      flatStripPackedTransitionUniformSpaceBound inputLength := by
    simpa only [inputLength] using
      flatPackedTransitionSpaceBound_le_flat_uniform
        periodicStrip state indices stateSpace
  have equalityArgument : encodedListSpace
      [2 * (state.query.first + state.query.last) + 4] + 1 ≤
      flatStripLeafSpaceUnit inputLength := by
    simpa only [inputLength] using
      flatStripEqualityArgumentSpace_le_leaf periodicStrip state indices
  have equality : flatStripEqualitySpaceBound 0
      (flatStripStateBound periodicStrip) state periodicStrip ≤
      10000000000 * flatStripLeafSpaceUnit inputLength +
        flatStripContextUniformSpaceBound inputLength := by
    simp only [flatStripEqualitySpaceBound]
    exact Nat.add_le_add
      (Nat.mul_le_mul_left 10000000000 equalityArgument) contextBase
  have transition : flatStripTransitionSpaceBound tromino 0
      (flatStripStateBound periodicStrip) state periodicStrip ≤
      flatStripPackedTransitionUniformSpaceBound inputLength +
        100 * flatStripContextUniformSpaceBound inputLength := by
    simp only [flatStripTransitionSpaceBound]
    simpa only [PackedWindowState.ofIndex] using
      Nat.add_le_add packed contextBound
  have stateSpace' : encodedListSpace
      (FiniteState.divideEvalProgramList 0
        (flatStripStateBound periodicStrip) state ++
        PeriodicStripFlatEncoding.stripFields periodicStrip) ≤
      flatStripReachStateSpaceBound inputLength := by
    simpa [inputLength] using stateSpace
  have headSuccessor : encodedListSpace
      [(FiniteState.divideEvalProgramList 0
          (flatStripStateBound periodicStrip) state ++
          PeriodicStripFlatEncoding.stripFields periodicStrip).headI + 1] ≤
      2 := by
    have oneBits : (Computability.encodeNat 1).length = 1 := rfl
    simp [FiniteState.divideEvalProgramList, encodedListSpace_cons,
      encodedListSpace_nil, oneBits]
  have component : flatStripBaseComponentSpaceBound tromino 0
      (flatStripStateBound periodicStrip) state periodicStrip ≤
      (10000000000 * flatStripLeafSpaceUnit inputLength +
        flatStripContextUniformSpaceBound inputLength) +
        (flatStripPackedTransitionUniformSpaceBound inputLength +
          100 * flatStripContextUniformSpaceBound inputLength) +
        flatStripReachStateSpaceBound inputLength + 12 := by
    simp only [flatStripBaseComponentSpaceBound]
    omega
  change 1000 *
      (flatStripBaseComponentSpaceBound tromino 0
        (flatStripStateBound periodicStrip) state periodicStrip + 1) ≤
    1000 *
      ((10000000000 * flatStripLeafSpaceUnit inputLength +
          flatStripContextUniformSpaceBound inputLength) +
        (flatStripPackedTransitionUniformSpaceBound inputLength +
          100 * flatStripContextUniformSpaceBound inputLength) +
        flatStripReachStateSpaceBound inputLength + 12 + 1)
  exact Nat.mul_le_mul_left 1000 (Nat.add_le_add_right component 1)

/-- Input-polynomial exact-step allowance used by the invariant iterator. -/
def flatStripSavitchStepSpaceBound (inputLength : Nat) : Nat :=
  1000000000000000000000000000000 *
    (flatStripReachStateSpaceBound inputLength +
      flatStripBaseUniformSpaceBound inputLength + 1)

theorem flatStripSavitchStepCost_le
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (state : FiniteState.DivideEvalState)
    (indices : state.IndicesBelow (flatStripStateBound periodicStrip))
    (stateSpace :
      encodedListSpace
          (FiniteState.divideEvalProgramList 0
            (flatStripStateBound periodicStrip) state ++
            PeriodicStripFlatEncoding.stripFields periodicStrip) ≤
        flatStripReachStateSpaceBound
          (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length) :
    FiniteState.FlatStripSavitchStep.stepCost tromino periodicStrip 0
        (flatStripStateBound periodicStrip) state ≤
      flatStripSavitchStepSpaceBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  have baseExact := flatStripBaseCost_le_bound tromino 0
    (flatStripStateBound periodicStrip) state periodicStrip wellFormed
  have baseUniform := flatStripBaseSpaceBound_le_uniform tromino periodicStrip
    state indices stateSpace
  have baseCost : flatStripBaseCost tromino 0
      (flatStripStateBound periodicStrip) state periodicStrip ≤
      flatStripBaseUniformSpaceBound inputLength :=
    baseExact.trans (by simpa [inputLength] using baseUniform)
  have stateSpace' : encodedListSpace
      (FiniteState.FlatStripSavitchStep.flatProgramList
        (PeriodicStripFlatEncoding.stripFields periodicStrip) 0
        (flatStripStateBound periodicStrip) state) ≤
      flatStripReachStateSpaceBound inputLength := by
    simpa [FiniteState.FlatStripSavitchStep.flatProgramList, inputLength]
      using stateSpace
  simp only [FiniteState.FlatStripSavitchStep.stepCost,
    FiniteState.FlatStripSavitchStep.stepSpaceUnit,
    FiniteState.FlatStripSavitchStep.baseBoolCost,
    flatStripSavitchStepSpaceBound]
  gcongr

end RawWindowState
end PeriodicStrip
end LeanTrominoes
