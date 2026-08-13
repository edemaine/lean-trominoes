import LeanTrominoes.PartrecFlatSavitchStepSpace
import LeanTrominoes.PeriodicStripFlatEncodingSize

/-!
# Native-input bounds for flat Savitch reachability

The legacy strip driver chooses its recursion depth from a recursively paired
encoding.  This module instead fixes the same sufficient linear depth from the
target flat encoding, proves that its power-of-two ambient graph contains the
sparse frontier graph, and bounds every reachable serialized DFS state while
retaining the complete native strip suffix.
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

end RawWindowState
end PeriodicStrip
end LeanTrominoes
