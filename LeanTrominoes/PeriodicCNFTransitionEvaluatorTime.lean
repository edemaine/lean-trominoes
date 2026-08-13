import LeanTrominoes.PeriodicCNFTransitionEvaluatorMachine
import LeanTrominoes.PartrecBinaryLengthSpace

/-!
# Polynomial time bound for the native transition compiler

This file turns the exact machine costs into one quadratic bound on generated
bounded-expression requests.  The request type retains the compiler invariant
that every source atom is below the initial fresh boundary; this is exactly the
invariant supplied by the bounded-machine front end.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF
namespace TransitionEvaluatorMachine

open Computability StateTransition Turing
open Turing.PartrecToTM2

theorem trNat_length_mono {smaller larger : Nat}
    (bounded : smaller ≤ larger) :
    (trNat smaller).length ≤ (trNat larger).length := by
  rw [Complexity.partrec_trNat_length,
    Complexity.partrec_trNat_length]
  exact encodeNat_length_mono bounded

theorem constantGate_native_length_le (output bound : Nat) (value : Bool)
    (outputBits : (trNat output).length ≤ bound) :
    (trList (constantGateFields output value)).length ≤
      50 * (bound + 1) := by
  rw [constantGateFields_native]
  cases value <;> simp [trList] at * <;> omega

theorem unaryGate_native_length_le (kind : UnaryGateKind)
    (output input bound : Nat)
    (outputBits : (trNat output).length ≤ bound)
    (inputBits : (trNat input).length ≤ bound) :
    (trList (unaryGateFields kind output input)).length ≤
      50 * (bound + 1) := by
  rw [unaryGateFields_native]
  cases kind <;>
    simp [trList, UnaryGateKind.sliceCode,
      UnaryGateKind.firstInputDesired,
      UnaryGateKind.secondInputDesired] at * <;>
    omega

theorem binaryGate_native_length_le (kind : BinaryGateKind)
    (output first second bound : Nat)
    (outputBits : (trNat output).length ≤ bound)
    (firstBits : (trNat first).length ≤ bound)
    (secondBits : (trNat second).length ≤ bound) :
    (trList (binaryGateFields kind output first second)).length ≤
      50 * (bound + 1) := by
  rw [binaryGateFields_native]
  cases kind <;>
    simp [trList, BinaryGateKind.shortOutputDesired,
      BinaryGateKind.shortInputDesired, BinaryGateKind.longOutputDesired,
      BinaryGateKind.longInputDesired] at * <;>
    omega

/-- Every gate field emitted by the structural compiler fits a common
linear-width allowance, summed once per expression node. -/
theorem compiledFields_native_length_le (expression : TransitionExpr)
    (fresh : Nat) (sourceBound : expression.AtomsBelow fresh) :
    (trList (compileTransitionFields expression fresh).fields).length ≤
      50 * expression.gateCount *
        ((trNat (compileTransitionFields expression fresh).nextFresh).length +
          1) := by
  induction expression generalizing fresh with
  | constant value =>
      have freshBits := trNat_length_mono
        (show fresh ≤ fresh + 1 by omega)
      simpa [compileTransitionFields, TransitionExpr.gateCount] using
        constantGate_native_length_le fresh
          (trNat (fresh + 1)).length value freshBits
  | wire input =>
      have freshBits := trNat_length_mono
        (show fresh ≤ fresh + 1 by omega)
      have inputBits : (trNat input.atom).length ≤
          (trNat (fresh + 1)).length :=
        trNat_length_mono (by
          change input.atom < fresh at sourceBound
          omega)
      have gate := unaryGate_native_length_le (wireUnaryKind input.slice)
          fresh input.atom (trNat (fresh + 1)).length
          freshBits inputBits
      rw [unaryGateFields_wireUnaryKind] at gate
      simpa [compileTransitionFields, TransitionExpr.gateCount] using gate
  | not input induction =>
      let compiled := compileTransitionFields input fresh
      let finalBits := (trNat (compiled.nextFresh + 1)).length
      have previousBits : (trNat compiled.nextFresh).length ≤ finalBits :=
        trNat_length_mono (by omega)
      have rootBits : (trNat compiled.root).length ≤ finalBits := by
        apply trNat_length_mono
        have rootLt := compileTransitionExpr_root_lt_nextFresh input fresh
        simpa [compiled] using Nat.le_trans (Nat.le_of_lt rootLt)
          (Nat.le_succ _)
      have previous := induction fresh sourceBound
      have previous' :
          (trList compiled.fields).length ≤
            50 * input.gateCount * (finalBits + 1) := by
        apply previous.trans
        exact Nat.mul_le_mul_left (50 * input.gateCount)
          (Nat.add_le_add_right previousBits 1)
      have gate := unaryGate_native_length_le .negation
        compiled.nextFresh compiled.root finalBits previousBits rootBits
      rw [show compileTransitionFields (.not input) fresh =
          ⟨compiled.nextFresh + 1, compiled.nextFresh,
            compiled.fields ++
              notGateFields compiled.nextFresh (gateOutput compiled.root)⟩ by
        rfl]
      simp only [trList_append, List.length_append,
        TransitionExpr.gateCount]
      change _ ≤ 50 * (input.gateCount + 1) * (finalBits + 1)
      have gate' :
          (trList (notGateFields compiled.nextFresh
            (gateOutput compiled.root))).length ≤
              50 * (finalBits + 1) := by
        simpa [unaryGateFields] using gate
      calc
        (trList compiled.fields).length +
            (trList (notGateFields compiled.nextFresh
              (gateOutput compiled.root))).length ≤
            50 * input.gateCount * (finalBits + 1) +
              50 * (finalBits + 1) := Nat.add_le_add previous' gate'
        _ = 50 * (input.gateCount + 1) * (finalBits + 1) := by ring
  | and first second firstIH secondIH =>
      let firstCompiled := compileTransitionFields first fresh
      let secondCompiled :=
        compileTransitionFields second firstCompiled.nextFresh
      let finalBits := (trNat (secondCompiled.nextFresh + 1)).length
      have freshLeFirst : fresh ≤ firstCompiled.nextFresh := by
        simp [firstCompiled, compileTransitionExpr_nextFresh]
      have secondSource := sourceBound.2.mono freshLeFirst
      have firstRun := firstIH fresh sourceBound.1
      have secondRun := secondIH firstCompiled.nextFresh secondSource
      have firstNextLe : firstCompiled.nextFresh ≤
          secondCompiled.nextFresh + 1 := by
        simp [firstCompiled, secondCompiled,
          compileTransitionExpr_nextFresh]
        omega
      have secondNextLe : secondCompiled.nextFresh ≤
          secondCompiled.nextFresh + 1 := by omega
      have firstBits := trNat_length_mono firstNextLe
      have secondBits := trNat_length_mono secondNextLe
      have firstRun' : (trList firstCompiled.fields).length ≤
          50 * first.gateCount * (finalBits + 1) := by
        apply firstRun.trans
        exact Nat.mul_le_mul_left (50 * first.gateCount)
          (Nat.add_le_add_right firstBits 1)
      have secondRun' : (trList secondCompiled.fields).length ≤
          50 * second.gateCount * (finalBits + 1) := by
        apply secondRun.trans
        exact Nat.mul_le_mul_left (50 * second.gateCount)
          (Nat.add_le_add_right secondBits 1)
      have firstRootBits : (trNat firstCompiled.root).length ≤ finalBits :=
        trNat_length_mono (by
          have rootLt := compileTransitionExpr_root_lt_nextFresh first fresh
          have rootLe : firstCompiled.root ≤ firstCompiled.nextFresh := by
            simpa [firstCompiled] using Nat.le_of_lt rootLt
          exact rootLe.trans firstNextLe)
      have secondRootBits : (trNat secondCompiled.root).length ≤ finalBits :=
        trNat_length_mono (by
          have rootLt := compileTransitionExpr_root_lt_nextFresh second
            firstCompiled.nextFresh
          have rootLe : secondCompiled.root ≤ secondCompiled.nextFresh := by
            simpa [secondCompiled] using Nat.le_of_lt rootLt
          exact rootLe.trans (Nat.le_succ _))
      have gate := binaryGate_native_length_le .conjunction
        secondCompiled.nextFresh firstCompiled.root secondCompiled.root
        finalBits secondBits firstRootBits secondRootBits
      rw [show compileTransitionFields (.and first second) fresh =
          ⟨secondCompiled.nextFresh + 1, secondCompiled.nextFresh,
            firstCompiled.fields ++ secondCompiled.fields ++
              andGateFields secondCompiled.nextFresh
                (gateOutput firstCompiled.root)
                (gateOutput secondCompiled.root)⟩ by rfl]
      simp only [trList_append, List.length_append,
        TransitionExpr.gateCount]
      have gate' :
          (trList (andGateFields secondCompiled.nextFresh
            (gateOutput firstCompiled.root)
            (gateOutput secondCompiled.root))).length ≤
              50 * (finalBits + 1) := by
        simpa [binaryGateFields] using gate
      calc
        _ ≤ 50 * first.gateCount * (finalBits + 1) +
              50 * second.gateCount * (finalBits + 1) +
              50 * (finalBits + 1) :=
          Nat.add_le_add (Nat.add_le_add firstRun' secondRun') gate'
        _ = 50 * (first.gateCount + second.gateCount + 1) *
              (finalBits + 1) := by ring
  | or first second firstIH secondIH =>
      let firstCompiled := compileTransitionFields first fresh
      let secondCompiled :=
        compileTransitionFields second firstCompiled.nextFresh
      let finalBits := (trNat (secondCompiled.nextFresh + 1)).length
      have freshLeFirst : fresh ≤ firstCompiled.nextFresh := by
        simp [firstCompiled, compileTransitionExpr_nextFresh]
      have secondSource := sourceBound.2.mono freshLeFirst
      have firstRun := firstIH fresh sourceBound.1
      have secondRun := secondIH firstCompiled.nextFresh secondSource
      have firstNextLe : firstCompiled.nextFresh ≤
          secondCompiled.nextFresh + 1 := by
        simp [firstCompiled, secondCompiled,
          compileTransitionExpr_nextFresh]
        omega
      have secondNextLe : secondCompiled.nextFresh ≤
          secondCompiled.nextFresh + 1 := by omega
      have firstBits := trNat_length_mono firstNextLe
      have secondBits := trNat_length_mono secondNextLe
      have firstRun' : (trList firstCompiled.fields).length ≤
          50 * first.gateCount * (finalBits + 1) := by
        apply firstRun.trans
        exact Nat.mul_le_mul_left (50 * first.gateCount)
          (Nat.add_le_add_right firstBits 1)
      have secondRun' : (trList secondCompiled.fields).length ≤
          50 * second.gateCount * (finalBits + 1) := by
        apply secondRun.trans
        exact Nat.mul_le_mul_left (50 * second.gateCount)
          (Nat.add_le_add_right secondBits 1)
      have firstRootBits : (trNat firstCompiled.root).length ≤ finalBits :=
        trNat_length_mono (by
          have rootLt := compileTransitionExpr_root_lt_nextFresh first fresh
          have rootLe : firstCompiled.root ≤ firstCompiled.nextFresh := by
            simpa [firstCompiled] using Nat.le_of_lt rootLt
          exact rootLe.trans firstNextLe)
      have secondRootBits : (trNat secondCompiled.root).length ≤ finalBits :=
        trNat_length_mono (by
          have rootLt := compileTransitionExpr_root_lt_nextFresh second
            firstCompiled.nextFresh
          have rootLe : secondCompiled.root ≤ secondCompiled.nextFresh := by
            simpa [secondCompiled] using Nat.le_of_lt rootLt
          exact rootLe.trans (Nat.le_succ _))
      have gate := binaryGate_native_length_le .disjunction
        secondCompiled.nextFresh firstCompiled.root secondCompiled.root
        finalBits secondBits firstRootBits secondRootBits
      rw [show compileTransitionFields (.or first second) fresh =
          ⟨secondCompiled.nextFresh + 1, secondCompiled.nextFresh,
            firstCompiled.fields ++ secondCompiled.fields ++
              orGateFields secondCompiled.nextFresh
                (gateOutput firstCompiled.root)
                (gateOutput secondCompiled.root)⟩ by rfl]
      simp only [trList_append, List.length_append,
        TransitionExpr.gateCount]
      have gate' :
          (trList (orGateFields secondCompiled.nextFresh
            (gateOutput firstCompiled.root)
            (gateOutput secondCompiled.root))).length ≤
              50 * (finalBits + 1) := by
        simpa [binaryGateFields] using gate
      calc
        _ ≤ 50 * first.gateCount * (finalBits + 1) +
              50 * second.gateCount * (finalBits + 1) +
              50 * (finalBits + 1) :=
          Nat.add_le_add (Nat.add_le_add firstRun' secondRun') gate'
        _ = 50 * (first.gateCount + second.gateCount + 1) *
              (finalBits + 1) := by ring

/-- The exact postorder-program runtime has the same per-gate linear-width
allowance as its emitted native field stream. -/
theorem transitionExpressionTime_le (expression : TransitionExpr)
    (fresh : Nat) (sourceBound : expression.AtomsBelow fresh) :
    transitionExpressionTime expression fresh ≤
      50 * expression.gateCount *
        ((trNat (compileTransitionFields expression fresh).nextFresh).length +
          1) := by
  induction expression generalizing fresh with
  | constant value =>
      have freshBits := trNat_length_mono
        (show fresh ≤ fresh + 1 by omega)
      cases value <;>
        simp [transitionExpressionTime, constantTagTime,
          compileTransitionFields, TransitionExpr.gateCount] at * <;>
        omega
  | wire input =>
      have freshBits := trNat_length_mono
        (show fresh ≤ fresh + 1 by omega)
      have inputBits : (trNat input.atom).length ≤
          (trNat (fresh + 1)).length :=
        trNat_length_mono (by
          change input.atom < fresh at sourceBound
          omega)
      rcases input with ⟨slice, atom⟩
      cases slice <;>
        simp [transitionExpressionTime, wireTagTime,
          compileTransitionFields, TransitionExpr.gateCount] at * <;>
        omega
  | not input induction =>
      let compiled := compileTransitionFields input fresh
      let finalBits := (trNat (compiled.nextFresh + 1)).length
      have previousBits : (trNat compiled.nextFresh).length ≤ finalBits :=
        trNat_length_mono (by omega)
      have rootBits : (trNat compiled.root).length ≤ finalBits := by
        apply trNat_length_mono
        have rootLt := compileTransitionExpr_root_lt_nextFresh input fresh
        have rootLe : compiled.root ≤ compiled.nextFresh := by
          simpa [compiled] using Nat.le_of_lt rootLt
        exact rootLe.trans (Nat.le_succ _)
      have previous := induction fresh sourceBound
      have previous' : transitionExpressionTime input fresh ≤
          50 * input.gateCount * (finalBits + 1) := by
        apply previous.trans
        exact Nat.mul_le_mul_left (50 * input.gateCount)
          (Nat.add_le_add_right previousBits 1)
      have gateCost :
          8 * (trNat compiled.nextFresh).length +
              7 * (trNat compiled.root).length + 31 ≤
            50 * (finalBits + 1) := by omega
      change transitionExpressionTime input fresh +
          (8 * (trNat compiled.nextFresh).length +
            7 * (trNat compiled.root).length + 31) ≤
        50 * (input.gateCount + 1) * (finalBits + 1)
      calc
        _ ≤ 50 * input.gateCount * (finalBits + 1) +
              50 * (finalBits + 1) := Nat.add_le_add previous' gateCost
        _ = 50 * (input.gateCount + 1) * (finalBits + 1) := by ring
  | and first second firstIH secondIH =>
      let firstCompiled := compileTransitionFields first fresh
      let secondCompiled :=
        compileTransitionFields second firstCompiled.nextFresh
      let finalBits := (trNat (secondCompiled.nextFresh + 1)).length
      have freshLeFirst : fresh ≤ firstCompiled.nextFresh := by
        simp [firstCompiled, compileTransitionExpr_nextFresh]
      have secondSource := sourceBound.2.mono freshLeFirst
      have firstRun := firstIH fresh sourceBound.1
      have secondRun := secondIH firstCompiled.nextFresh secondSource
      have firstNextLe : firstCompiled.nextFresh ≤
          secondCompiled.nextFresh + 1 := by
        simp [firstCompiled, secondCompiled,
          compileTransitionExpr_nextFresh]
        omega
      have secondNextLe : secondCompiled.nextFresh ≤
          secondCompiled.nextFresh + 1 := Nat.le_succ _
      have firstBits := trNat_length_mono firstNextLe
      have secondBits := trNat_length_mono secondNextLe
      have firstRun' : transitionExpressionTime first fresh ≤
          50 * first.gateCount * (finalBits + 1) := by
        apply firstRun.trans
        exact Nat.mul_le_mul_left (50 * first.gateCount)
          (Nat.add_le_add_right firstBits 1)
      have secondRun' :
          transitionExpressionTime second firstCompiled.nextFresh ≤
            50 * second.gateCount * (finalBits + 1) := by
        apply secondRun.trans
        exact Nat.mul_le_mul_left (50 * second.gateCount)
          (Nat.add_le_add_right secondBits 1)
      have firstRootBits : (trNat firstCompiled.root).length ≤ finalBits :=
        trNat_length_mono (by
          have rootLt := compileTransitionExpr_root_lt_nextFresh first fresh
          have rootLe : firstCompiled.root ≤ firstCompiled.nextFresh := by
            simpa [firstCompiled] using Nat.le_of_lt rootLt
          exact rootLe.trans firstNextLe)
      have secondRootBits : (trNat secondCompiled.root).length ≤ finalBits :=
        trNat_length_mono (by
          have rootLt := compileTransitionExpr_root_lt_nextFresh second
            firstCompiled.nextFresh
          have rootLe : secondCompiled.root ≤ secondCompiled.nextFresh := by
            simpa [secondCompiled] using Nat.le_of_lt rootLt
          exact rootLe.trans secondNextLe)
      have gateCost :
          binaryTagTime .conjunction +
                10 * (trNat secondCompiled.nextFresh).length +
              7 * (trNat firstCompiled.root).length +
            7 * (trNat secondCompiled.root).length + 40 ≤
          50 * (finalBits + 1) := by
        change 3 + 10 * (trNat secondCompiled.nextFresh).length +
              7 * (trNat firstCompiled.root).length +
            7 * (trNat secondCompiled.root).length + 40 ≤
          50 * (finalBits + 1)
        omega
      change transitionExpressionTime first fresh +
            transitionExpressionTime second firstCompiled.nextFresh +
            _ ≤
        50 * (first.gateCount + second.gateCount + 1) *
          (finalBits + 1)
      calc
        _ ≤ 50 * first.gateCount * (finalBits + 1) +
              50 * second.gateCount * (finalBits + 1) +
              50 * (finalBits + 1) :=
          Nat.add_le_add (Nat.add_le_add firstRun' secondRun') gateCost
        _ = 50 * (first.gateCount + second.gateCount + 1) *
              (finalBits + 1) := by ring
  | or first second firstIH secondIH =>
      let firstCompiled := compileTransitionFields first fresh
      let secondCompiled :=
        compileTransitionFields second firstCompiled.nextFresh
      let finalBits := (trNat (secondCompiled.nextFresh + 1)).length
      have freshLeFirst : fresh ≤ firstCompiled.nextFresh := by
        simp [firstCompiled, compileTransitionExpr_nextFresh]
      have secondSource := sourceBound.2.mono freshLeFirst
      have firstRun := firstIH fresh sourceBound.1
      have secondRun := secondIH firstCompiled.nextFresh secondSource
      have firstNextLe : firstCompiled.nextFresh ≤
          secondCompiled.nextFresh + 1 := by
        simp [firstCompiled, secondCompiled,
          compileTransitionExpr_nextFresh]
        omega
      have secondNextLe : secondCompiled.nextFresh ≤
          secondCompiled.nextFresh + 1 := Nat.le_succ _
      have firstBits := trNat_length_mono firstNextLe
      have secondBits := trNat_length_mono secondNextLe
      have firstRun' : transitionExpressionTime first fresh ≤
          50 * first.gateCount * (finalBits + 1) := by
        apply firstRun.trans
        exact Nat.mul_le_mul_left (50 * first.gateCount)
          (Nat.add_le_add_right firstBits 1)
      have secondRun' :
          transitionExpressionTime second firstCompiled.nextFresh ≤
            50 * second.gateCount * (finalBits + 1) := by
        apply secondRun.trans
        exact Nat.mul_le_mul_left (50 * second.gateCount)
          (Nat.add_le_add_right secondBits 1)
      have firstRootBits : (trNat firstCompiled.root).length ≤ finalBits :=
        trNat_length_mono (by
          have rootLt := compileTransitionExpr_root_lt_nextFresh first fresh
          have rootLe : firstCompiled.root ≤ firstCompiled.nextFresh := by
            simpa [firstCompiled] using Nat.le_of_lt rootLt
          exact rootLe.trans firstNextLe)
      have secondRootBits : (trNat secondCompiled.root).length ≤ finalBits :=
        trNat_length_mono (by
          have rootLt := compileTransitionExpr_root_lt_nextFresh second
            firstCompiled.nextFresh
          have rootLe : secondCompiled.root ≤ secondCompiled.nextFresh := by
            simpa [secondCompiled] using Nat.le_of_lt rootLt
          exact rootLe.trans secondNextLe)
      have gateCost :
          binaryTagTime .disjunction +
                10 * (trNat secondCompiled.nextFresh).length +
              7 * (trNat firstCompiled.root).length +
            7 * (trNat secondCompiled.root).length + 40 ≤
          50 * (finalBits + 1) := by
        change 4 + 10 * (trNat secondCompiled.nextFresh).length +
              7 * (trNat firstCompiled.root).length +
            7 * (trNat secondCompiled.root).length + 40 ≤
          50 * (finalBits + 1)
        omega
      change transitionExpressionTime first fresh +
            transitionExpressionTime second firstCompiled.nextFresh +
            _ ≤
        50 * (first.gateCount + second.gateCount + 1) *
          (finalBits + 1)
      calc
        _ ≤ 50 * first.gateCount * (finalBits + 1) +
              50 * second.gateCount * (finalBits + 1) +
              50 * (finalBits + 1) :=
          Nat.add_le_add (Nat.add_le_add firstRun' secondRun') gateCost
        _ = 50 * (first.gateCount + second.gateCount + 1) *
              (finalBits + 1) := by ring

theorem list_length_le_trList_length (fields : List Nat) :
    fields.length ≤ (trList fields).length := by
  induction fields with
  | nil => rfl
  | cons field fields induction =>
      simp only [List.length_cons, trList, List.length_append]
      omega

theorem transitionInstruction_fields_nonempty
    (instruction : TransitionInstruction) :
    1 ≤ instruction.fields.length := by
  cases instruction with
  | constant value => simp [TransitionInstruction.fields]
  | wire wire =>
      rcases wire with ⟨slice, atom⟩
      cases slice <;> simp [TransitionInstruction.fields]
  | negate => simp [TransitionInstruction.fields]
  | conjoin => simp [TransitionInstruction.fields]
  | disjoin => simp [TransitionInstruction.fields]

theorem transitionProgram_length_le_fields
    (instructions : List TransitionInstruction) :
    instructions.length ≤ (transitionProgramFields instructions).length := by
  induction instructions with
  | nil => rfl
  | cons instruction instructions induction =>
      rw [show transitionProgramFields (instruction :: instructions) =
          instruction.fields ++ transitionProgramFields instructions by rfl]
      simp only [List.length_cons, List.length_append]
      have instructionPositive := transitionInstruction_fields_nonempty instruction
      omega

theorem gateCount_le_program_native_length (expression : TransitionExpr) :
    expression.gateCount ≤
      (trList (transitionProgramFields expression.program)).length := by
  rw [← TransitionExpr.program_length]
  exact (transitionProgram_length_le_fields expression.program).trans
    (list_length_le_trList_length _)

def transitionRequestSize (expression : TransitionExpr) (fresh : Nat) : Nat :=
  (trList (transitionCompilerInputFields expression fresh)).length

theorem freshBits_le_transitionRequestSize
    (expression : TransitionExpr) (fresh : Nat) :
    (trNat fresh).length ≤ transitionRequestSize expression fresh := by
  unfold transitionRequestSize transitionCompilerInputFields
  simp only [trList, List.length_append, List.length_cons]
  omega

theorem gateCount_le_transitionRequestSize
    (expression : TransitionExpr) (fresh : Nat) :
    expression.gateCount ≤ transitionRequestSize expression fresh := by
  have programBound := gateCount_le_program_native_length expression
  unfold transitionRequestSize transitionCompilerInputFields
  simp only [trList, List.length_append, List.length_cons]
  omega

theorem headerBits_le_transitionRequestSize
    (expression : TransitionExpr) (fresh : Nat) :
    (trNat (expression.clauseCount + 1)).length ≤
      transitionRequestSize expression fresh := by
  unfold transitionRequestSize transitionCompilerInputFields
  simp only [trList, List.length_append, List.length_cons]
  omega

theorem finalFreshBits_le_transitionRequestSize
    (expression : TransitionExpr) (fresh : Nat) :
    (trNat (compileTransitionFields expression fresh).nextFresh).length ≤
      2 * transitionRequestSize expression fresh + 1 := by
  let size := transitionRequestSize expression fresh
  have freshBits := freshBits_le_transitionRequestSize expression fresh
  have gates := gateCount_le_transitionRequestSize expression fresh
  have addBits := encodeNat_add_length_le_sum fresh expression.gateCount
  have gateBits := encodeNat_length_le_self expression.gateCount
  have freshBits' : (Computability.encodeNat fresh).length ≤ size := by
    simpa [size, Complexity.partrec_trNat_length] using freshBits
  have gates' : expression.gateCount ≤ size := by
    simpa [size] using gates
  rw [compileTransitionFields_nextFresh,
    compileTransitionExpr_nextFresh,
    Complexity.partrec_trNat_length]
  omega

set_option maxHeartbeats 800000 in
/-- Exact machine execution is bounded quadratically in the native generated
request length. -/
theorem transitionMachineTime_le_quadratic (expression : TransitionExpr)
    (fresh : Nat) (sourceBound : expression.AtomsBelow fresh) :
    transitionMachineTime expression fresh ≤
      400 * (transitionRequestSize expression fresh + 1) ^ 2 := by
  let compiled := compileTransitionFields expression fresh
  let size := transitionRequestSize expression fresh
  let finalBits := (trNat compiled.nextFresh).length
  have gates : expression.gateCount ≤ size := by
    simpa [size] using gateCount_le_transitionRequestSize expression fresh
  have freshBits : (trNat fresh).length ≤ size := by
    simpa [size] using freshBits_le_transitionRequestSize expression fresh
  have headerBits : (trNat (expression.clauseCount + 1)).length ≤ size := by
    simpa [size] using headerBits_le_transitionRequestSize expression fresh
  have finalBitsBound : finalBits ≤ 2 * size + 1 := by
    simpa [finalBits, compiled, size] using
      finalFreshBits_le_transitionRequestSize expression fresh
  have rootBits : (trNat compiled.root).length ≤ finalBits := by
    apply trNat_length_mono
    have rootLt := compileTransitionExpr_root_lt_nextFresh expression fresh
    simpa [compiled] using Nat.le_of_lt rootLt
  have expressionTime := transitionExpressionTime_le expression fresh sourceBound
  have outputLength := compiledFields_native_length_le expression fresh sourceBound
  have scaleBound :
      50 * expression.gateCount * (finalBits + 1) ≤
        100 * size * (size + 1) := by
    calc
      50 * expression.gateCount * (finalBits + 1) ≤
          50 * size * (2 * (size + 1)) := by
        apply Nat.mul_le_mul
        · exact Nat.mul_le_mul_left 50 gates
        · omega
      _ = 100 * size * (size + 1) := by ring
  have expressionTime' : transitionExpressionTime expression fresh ≤
      100 * size * (size + 1) := expressionTime.trans (by
        simpa [compiled, finalBits] using scaleBound)
  have outputLength' : (trList compiled.fields).length ≤
      100 * size * (size + 1) := outputLength.trans (by
        simpa [compiled, finalBits] using scaleBound)
  have rootClauseLength :
      (trList (constantGateFields compiled.root true)).length ≤
        100 * (size + 1) := by
    apply (constantGate_native_length_le compiled.root finalBits true rootBits).trans
    omega
  have headerFieldLength :
      (trList [expression.clauseCount + 1]).length =
        (trNat (expression.clauseCount + 1)).length + 1 := by
    simp [trList]
  change
    (trNat (expression.clauseCount + 1)).length + 1 + 1 +
        (2 * (trNat fresh).length + 2) +
        transitionExpressionTime expression fresh +
        (finalBits + 5 * (trNat compiled.root).length +
          (trList (constantGateFields compiled.root true)).length +
          ((trList compiled.fields).reverse ++
            (trList [expression.clauseCount + 1]).reverse).length + 13) + 1 ≤
      400 * (size + 1) ^ 2
  simp only [List.length_append, List.length_reverse]
  rw [headerFieldLength]
  nlinarith

def transitionTimePolynomial : Polynomial Nat :=
  Polynomial.C 400 * (Polynomial.X + Polynomial.C 1) ^ 2

@[simp]
theorem transitionTimePolynomial_eval (length : Nat) :
    transitionTimePolynomial.eval length = 400 * (length + 1) ^ 2 := by
  simp [transitionTimePolynomial, Polynomial.eval_mul,
    Polynomial.eval_add, Polynomial.eval_pow]

/-- Semantic domain of well-bounded compiler requests.  Its encoding is the
same compact native field stream consumed by the physical machine. -/
structure TransitionCompilerRequest where
  expression : TransitionExpr
  fresh : Nat
  sourceBound : expression.AtomsBelow fresh

def TransitionCompilerRequest.encode
    (request : TransitionCompilerRequest) : List Γ' :=
  trList (transitionCompilerInputFields request.expression request.fresh)

def TransitionCompilerRequest.compile
    (request : TransitionCompilerRequest) : List Nat :=
  requireTransitionExprFields request.expression request.fresh

/-- The native structural transition compiler is a quadratic-time finite
multi-stack machine on every bounded request. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime TransitionCompilerRequest.encode trList
      TransitionCompilerRequest.compile where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := transitionTimePolynomial
  outputsFun request := by
    have exact := transitionMachine_outputs request.expression request.fresh
    have exact' : TM2OutputsInTime machine
        (List.map (Equiv.refl Γ').invFun
          (TransitionCompilerRequest.encode request))
        (some (List.map (Equiv.refl Γ').invFun
          (trList (TransitionCompilerRequest.compile request))))
        (transitionMachineTime request.expression request.fresh) := by
      simpa only [FiniteBlockTransducer.map_refl_invFun,
        TransitionCompilerRequest.encode,
        TransitionCompilerRequest.compile] using exact
    refine
      { toEvalsTo := exact'.toEvalsTo
        steps_le_m := exact'.steps_le_m.trans ?_ }
    rw [transitionTimePolynomial_eval]
    simpa [TransitionCompilerRequest.encode, transitionRequestSize] using
      transitionMachineTime_le_quadratic request.expression request.fresh
        request.sourceBound

end TransitionEvaluatorMachine
end PeriodicCNF
end LeanTrominoes
