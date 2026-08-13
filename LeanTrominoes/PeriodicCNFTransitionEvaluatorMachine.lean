import LeanTrominoes.PeriodicCNFTransitionProgramEncoding
import LeanTrominoes.FiniteBlockTransducer

/-!
# A finite evaluator for transition-compiler programs

The compact postorder request uses the evaluator-native `trList` format.  The
finite evaluator assembled in this file streams its result backwards onto an
accumulator and reverses that accumulator only once at the end.

This first layer verifies the variable-width primitive used by every gate:
copy one binary atom from a dedicated stack to the output accumulator as a
complete delimiter-terminated field, then restore the source stack exactly.
The routine takes two steps per bit plus two boundary steps.
-/

namespace LeanTrominoes
namespace PeriodicCNF
namespace TransitionEvaluatorMachine

open Computability StateTransition Turing
open Turing.PartrecToTM2

/-- Physical stacks of the transition-program evaluator. -/
inductive Stack
  | input
  | outputReverse
  | output
  | fresh
  | roots
  | first
  | second
  | scratch
  deriving DecidableEq, Fintype

/-- The three variable-width atom registers used by gate emission. -/
inductive AtomSource
  | fresh
  | first
  | second
  deriving DecidableEq, Fintype

namespace AtomSource

def stack : AtomSource → Stack
  | .fresh => .fresh
  | .first => .first
  | .second => .second

@[simp]
theorem stack_ne_outputReverse (source : AtomSource) :
    source.stack ≠ Stack.outputReverse := by
  cases source <;> decide

@[simp]
theorem stack_ne_scratch (source : AtomSource) :
    source.stack ≠ Stack.scratch := by
  cases source <;> decide

end AtomSource

/-- Continuations of variable-atom emission.  More gate phases are added by
the evaluator layer; `done` is enough to state and test the primitive in
isolation. -/
inductive Phase
  | done
  deriving DecidableEq, Fintype

/-- Control labels for copying and restoring a binary atom. -/
inductive Label
  | copyAtom (source : AtomSource) (next : Phase)
  | restoreAtom (source : AtomSource) (next : Phase)
  | incrementFresh (next : Phase)
  | phase (phase : Phase)
  deriving DecidableEq, Fintype

abbrev State := Option Γ'

abbrev Alphabet (_ : Stack) := Γ'

/-- One loop step of the verified atom-field emitter. -/
def program : Label → TM2.Stmt Alphabet Label State
  | .copyAtom source next =>
      .pop source.stack (fun _ symbol => symbol)
        (.branch Option.isNone
          (.push .outputReverse (fun _ => .cons)
            (.load (fun _ => none) (.goto fun _ => .restoreAtom source next)))
          (.push .scratch (fun state => state.getD default)
            (.push .outputReverse (fun state => state.getD default)
              (.load (fun _ => none)
                (.goto fun _ => .copyAtom source next)))))
  | .restoreAtom source next =>
      .pop .scratch (fun _ symbol => symbol)
        (.branch Option.isNone
          (.load (fun _ => none) (.goto fun _ => .phase next))
          (.push source.stack (fun state => state.getD default)
            (.load (fun _ => none)
              (.goto fun _ => .restoreAtom source next))))
  | .incrementFresh next =>
      .pop .fresh (fun _ symbol => symbol)
        (.branch Option.isNone
          (.push .scratch (fun _ => .bit1)
            (.load (fun _ => none)
              (.goto fun _ => .restoreAtom .fresh next)))
          (.branch (fun state =>
              match state with
              | some .bit0 => true
              | _ => false)
            (.push .scratch (fun _ => .bit1)
              (.load (fun _ => none)
                (.goto fun _ => .restoreAtom .fresh next)))
            (.push .scratch (fun _ => .bit0)
              (.load (fun _ => none)
                (.goto fun _ => .incrementFresh next)))))
  | .phase .done => .halt

/-- The finite machine containing the atom-emission primitive.  Subsequent
layers extend its phase language into the complete compiler evaluator. -/
abbrev machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .phase .done
  σ := State
  initialState := none
  m := program

/-- Explicit tape contents used in all evaluator invariants. -/
structure TapeData where
  input : List Γ'
  outputReverse : List Γ'
  output : List Γ'
  fresh : List Γ'
  roots : List Γ'
  first : List Γ'
  second : List Γ'
  scratch : List Γ'
  deriving DecidableEq

namespace TapeData

def atom : TapeData → AtomSource → List Γ'
  | data, .fresh => data.fresh
  | data, .first => data.first
  | data, .second => data.second

def setAtom (data : TapeData) : AtomSource → List Γ' → TapeData
  | .fresh, value => { data with fresh := value }
  | .first, value => { data with first := value }
  | .second, value => { data with second := value }

@[simp]
theorem atom_setAtom (data : TapeData) (source : AtomSource)
    (value : List Γ') :
    (data.setAtom source value).atom source = value := by
  cases source <;> rfl

@[simp]
theorem setAtom_atom (data : TapeData) (source : AtomSource) :
    data.setAtom source (data.atom source) = data := by
  cases data
  cases source <;> rfl

end TapeData

def tapes (data : TapeData) : ∀ stack, List (Alphabet stack)
  | .input => data.input
  | .outputReverse => data.outputReverse
  | .output => data.output
  | .fresh => data.fresh
  | .roots => data.roots
  | .first => data.first
  | .second => data.second
  | .scratch => data.scratch

def copyCfg (source : AtomSource) (next : Phase) (data : TapeData) :
    TM2.Cfg Alphabet Label State :=
  ⟨some (.copyAtom source next), none, tapes data⟩

def restoreCfg (source : AtomSource) (next : Phase) (data : TapeData) :
    TM2.Cfg Alphabet Label State :=
  ⟨some (.restoreAtom source next), none, tapes data⟩

def phaseCfg (next : Phase) (data : TapeData) :
    TM2.Cfg Alphabet Label State :=
  ⟨some (.phase next), none, tapes data⟩

def incrementCfg (next : Phase) (data : TapeData) :
    TM2.Cfg Alphabet Label State :=
  ⟨some (.incrementFresh next), none, tapes data⟩

@[simp]
theorem update_tapes_outputReverse (data : TapeData) (value : List Γ') :
    Function.update (tapes data) Stack.outputReverse value =
      tapes { data with outputReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_scratch (data : TapeData) (value : List Γ') :
    Function.update (tapes data) Stack.scratch value =
      tapes { data with scratch := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_atom (data : TapeData) (source : AtomSource)
    (value : List Γ') :
    Function.update (tapes data) source.stack value =
      tapes (data.setAtom source value) := by
  cases data
  cases source <;>
    funext stack <;> cases stack <;> simp [tapes, TapeData.setAtom,
      AtomSource.stack, Function.update]

/-- One counted transition, packaged for the routine proofs. -/
def oneStep {first last : TM2.Cfg Alphabet Label State}
    (step : TM2.step program first = some last) :
    EvalsToInTime (TM2.step program) first (some last) 1 :=
  FiniteBlockTransducer.oneStep step

/-- Little-endian binary successor on native words.  The evaluator only calls
this function on canonical `trNat` words. -/
def incrementNative : List Γ' → List Γ'
  | [] => [.bit1]
  | .bit0 :: rest => .bit1 :: rest
  | _ :: rest => .bit0 :: incrementNative rest

/-- The untouched high suffix and reversed changed low prefix produced by the
carry scan. -/
def incrementCarry : List Γ' → List Γ' × List Γ'
  | [] => ([], [.bit1])
  | .bit0 :: rest => (rest, [.bit1])
  | _ :: rest =>
      let result := incrementCarry rest
      (result.1, result.2 ++ [.bit0])

/-- Number of carry-scan transitions. -/
def incrementCarrySteps : List Γ' → Nat
  | [] => 1
  | .bit0 :: _ => 1
  | _ :: rest => incrementCarrySteps rest + 1

theorem incrementCarry_spec (word : List Γ') :
    (incrementCarry word).2.reverse ++ (incrementCarry word).1 =
      incrementNative word := by
  induction word with
  | nil => rfl
  | cons symbol word induction =>
      cases symbol <;>
        simp [incrementCarry, incrementNative, List.reverse_append,
          induction, List.append_assoc]

theorem incrementCarrySteps_le (word : List Γ') :
    incrementCarrySteps word ≤ word.length + 1 := by
  induction word with
  | nil => simp [incrementCarrySteps]
  | cons symbol word induction =>
      cases symbol <;> simp [incrementCarrySteps] <;> omega

theorem incrementCarry_reverse_length_le (word : List Γ') :
    (incrementCarry word).2.length ≤ word.length + 1 := by
  induction word with
  | nil => simp [incrementCarry]
  | cons symbol word induction =>
      cases symbol <;> simp [incrementCarry] <;> omega

theorem incrementNative_trPosNum (number : PosNum) :
    incrementNative (trPosNum number) = trPosNum number.succ := by
  induction number with
  | one => rfl
  | bit0 number induction => rfl
  | bit1 number induction =>
      simp [trPosNum, incrementNative, PosNum.succ, induction]

@[simp]
theorem incrementNative_trNat (number : Nat) :
    incrementNative (trNat number) = trNat number.succ := by
  simp only [trNat, Nat.cast_succ, Num.add_one]
  cases encoded : (number : Num) with
  | zero => rfl
  | pos positive =>
      simpa [Num.succ, Num.succ', trNum] using
        incrementNative_trPosNum positive

def copyBitData (data : TapeData) (source : AtomSource)
    (symbol : Γ') (tail : List Γ') : TapeData :=
  { data.setAtom source tail with
    outputReverse := symbol :: data.outputReverse
    scratch := symbol :: data.scratch }

def restoreBitData (data : TapeData) (source : AtomSource)
    (symbol : Γ') (tail : List Γ') : TapeData :=
  { data.setAtom source (symbol :: data.atom source) with
    scratch := tail }

@[simp]
theorem copyBitData_atom (data : TapeData) (source : AtomSource)
    (symbol : Γ') (tail : List Γ') :
    (copyBitData data source symbol tail).atom source = tail := by
  cases data
  cases source <;> rfl

@[simp]
theorem copyBitData_outputReverse (data : TapeData) (source : AtomSource)
    (symbol : Γ') (tail : List Γ') :
    (copyBitData data source symbol tail).outputReverse =
      symbol :: data.outputReverse := by
  cases data
  cases source <;> rfl

@[simp]
theorem copyBitData_scratch (data : TapeData) (source : AtomSource)
    (symbol : Γ') (tail : List Γ') :
    (copyBitData data source symbol tail).scratch =
      symbol :: data.scratch := by
  cases data
  cases source <;> rfl

@[simp]
theorem restoreBitData_atom (data : TapeData) (source : AtomSource)
    (symbol : Γ') (tail : List Γ') :
    (restoreBitData data source symbol tail).atom source =
      symbol :: data.atom source := by
  cases data
  cases source <;> rfl

@[simp]
theorem restoreBitData_scratch (data : TapeData) (source : AtomSource)
    (symbol : Γ') (tail : List Γ') :
    (restoreBitData data source symbol tail).scratch = tail := by
  cases data
  cases source <;> rfl

theorem step_copyAtom_cons (source : AtomSource) (next : Phase)
    (data : TapeData) (symbol : Γ') (tail : List Γ')
    (sourceValue : data.atom source = symbol :: tail) :
    TM2.step program (copyCfg source next data) =
      some (copyCfg source next (copyBitData data source symbol tail)) := by
  rcases data with
    ⟨input, outputReverse, output, fresh, roots, first, second, scratch⟩
  cases source <;>
    simp [TapeData.atom] at sourceValue <;>
    simp [TM2.step, program, copyCfg, copyBitData, tapes,
      TapeData.setAtom, AtomSource.stack, sourceValue, Function.update]
  all_goals
    funext stack
    cases stack <;> simp [tapes, Function.update]

theorem step_copyAtom_nil (source : AtomSource) (next : Phase)
    (data : TapeData) (sourceValue : data.atom source = []) :
    TM2.step program (copyCfg source next data) =
      some (restoreCfg source next
        { data with outputReverse := .cons :: data.outputReverse }) := by
  rcases data with
    ⟨input, outputReverse, output, fresh, roots, first, second, scratch⟩
  cases source <;>
    simp [TapeData.atom] at sourceValue <;>
    simp [TM2.step, program, copyCfg, restoreCfg, tapes,
      TapeData.setAtom, AtomSource.stack, sourceValue, Function.update]
  all_goals
    funext stack
    cases stack <;> simp [tapes, Function.update]

theorem step_restoreAtom_cons (source : AtomSource) (next : Phase)
    (data : TapeData) (symbol : Γ') (tail : List Γ')
    (scratchValue : data.scratch = symbol :: tail) :
    TM2.step program (restoreCfg source next data) =
      some (restoreCfg source next
        (restoreBitData data source symbol tail)) := by
  rcases data with
    ⟨input, outputReverse, output, fresh, roots, first, second, scratch⟩
  cases source <;>
    simp at scratchValue <;>
    simp [TM2.step, program, restoreCfg, restoreBitData, tapes,
      TapeData.atom, TapeData.setAtom, AtomSource.stack,
      scratchValue, Function.update]
  all_goals
    funext stack
    cases stack <;> simp [tapes, Function.update]

theorem step_restoreAtom_nil (source : AtomSource) (next : Phase)
    (data : TapeData) (scratchValue : data.scratch = []) :
    TM2.step program (restoreCfg source next data) =
      some (phaseCfg next data) := by
  rcases data with
    ⟨input, outputReverse, output, fresh, roots, first, second, scratch⟩
  cases source <;>
    simp at scratchValue <;>
    simp [TM2.step, program, restoreCfg, phaseCfg, tapes,
      AtomSource.stack, scratchValue, Function.update]

def incrementScanData (data : TapeData) (word : List Γ') : TapeData :=
  { data with
    fresh := (incrementCarry word).1
    scratch := (incrementCarry word).2 ++ data.scratch }

theorem step_incrementFresh_nil (next : Phase) (data : TapeData)
    (freshValue : data.fresh = []) :
    TM2.step program (incrementCfg next data) =
      some (restoreCfg .fresh next
        { data with
          fresh := []
          scratch := .bit1 :: data.scratch }) := by
  rcases data with
    ⟨input, outputReverse, output, fresh, roots, first, second, scratch⟩
  change fresh = [] at freshValue
  subst fresh
  simp [TM2.step, program, incrementCfg, restoreCfg, tapes,
    Function.update]
  congr 1
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_incrementFresh_bit0 (next : Phase) (data : TapeData)
    (tail : List Γ') (freshValue : data.fresh = .bit0 :: tail) :
    TM2.step program (incrementCfg next data) =
      some (restoreCfg .fresh next
        { data with
          fresh := tail
          scratch := .bit1 :: data.scratch }) := by
  rcases data with
    ⟨input, outputReverse, output, fresh, roots, first, second, scratch⟩
  change fresh = .bit0 :: tail at freshValue
  subst fresh
  simp [TM2.step, program, incrementCfg, restoreCfg, tapes,
    Function.update]
  congr 1
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_incrementFresh_carry (next : Phase) (data : TapeData)
    (symbol : Γ') (tail : List Γ') (notZero : symbol ≠ .bit0)
    (freshValue : data.fresh = symbol :: tail) :
    TM2.step program (incrementCfg next data) =
      some (incrementCfg next
        { data with
          fresh := tail
          scratch := .bit0 :: data.scratch }) := by
  rcases data with
    ⟨input, outputReverse, output, fresh, roots, first, second, scratch⟩
  change fresh = symbol :: tail at freshValue
  subst fresh
  cases symbol <;> simp_all [TM2.step, program, incrementCfg, tapes,
    Function.update]
  all_goals
    congr 1
    funext stack
    cases stack <;> simp [tapes, Function.update]

/-- The carry scan reaches the restoration loop with the exact high suffix
and reversed changed low prefix. -/
def incrementFresh_to_restore (next : Phase) (data : TapeData)
    (word : List Γ') (freshValue : data.fresh = word) :
    EvalsToInTime (TM2.step program)
      (incrementCfg next data)
      (some (restoreCfg .fresh next (incrementScanData data word)))
      (incrementCarrySteps word) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep (step_incrementFresh_nil next data freshValue)
      convert step using 1
      · simp [incrementScanData, incrementCarry, freshValue]
      · simp [incrementCarrySteps]
  | cons symbol word induction =>
      cases symbol with
      | bit0 =>
          have step := oneStep
            (step_incrementFresh_bit0 next data word freshValue)
          convert step using 1
          · simp [incrementScanData, incrementCarry, freshValue]
          · simp [incrementCarrySteps]
      | bit1 =>
          let nextData : TapeData :=
            { data with
              fresh := word
              scratch := .bit0 :: data.scratch }
          have first := oneStep
            (step_incrementFresh_carry next data .bit1 word (by decide)
              freshValue)
          have rest := induction nextData rfl
          have target :
              incrementScanData nextData word =
                incrementScanData data (.bit1 :: word) := by
            simp [nextData, incrementScanData, incrementCarry,
              List.append_assoc]
          rw [target] at rest
          have composed := EvalsToInTime.trans (TM2.step program)
            1 (incrementCarrySteps word)
            (incrementCfg next data) (incrementCfg next nextData)
            (some (restoreCfg .fresh next
              (incrementScanData data (.bit1 :: word)))) first rest
          convert composed using 1 <;> simp [incrementCarrySteps]
      | cons =>
          let nextData : TapeData :=
            { data with
              fresh := word
              scratch := .bit0 :: data.scratch }
          have first := oneStep
            (step_incrementFresh_carry next data .cons word (by decide)
              freshValue)
          have rest := induction nextData rfl
          have target :
              incrementScanData nextData word =
                incrementScanData data (.cons :: word) := by
            simp [nextData, incrementScanData, incrementCarry,
              List.append_assoc]
          rw [target] at rest
          have composed := EvalsToInTime.trans (TM2.step program)
            1 (incrementCarrySteps word)
            (incrementCfg next data) (incrementCfg next nextData)
            (some (restoreCfg .fresh next
              (incrementScanData data (.cons :: word)))) first rest
          convert composed using 1 <;> simp [incrementCarrySteps]
      | consₗ =>
          let nextData : TapeData :=
            { data with
              fresh := word
              scratch := .bit0 :: data.scratch }
          have first := oneStep
            (step_incrementFresh_carry next data .consₗ word (by decide)
              freshValue)
          have rest := induction nextData rfl
          have target :
              incrementScanData nextData word =
                incrementScanData data (.consₗ :: word) := by
            simp [nextData, incrementScanData, incrementCarry,
              List.append_assoc]
          rw [target] at rest
          have composed := EvalsToInTime.trans (TM2.step program)
            1 (incrementCarrySteps word)
            (incrementCfg next data) (incrementCfg next nextData)
            (some (restoreCfg .fresh next
              (incrementScanData data (.consₗ :: word)))) first rest
          convert composed using 1 <;> simp [incrementCarrySteps]

/-- Tape state after consuming an atom into the reverse-output and scratch
stacks. -/
def copiedAtomData (data : TapeData) (source : AtomSource)
    (word : List Γ') : TapeData :=
  { data.setAtom source [] with
    outputReverse := .cons :: word.reverse ++ data.outputReverse
    scratch := word.reverse ++ data.scratch }

/-- The copying half consumes one symbol per step and one final boundary
step, leaving the source word reversed on scratch. -/
def copyAtom_to_restore (source : AtomSource) (next : Phase)
    (data : TapeData) (word : List Γ')
    (sourceValue : data.atom source = word) :
    EvalsToInTime (TM2.step program)
      (copyCfg source next data)
      (some (restoreCfg source next (copiedAtomData data source word)))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep (step_copyAtom_nil source next data sourceValue)
      convert step using 1
      · rcases data with
          ⟨input, outputReverse, output, fresh, roots, first, second,
            scratch⟩
        cases source <;>
          simp [TapeData.atom] at sourceValue <;>
          simp [copiedAtomData, TapeData.setAtom, sourceValue]
      · simp
  | cons symbol word induction =>
      have sourceHead : data.atom source = symbol :: word := sourceValue
      let nextData := copyBitData data source symbol word
      have first := oneStep
        (step_copyAtom_cons source next data symbol word sourceHead)
      have rest := induction nextData (by simp [nextData])
      have target :
          copiedAtomData nextData source word =
            copiedAtomData data source (symbol :: word) := by
        rcases data with
          ⟨input, outputReverse, output, fresh, roots, first, second,
            scratch⟩
        cases source <;>
          simp [nextData, copyBitData, copiedAtomData, TapeData.setAtom,
            List.reverse_cons, List.append_assoc]
      rw [target] at rest
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1)
        (copyCfg source next data)
        (copyCfg source next nextData)
        (some (restoreCfg source next
          (copiedAtomData data source (symbol :: word)))) first rest
      convert composed using 1 <;> simp

/-- Tape state after restoring a reversed scratch word onto an atom stack. -/
def restoredAtomData (data : TapeData) (source : AtomSource)
    (word : List Γ') : TapeData :=
  { data.setAtom source (word.reverse ++ data.atom source) with
    scratch := [] }

/-- The restoration half consumes one scratch symbol per step and one final
boundary step. -/
def restoreAtom_to_phase (source : AtomSource) (next : Phase)
    (data : TapeData) (word : List Γ')
    (scratchValue : data.scratch = word) :
    EvalsToInTime (TM2.step program)
      (restoreCfg source next data)
      (some (phaseCfg next (restoredAtomData data source word)))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_restoreAtom_nil source next data scratchValue)
      convert step using 1
      · rcases data with
          ⟨input, outputReverse, output, fresh, roots, first, second,
            scratch⟩
        cases source <;>
          simp at scratchValue <;>
          simp [restoredAtomData, TapeData.atom, TapeData.setAtom,
            scratchValue]
      · simp
  | cons symbol word induction =>
      let nextData := restoreBitData data source symbol word
      have first := oneStep
        (step_restoreAtom_cons source next data symbol word scratchValue)
      have rest := induction nextData (by simp [nextData])
      have target :
          restoredAtomData nextData source word =
            restoredAtomData data source (symbol :: word) := by
        rcases data with
          ⟨input, outputReverse, output, fresh, roots, first, second,
            scratch⟩
        cases source <;>
          simp [nextData, restoreBitData, restoredAtomData,
            TapeData.atom, TapeData.setAtom, List.reverse_cons,
            List.append_assoc]
      rw [target] at rest
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1)
        (restoreCfg source next data)
        (restoreCfg source next nextData)
        (some (phaseCfg next
          (restoredAtomData data source (symbol :: word)))) first rest
      convert composed using 1 <;> simp

/-- Increment a canonical native fresh-atom counter in place.  The generous
uniform bound covers the carry scan, reversal of the changed prefix, and the
final empty-scratch transition. -/
def incrementFresh_trNat (next : Phase) (data : TapeData) (number : Nat)
    (freshValue : data.fresh = trNat number)
    (scratchValue : data.scratch = []) :
    EvalsToInTime (TM2.step program)
      (incrementCfg next data)
      (some (phaseCfg next
        { data with fresh := trNat number.succ }))
      (2 * (trNat number).length + 3) := by
  let word := trNat number
  have scanned := incrementFresh_to_restore next data word (by
    simpa [word] using freshValue)
  have restored := restoreAtom_to_phase .fresh next
    (incrementScanData data word) (incrementCarry word).2 (by
      simp [incrementScanData, scratchValue])
  have finalData :
      restoredAtomData (incrementScanData data word) .fresh
          (incrementCarry word).2 =
        { data with fresh := trNat number.succ } := by
    rcases data with
      ⟨input, outputReverse, output, fresh, roots, first, second, scratch⟩
    change fresh = trNat number at freshValue
    change scratch = [] at scratchValue
    subst fresh
    subst scratch
    simp [restoredAtomData, incrementScanData, TapeData.atom,
      TapeData.setAtom, incrementCarry_spec, word]
  rw [finalData] at restored
  have composed := EvalsToInTime.trans (TM2.step program)
    (incrementCarrySteps word) ((incrementCarry word).2.length + 1)
    (incrementCfg next data)
    (restoreCfg .fresh next (incrementScanData data word))
    (some (phaseCfg next { data with fresh := trNat number.succ }))
    scanned restored
  refine
    { toEvalsTo := composed.toEvalsTo
      steps_le_m := composed.steps_le_m.trans ?_ }
  have scanBound := incrementCarrySteps_le word
  have reverseBound := incrementCarry_reverse_length_le word
  dsimp only [word] at scanBound reverseBound ⊢
  omega

/-- Emit one delimiter-terminated atom field into the reverse accumulator and
restore the atom register exactly. -/
def emitAtomField (source : AtomSource) (next : Phase)
    (data : TapeData) (word : List Γ')
    (sourceValue : data.atom source = word)
    (scratchValue : data.scratch = []) :
    EvalsToInTime (TM2.step program)
      (copyCfg source next data)
      (some (phaseCfg next
        { data with
          outputReverse :=
            (word ++ [Γ'.cons]).reverse ++ data.outputReverse }))
      (2 * word.length + 2) := by
  have copied := copyAtom_to_restore source next data word sourceValue
  have restored := restoreAtom_to_phase source next
    (copiedAtomData data source word) word.reverse (by
      simp [copiedAtomData, scratchValue])
  have finalData :
      restoredAtomData (copiedAtomData data source word) source word.reverse =
        { data with
          outputReverse :=
            (word ++ [Γ'.cons]).reverse ++ data.outputReverse } := by
    rcases data with
      ⟨input, outputReverse, output, fresh, roots, first, second, scratch⟩
    cases source <;>
      simp [TapeData.atom] at sourceValue <;>
      simp at scratchValue <;>
      simp [restoredAtomData, copiedAtomData, TapeData.setAtom,
        TapeData.atom, sourceValue, scratchValue, List.reverse_append,
        List.append_assoc]
  rw [finalData] at restored
  have composed := EvalsToInTime.trans (TM2.step program)
    (word.length + 1) (word.reverse.length + 1)
    (copyCfg source next data)
    (restoreCfg source next (copiedAtomData data source word))
    (some (phaseCfg next
      { data with
        outputReverse :=
          (word ++ [Γ'.cons]).reverse ++ data.outputReverse }))
    copied restored
  convert composed using 1 <;> simp <;> omega

/-- Native-number specialization of `emitAtomField`: the accumulator gains
exactly the reverse of one `trList` field. -/
def emitAtomField_trNat (source : AtomSource) (next : Phase)
    (data : TapeData) (atom : Nat)
    (sourceValue : data.atom source = trNat atom)
    (scratchValue : data.scratch = []) :
    EvalsToInTime (TM2.step program)
      (copyCfg source next data)
      (some (phaseCfg next
        { data with
          outputReverse :=
            (trList [atom]).reverse ++ data.outputReverse }))
      (2 * (trNat atom).length + 2) := by
  simpa using emitAtomField source next data (trNat atom)
    sourceValue scratchValue

end TransitionEvaluatorMachine
end PeriodicCNF
end LeanTrominoes
