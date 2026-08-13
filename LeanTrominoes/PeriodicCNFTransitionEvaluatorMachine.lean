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
