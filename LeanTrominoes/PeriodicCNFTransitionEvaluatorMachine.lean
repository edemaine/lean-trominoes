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

/-- Equality gates differ only by their source slice; negation uses the same
two-clause emission skeleton with different desired input bits. -/
inductive UnaryGateKind
  | equalityCurrent
  | equalityNext
  | negation
  deriving DecidableEq, Fintype

namespace UnaryGateKind

def sliceCode : UnaryGateKind → Nat
  | .equalityCurrent => 0
  | .equalityNext => 2
  | .negation => 0

def firstInputDesired : UnaryGateKind → Nat
  | .equalityCurrent | .equalityNext => 1
  | .negation => 0

def secondInputDesired : UnaryGateKind → Nat
  | .equalityCurrent | .equalityNext => 0
  | .negation => 1

end UnaryGateKind

/-- Conjunction and disjunction have the same three-clause shape with all
four desired truth values reversed. -/
inductive BinaryGateKind
  | conjunction
  | disjunction
  deriving DecidableEq, Fintype

namespace BinaryGateKind

def shortOutputDesired : BinaryGateKind → Nat
  | .conjunction => 0
  | .disjunction => 1

def shortInputDesired : BinaryGateKind → Nat
  | .conjunction => 1
  | .disjunction => 0

def longOutputDesired : BinaryGateKind → Nat
  | .conjunction => 1
  | .disjunction => 0

def longInputDesired : BinaryGateKind → Nat
  | .conjunction => 0
  | .disjunction => 1

end BinaryGateKind

/-- Continuations of variable-atom emission.  More gate phases are added by
the evaluator layer; `done` is enough to state and test the primitive in
isolation. -/
inductive Phase
  | done
  | gateDone
  | constantStart (value : Bool)
  | constantTail (value : Bool)
  | unaryStart (kind : UnaryGateKind)
  | unaryAfterOutput₁ (kind : UnaryGateKind)
  | unaryAfterInput₁ (kind : UnaryGateKind)
  | unaryAfterOutput₂ (kind : UnaryGateKind)
  | unaryAfterInput₂ (kind : UnaryGateKind)
  | binaryStart (kind : BinaryGateKind)
  | binaryAfterOutput₁ (kind : BinaryGateKind)
  | binaryAfterFirst₁ (kind : BinaryGateKind)
  | binaryAfterOutput₂ (kind : BinaryGateKind)
  | binaryAfterSecond₁ (kind : BinaryGateKind)
  | binaryAfterOutput₃ (kind : BinaryGateKind)
  | binaryAfterFirst₂ (kind : BinaryGateKind)
  | binaryAfterSecond₂ (kind : BinaryGateKind)
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

/-- Push a compile-time native word onto the reverse-output accumulator. -/
def pushOutputWord (word : List Γ')
    (next : TM2.Stmt Alphabet Label State) :
    TM2.Stmt Alphabet Label State :=
  word.foldr
    (fun symbol continuation =>
      .push .outputReverse (fun _ => symbol) continuation)
    next

/-- Emit compile-time natural fields in one finite-control transition. -/
def emitFixedFields (fields : List Nat) (next : Label) :
    TM2.Stmt Alphabet Label State :=
  pushOutputWord (trList fields)
    (.load (fun _ => none) (.goto fun _ => next))

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
  | .phase .gateDone => .halt
  | .phase (.constantStart value) =>
      emitFixedFields [1] (.copyAtom .fresh (.constantTail value))
  | .phase (.constantTail value) =>
      emitFixedFields [0, 0, if value then 1 else 0] (.phase .gateDone)
  | .phase (.unaryStart kind) =>
      emitFixedFields [2] (.copyAtom .fresh (.unaryAfterOutput₁ kind))
  | .phase (.unaryAfterOutput₁ kind) =>
      emitFixedFields [0, 0, 0] (.copyAtom .first (.unaryAfterInput₁ kind))
  | .phase (.unaryAfterInput₁ kind) =>
      emitFixedFields
        [kind.sliceCode, 0, kind.firstInputDesired, 2]
        (.copyAtom .fresh (.unaryAfterOutput₂ kind))
  | .phase (.unaryAfterOutput₂ kind) =>
      emitFixedFields [0, 0, 1]
        (.copyAtom .first (.unaryAfterInput₂ kind))
  | .phase (.unaryAfterInput₂ kind) =>
      emitFixedFields
        [kind.sliceCode, 0, kind.secondInputDesired]
        (.phase .gateDone)
  | .phase (.binaryStart kind) =>
      emitFixedFields [2]
        (.copyAtom .fresh (.binaryAfterOutput₁ kind))
  | .phase (.binaryAfterOutput₁ kind) =>
      emitFixedFields [0, 0, kind.shortOutputDesired]
        (.copyAtom .first (.binaryAfterFirst₁ kind))
  | .phase (.binaryAfterFirst₁ kind) =>
      emitFixedFields [0, 0, kind.shortInputDesired, 2]
        (.copyAtom .fresh (.binaryAfterOutput₂ kind))
  | .phase (.binaryAfterOutput₂ kind) =>
      emitFixedFields [0, 0, kind.shortOutputDesired]
        (.copyAtom .second (.binaryAfterSecond₁ kind))
  | .phase (.binaryAfterSecond₁ kind) =>
      emitFixedFields [0, 0, kind.shortInputDesired, 3]
        (.copyAtom .fresh (.binaryAfterOutput₃ kind))
  | .phase (.binaryAfterOutput₃ kind) =>
      emitFixedFields [0, 0, kind.longOutputDesired]
        (.copyAtom .first (.binaryAfterFirst₂ kind))
  | .phase (.binaryAfterFirst₂ kind) =>
      emitFixedFields [0, 0, kind.longInputDesired]
        (.copyAtom .second (.binaryAfterSecond₂ kind))
  | .phase (.binaryAfterSecond₂ kind) =>
      emitFixedFields [0, 0, kind.longInputDesired]
        (.phase .gateDone)

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

theorem stepAux_pushOutputWord (word : List Γ')
    (next : TM2.Stmt Alphabet Label State) (state : State)
    (tapeStacks : ∀ stack, List (Alphabet stack)) :
    TM2.stepAux (pushOutputWord word next) state tapeStacks =
      TM2.stepAux next state
        (Function.update tapeStacks .outputReverse
          (word.reverse ++ tapeStacks .outputReverse)) := by
  induction word generalizing tapeStacks with
  | nil => simp [pushOutputWord]
  | cons symbol word induction =>
      simp only [pushOutputWord, List.foldr_cons, TM2.stepAux]
      change TM2.stepAux (pushOutputWord word next) state
          (Function.update tapeStacks .outputReverse
            (symbol :: tapeStacks .outputReverse)) = _
      rw [induction]
      congr 1
      funext stack
      cases stack <;>
        simp [Function.update, List.reverse_cons, List.append_assoc]

/-- Add one native word to the semantic reverse-output invariant. -/
def emittedWordData (data : TapeData) (word : List Γ') : TapeData :=
  { data with outputReverse := word.reverse ++ data.outputReverse }

@[simp]
theorem emittedWordData_atom (data : TapeData) (word : List Γ')
    (source : AtomSource) :
    (emittedWordData data word).atom source = data.atom source := by
  cases data
  cases source <;> rfl

@[simp]
theorem emittedWordData_scratch (data : TapeData) (word : List Γ') :
    (emittedWordData data word).scratch = data.scratch := by
  rfl

@[simp]
theorem emittedWordData_fresh (data : TapeData) (word : List Γ') :
    (emittedWordData data word).fresh = data.fresh := by
  rfl

@[simp]
theorem emittedWordData_first (data : TapeData) (word : List Γ') :
    (emittedWordData data word).first = data.first := by
  rfl

@[simp]
theorem emittedWordData_second (data : TapeData) (word : List Γ') :
    (emittedWordData data word).second = data.second := by
  rfl

theorem step_constantStart (data : TapeData) (value : Bool) :
    TM2.step program (phaseCfg (.constantStart value) data) =
      some (copyCfg .fresh (.constantTail value)
        (emittedWordData data (trList [1]))) := by
  simp only [TM2.step, program, phaseCfg, emitFixedFields]
  rw [stepAux_pushOutputWord]
  simp [copyCfg, emittedWordData, tapes]

theorem step_constantTail (data : TapeData) (value : Bool) :
    TM2.step program (phaseCfg (.constantTail value) data) =
      some (phaseCfg .gateDone
        (emittedWordData data
          (trList [0, 0, if value then 1 else 0]))) := by
  simp only [TM2.step, program, phaseCfg, emitFixedFields]
  rw [stepAux_pushOutputWord]
  simp [phaseCfg, emittedWordData, tapes]

theorem step_unaryStart (data : TapeData) (kind : UnaryGateKind) :
    TM2.step program (phaseCfg (.unaryStart kind) data) =
      some (copyCfg .fresh (.unaryAfterOutput₁ kind)
        (emittedWordData data (trList [2]))) := by
  simp only [TM2.step, program, phaseCfg, emitFixedFields]
  rw [stepAux_pushOutputWord]
  simp [copyCfg, emittedWordData, tapes]

theorem step_unaryAfterOutput₁ (data : TapeData)
    (kind : UnaryGateKind) :
    TM2.step program (phaseCfg (.unaryAfterOutput₁ kind) data) =
      some (copyCfg .first (.unaryAfterInput₁ kind)
        (emittedWordData data (trList [0, 0, 0]))) := by
  simp only [TM2.step, program, phaseCfg, emitFixedFields]
  rw [stepAux_pushOutputWord]
  simp [copyCfg, emittedWordData, tapes]

theorem step_unaryAfterInput₁ (data : TapeData)
    (kind : UnaryGateKind) :
    TM2.step program (phaseCfg (.unaryAfterInput₁ kind) data) =
      some (copyCfg .fresh (.unaryAfterOutput₂ kind)
        (emittedWordData data
          (trList [kind.sliceCode, 0, kind.firstInputDesired, 2]))) := by
  simp only [TM2.step, program, phaseCfg, emitFixedFields]
  rw [stepAux_pushOutputWord]
  simp [copyCfg, emittedWordData, tapes]

theorem step_unaryAfterOutput₂ (data : TapeData)
    (kind : UnaryGateKind) :
    TM2.step program (phaseCfg (.unaryAfterOutput₂ kind) data) =
      some (copyCfg .first (.unaryAfterInput₂ kind)
        (emittedWordData data (trList [0, 0, 1]))) := by
  simp only [TM2.step, program, phaseCfg, emitFixedFields]
  rw [stepAux_pushOutputWord]
  simp [copyCfg, emittedWordData, tapes]

theorem step_unaryAfterInput₂ (data : TapeData)
    (kind : UnaryGateKind) :
    TM2.step program (phaseCfg (.unaryAfterInput₂ kind) data) =
      some (phaseCfg .gateDone
        (emittedWordData data
          (trList [kind.sliceCode, 0, kind.secondInputDesired]))) := by
  simp only [TM2.step, program, phaseCfg, emitFixedFields]
  rw [stepAux_pushOutputWord]
  simp [phaseCfg, emittedWordData, tapes]

theorem step_binaryStart (data : TapeData) (kind : BinaryGateKind) :
    TM2.step program (phaseCfg (.binaryStart kind) data) =
      some (copyCfg .fresh (.binaryAfterOutput₁ kind)
        (emittedWordData data (trList [2]))) := by
  simp only [TM2.step, program, phaseCfg, emitFixedFields]
  rw [stepAux_pushOutputWord]
  simp [copyCfg, emittedWordData, tapes]

theorem step_binaryAfterOutput₁ (data : TapeData)
    (kind : BinaryGateKind) :
    TM2.step program (phaseCfg (.binaryAfterOutput₁ kind) data) =
      some (copyCfg .first (.binaryAfterFirst₁ kind)
        (emittedWordData data
          (trList [0, 0, kind.shortOutputDesired]))) := by
  simp only [TM2.step, program, phaseCfg, emitFixedFields]
  rw [stepAux_pushOutputWord]
  simp [copyCfg, emittedWordData, tapes]

theorem step_binaryAfterFirst₁ (data : TapeData)
    (kind : BinaryGateKind) :
    TM2.step program (phaseCfg (.binaryAfterFirst₁ kind) data) =
      some (copyCfg .fresh (.binaryAfterOutput₂ kind)
        (emittedWordData data
          (trList [0, 0, kind.shortInputDesired, 2]))) := by
  simp only [TM2.step, program, phaseCfg, emitFixedFields]
  rw [stepAux_pushOutputWord]
  simp [copyCfg, emittedWordData, tapes]

theorem step_binaryAfterOutput₂ (data : TapeData)
    (kind : BinaryGateKind) :
    TM2.step program (phaseCfg (.binaryAfterOutput₂ kind) data) =
      some (copyCfg .second (.binaryAfterSecond₁ kind)
        (emittedWordData data
          (trList [0, 0, kind.shortOutputDesired]))) := by
  simp only [TM2.step, program, phaseCfg, emitFixedFields]
  rw [stepAux_pushOutputWord]
  simp [copyCfg, emittedWordData, tapes]

theorem step_binaryAfterSecond₁ (data : TapeData)
    (kind : BinaryGateKind) :
    TM2.step program (phaseCfg (.binaryAfterSecond₁ kind) data) =
      some (copyCfg .fresh (.binaryAfterOutput₃ kind)
        (emittedWordData data
          (trList [0, 0, kind.shortInputDesired, 3]))) := by
  simp only [TM2.step, program, phaseCfg, emitFixedFields]
  rw [stepAux_pushOutputWord]
  simp [copyCfg, emittedWordData, tapes]

theorem step_binaryAfterOutput₃ (data : TapeData)
    (kind : BinaryGateKind) :
    TM2.step program (phaseCfg (.binaryAfterOutput₃ kind) data) =
      some (copyCfg .first (.binaryAfterFirst₂ kind)
        (emittedWordData data
          (trList [0, 0, kind.longOutputDesired]))) := by
  simp only [TM2.step, program, phaseCfg, emitFixedFields]
  rw [stepAux_pushOutputWord]
  simp [copyCfg, emittedWordData, tapes]

theorem step_binaryAfterFirst₂ (data : TapeData)
    (kind : BinaryGateKind) :
    TM2.step program (phaseCfg (.binaryAfterFirst₂ kind) data) =
      some (copyCfg .second (.binaryAfterSecond₂ kind)
        (emittedWordData data
          (trList [0, 0, kind.longInputDesired]))) := by
  simp only [TM2.step, program, phaseCfg, emitFixedFields]
  rw [stepAux_pushOutputWord]
  simp [copyCfg, emittedWordData, tapes]

theorem step_binaryAfterSecond₂ (data : TapeData)
    (kind : BinaryGateKind) :
    TM2.step program (phaseCfg (.binaryAfterSecond₂ kind) data) =
      some (phaseCfg .gateDone
        (emittedWordData data
          (trList [0, 0, kind.longInputDesired]))) := by
  simp only [TM2.step, program, phaseCfg, emitFixedFields]
  rw [stepAux_pushOutputWord]
  simp [phaseCfg, emittedWordData, tapes]

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

/-- Compose one fixed-field phase transition with the variable-width atom
field that follows it. -/
def emitFixedThenAtom {start next : Phase} (source : AtomSource)
    (data : TapeData) (word : List Γ') (atom : Nat)
    (fixedStep :
      TM2.step program (phaseCfg start data) =
        some (copyCfg source next (emittedWordData data word)))
    (sourceValue : data.atom source = trNat atom)
    (scratchValue : data.scratch = []) :
    EvalsToInTime (TM2.step program)
      (phaseCfg start data)
      (some (phaseCfg next
        (emittedWordData (emittedWordData data word) (trList [atom]))))
      (2 * (trNat atom).length + 3) := by
  let fixedData := emittedWordData data word
  have first : EvalsToInTime (TM2.step program)
      (phaseCfg start data) (some (copyCfg source next fixedData)) 1 := by
    simpa [fixedData] using oneStep fixedStep
  have atomRun : EvalsToInTime (TM2.step program)
      (copyCfg source next fixedData)
      (some (phaseCfg next
        (emittedWordData fixedData (trList [atom]))))
      (2 * (trNat atom).length + 2) := by
    simpa [emittedWordData] using
      emitAtomField_trNat source next fixedData atom
        (by simpa [fixedData] using sourceValue)
        (by simpa [fixedData] using scratchValue)
  have composed := EvalsToInTime.trans (TM2.step program)
    1 (2 * (trNat atom).length + 2)
    (phaseCfg start data) (copyCfg source next fixedData)
    (some (phaseCfg next
      (emittedWordData fixedData (trList [atom])))) first atomRun
  simpa [fixedData] using composed

/-- Convenient composition for evaluator fragments whose intermediate result
is a live configuration. -/
def thenRun {first middle : TM2.Cfg Alphabet Label State}
    {last : Option (TM2.Cfg Alphabet Label State)} {firstTime secondTime : Nat}
    (firstRun : EvalsToInTime (TM2.step program)
      first (some middle) firstTime)
    (secondRun : EvalsToInTime (TM2.step program)
      middle last secondTime) :
    EvalsToInTime (TM2.step program)
      first last (secondTime + firstTime) :=
  EvalsToInTime.trans (TM2.step program)
    firstTime secondTime first middle last firstRun secondRun

@[simp]
theorem constantGateFields_native (output : Nat) (value : Bool) :
    constantGateFields output value =
      [1, output, 0, 0, if value then 1 else 0] := by
  cases value <;> rfl

/-- The common native-field interface for equality and negation gates. -/
def unaryGateFields (kind : UnaryGateKind) (output input : Nat) : List Nat :=
  match kind with
  | .equalityCurrent =>
      equalityGateFields output ⟨.current, input⟩
  | .equalityNext =>
      equalityGateFields output ⟨.next, input⟩
  | .negation =>
      notGateFields output (gateOutput input)

@[simp]
theorem unaryGateFields_native (kind : UnaryGateKind) (output input : Nat) :
    unaryGateFields kind output input =
      [2, output, 0, 0, 0, input, kind.sliceCode, 0,
        kind.firstInputDesired,
       2, output, 0, 0, 1, input, kind.sliceCode, 0,
        kind.secondInputDesired] := by
  cases kind <;>
    rfl

/-- The common native-field interface for conjunction and disjunction gates. -/
def binaryGateFields (kind : BinaryGateKind)
    (output first second : Nat) : List Nat :=
  match kind with
  | .conjunction =>
      andGateFields output (gateOutput first) (gateOutput second)
  | .disjunction =>
      orGateFields output (gateOutput first) (gateOutput second)

@[simp]
theorem binaryGateFields_native (kind : BinaryGateKind)
    (output first second : Nat) :
    binaryGateFields kind output first second =
      [2, output, 0, 0, kind.shortOutputDesired,
        first, 0, 0, kind.shortInputDesired,
       2, output, 0, 0, kind.shortOutputDesired,
        second, 0, 0, kind.shortInputDesired,
       3, output, 0, 0, kind.longOutputDesired,
        first, 0, 0, kind.longInputDesired,
        second, 0, 0, kind.longInputDesired] := by
  cases kind <;>
    rfl

/-- The complete finite-control script for a constant Tseitin gate emits its
verified native field block in linear time in the output-atom width. -/
def emitConstantGate (data : TapeData) (output : Nat) (value : Bool)
    (freshValue : data.fresh = trNat output)
    (scratchValue : data.scratch = []) :
    EvalsToInTime (TM2.step program)
      (phaseCfg (.constantStart value) data)
      (some (phaseCfg .gateDone
        { data with
          outputReverse :=
            (trList (constantGateFields output value)).reverse ++
              data.outputReverse }))
      (2 * (trNat output).length + 4) := by
  let firstData := emittedWordData data (trList [1])
  have first := oneStep (step_constantStart data value)
  have atom := emitAtomField_trNat .fresh (.constantTail value)
    firstData output (by
      simpa [firstData, emittedWordData, TapeData.atom] using freshValue)
    (by simpa [firstData, emittedWordData] using scratchValue)
  let secondData : TapeData :=
    { firstData with
      outputReverse :=
        (trList [output]).reverse ++ firstData.outputReverse }
  have atom' : EvalsToInTime (TM2.step program)
      (copyCfg .fresh (.constantTail value) firstData)
      (some (phaseCfg (.constantTail value) secondData))
      (2 * (trNat output).length + 2) := by
    simpa [secondData] using atom
  have tail := oneStep (step_constantTail secondData value)
  have firstTwo := EvalsToInTime.trans (TM2.step program)
    1 (2 * (trNat output).length + 2)
    (phaseCfg (.constantStart value) data)
    (copyCfg .fresh (.constantTail value) firstData)
    (some (phaseCfg (.constantTail value) secondData)) first atom'
  have composed := EvalsToInTime.trans (TM2.step program)
    (2 * (trNat output).length + 2 + 1) 1
    (phaseCfg (.constantStart value) data)
    (phaseCfg (.constantTail value) secondData)
    (some (phaseCfg .gateDone
      (emittedWordData secondData
        (trList [0, 0, if value then 1 else 0]))))
    firstTwo tail
  have finalData :
      emittedWordData secondData
          (trList [0, 0, if value then 1 else 0]) =
        { data with
          outputReverse :=
            (trList (constantGateFields output value)).reverse ++
              data.outputReverse } := by
    rw [constantGateFields_native]
    rcases data with
      ⟨input, outputReverse, finalOutput, fresh, roots, firstRoot,
        secondRoot, scratch⟩
    cases value <;>
      simp [firstData, secondData, emittedWordData, trList,
        List.reverse_append, List.append_assoc]
  rw [finalData] at composed
  convert composed using 1 <;> omega

/-- The shared finite-control script for equality and negation Tseitin gates
emits the exact native field block and restores both atom registers. -/
def emitUnaryGate (kind : UnaryGateKind) (data : TapeData)
    (output input : Nat)
    (freshValue : data.fresh = trNat output)
    (firstValue : data.first = trNat input)
    (scratchValue : data.scratch = []) :
    EvalsToInTime (TM2.step program)
      (phaseCfg (.unaryStart kind) data)
      (some (phaseCfg .gateDone
        { data with
          outputReverse :=
            (trList (unaryGateFields kind output input)).reverse ++
              data.outputReverse }))
      (4 * (trNat output).length + 4 * (trNat input).length + 13) := by
  let d₁ := emittedWordData data (trList [2])
  let d₂ := emittedWordData d₁ (trList [output])
  let d₃ := emittedWordData d₂ (trList [0, 0, 0])
  let d₄ := emittedWordData d₃ (trList [input])
  let d₅ := emittedWordData d₄
    (trList [kind.sliceCode, 0, kind.firstInputDesired, 2])
  let d₆ := emittedWordData d₅ (trList [output])
  let d₇ := emittedWordData d₆ (trList [0, 0, 1])
  let d₈ := emittedWordData d₇ (trList [input])
  let d₉ := emittedWordData d₈
    (trList [kind.sliceCode, 0, kind.secondInputDesired])
  have h₁ : EvalsToInTime (TM2.step program)
      (phaseCfg (.unaryStart kind) data)
      (some (copyCfg .fresh (.unaryAfterOutput₁ kind) d₁)) 1 := by
    simpa [d₁] using oneStep (step_unaryStart data kind)
  have h₂ : EvalsToInTime (TM2.step program)
      (copyCfg .fresh (.unaryAfterOutput₁ kind) d₁)
      (some (phaseCfg (.unaryAfterOutput₁ kind) d₂))
      (2 * (trNat output).length + 2) := by
    simpa [d₂, emittedWordData] using
      emitAtomField_trNat .fresh (.unaryAfterOutput₁ kind) d₁ output
        (by simpa [d₁, TapeData.atom] using freshValue)
        (by simpa [d₁] using scratchValue)
  have h₃ : EvalsToInTime (TM2.step program)
      (phaseCfg (.unaryAfterOutput₁ kind) d₂)
      (some (copyCfg .first (.unaryAfterInput₁ kind) d₃)) 1 := by
    simpa [d₃] using oneStep (step_unaryAfterOutput₁ d₂ kind)
  have h₄ : EvalsToInTime (TM2.step program)
      (copyCfg .first (.unaryAfterInput₁ kind) d₃)
      (some (phaseCfg (.unaryAfterInput₁ kind) d₄))
      (2 * (trNat input).length + 2) := by
    simpa [d₄, emittedWordData] using
      emitAtomField_trNat .first (.unaryAfterInput₁ kind) d₃ input
        (by simpa [d₃, d₂, d₁, TapeData.atom] using firstValue)
        (by simpa [d₃, d₂, d₁] using scratchValue)
  have h₅ : EvalsToInTime (TM2.step program)
      (phaseCfg (.unaryAfterInput₁ kind) d₄)
      (some (copyCfg .fresh (.unaryAfterOutput₂ kind) d₅)) 1 := by
    simpa [d₅] using oneStep (step_unaryAfterInput₁ d₄ kind)
  have h₆ : EvalsToInTime (TM2.step program)
      (copyCfg .fresh (.unaryAfterOutput₂ kind) d₅)
      (some (phaseCfg (.unaryAfterOutput₂ kind) d₆))
      (2 * (trNat output).length + 2) := by
    simpa [d₆, emittedWordData] using
      emitAtomField_trNat .fresh (.unaryAfterOutput₂ kind) d₅ output
        (by
          simpa [d₅, d₄, d₃, d₂, d₁, TapeData.atom]
            using freshValue)
        (by
          simpa [d₅, d₄, d₃, d₂, d₁]
            using scratchValue)
  have h₇ : EvalsToInTime (TM2.step program)
      (phaseCfg (.unaryAfterOutput₂ kind) d₆)
      (some (copyCfg .first (.unaryAfterInput₂ kind) d₇)) 1 := by
    simpa [d₇] using oneStep (step_unaryAfterOutput₂ d₆ kind)
  have h₈ : EvalsToInTime (TM2.step program)
      (copyCfg .first (.unaryAfterInput₂ kind) d₇)
      (some (phaseCfg (.unaryAfterInput₂ kind) d₈))
      (2 * (trNat input).length + 2) := by
    simpa [d₈, emittedWordData] using
      emitAtomField_trNat .first (.unaryAfterInput₂ kind) d₇ input
        (by
          simpa [d₇, d₆, d₅, d₄, d₃, d₂, d₁,
            TapeData.atom] using firstValue)
        (by
          simpa [d₇, d₆, d₅, d₄, d₃, d₂, d₁]
            using scratchValue)
  have h₉ : EvalsToInTime (TM2.step program)
      (phaseCfg (.unaryAfterInput₂ kind) d₈)
      (some (phaseCfg .gateDone d₉)) 1 := by
    simpa [d₉] using oneStep (step_unaryAfterInput₂ d₈ kind)
  have h₁₂ := EvalsToInTime.trans (TM2.step program)
    1 (2 * (trNat output).length + 2)
    (phaseCfg (.unaryStart kind) data)
    (copyCfg .fresh (.unaryAfterOutput₁ kind) d₁)
    (some (phaseCfg (.unaryAfterOutput₁ kind) d₂)) h₁ h₂
  have h₁₂₃ := EvalsToInTime.trans (TM2.step program)
    (2 * (trNat output).length + 2 + 1) 1
    (phaseCfg (.unaryStart kind) data)
    (phaseCfg (.unaryAfterOutput₁ kind) d₂)
    (some (copyCfg .first (.unaryAfterInput₁ kind) d₃)) h₁₂ h₃
  have h₁₂₃₄ := EvalsToInTime.trans (TM2.step program)
    (1 + (2 * (trNat output).length + 2 + 1))
    (2 * (trNat input).length + 2)
    (phaseCfg (.unaryStart kind) data)
    (copyCfg .first (.unaryAfterInput₁ kind) d₃)
    (some (phaseCfg (.unaryAfterInput₁ kind) d₄)) h₁₂₃ h₄
  have h₁₂₃₄₅ := EvalsToInTime.trans (TM2.step program)
    (2 * (trNat input).length + 2 +
      (1 + (2 * (trNat output).length + 2 + 1))) 1
    (phaseCfg (.unaryStart kind) data)
    (phaseCfg (.unaryAfterInput₁ kind) d₄)
    (some (copyCfg .fresh (.unaryAfterOutput₂ kind) d₅)) h₁₂₃₄ h₅
  have h₁₂₃₄₅₆ := EvalsToInTime.trans (TM2.step program)
    (1 + (2 * (trNat input).length + 2 +
      (1 + (2 * (trNat output).length + 2 + 1))))
    (2 * (trNat output).length + 2)
    (phaseCfg (.unaryStart kind) data)
    (copyCfg .fresh (.unaryAfterOutput₂ kind) d₅)
    (some (phaseCfg (.unaryAfterOutput₂ kind) d₆)) h₁₂₃₄₅ h₆
  have h₁₂₃₄₅₆₇ := EvalsToInTime.trans (TM2.step program)
    (2 * (trNat output).length + 2 +
      (1 + (2 * (trNat input).length + 2 +
        (1 + (2 * (trNat output).length + 2 + 1))))) 1
    (phaseCfg (.unaryStart kind) data)
    (phaseCfg (.unaryAfterOutput₂ kind) d₆)
    (some (copyCfg .first (.unaryAfterInput₂ kind) d₇)) h₁₂₃₄₅₆ h₇
  have h₁₂₃₄₅₆₇₈ := EvalsToInTime.trans (TM2.step program)
    (1 + (2 * (trNat output).length + 2 +
      (1 + (2 * (trNat input).length + 2 +
        (1 + (2 * (trNat output).length + 2 + 1))))))
    (2 * (trNat input).length + 2)
    (phaseCfg (.unaryStart kind) data)
    (copyCfg .first (.unaryAfterInput₂ kind) d₇)
    (some (phaseCfg (.unaryAfterInput₂ kind) d₈)) h₁₂₃₄₅₆₇ h₈
  have composed := EvalsToInTime.trans (TM2.step program)
    (2 * (trNat input).length + 2 +
      (1 + (2 * (trNat output).length + 2 +
        (1 + (2 * (trNat input).length + 2 +
          (1 + (2 * (trNat output).length + 2 + 1))))))) 1
    (phaseCfg (.unaryStart kind) data)
    (phaseCfg (.unaryAfterInput₂ kind) d₈)
    (some (phaseCfg .gateDone d₉)) h₁₂₃₄₅₆₇₈ h₉
  have finalData :
      d₉ =
        { data with
          outputReverse :=
            (trList (unaryGateFields kind output input)).reverse ++
              data.outputReverse } := by
    rw [unaryGateFields_native]
    rcases data with
      ⟨inputWord, outputReverse, finalOutput, fresh, roots, firstRoot,
        secondRoot, scratch⟩
    cases kind <;>
      simp [d₉, d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁,
        emittedWordData, trList, List.reverse_append, List.append_assoc]
  rw [finalData] at composed
  convert composed using 1 <;> omega

/-- The shared finite-control script for conjunction and disjunction Tseitin
gates emits the exact three-clause native field block and restores all three
atom registers. -/
def emitBinaryGate (kind : BinaryGateKind) (data : TapeData)
    (output first second : Nat)
    (freshValue : data.fresh = trNat output)
    (firstValue : data.first = trNat first)
    (secondValue : data.second = trNat second)
    (scratchValue : data.scratch = []) :
    EvalsToInTime (TM2.step program)
      (phaseCfg (.binaryStart kind) data)
      (some (phaseCfg .gateDone
        { data with
          outputReverse :=
            (trList (binaryGateFields kind output first second)).reverse ++
              data.outputReverse }))
      (6 * (trNat output).length + 4 * (trNat first).length +
        4 * (trNat second).length + 22) := by
  let d₁ := emittedWordData data (trList [2])
  let d₂ := emittedWordData d₁ (trList [output])
  let d₃ := emittedWordData d₂
    (trList [0, 0, kind.shortOutputDesired])
  let d₄ := emittedWordData d₃ (trList [first])
  let d₅ := emittedWordData d₄
    (trList [0, 0, kind.shortInputDesired, 2])
  let d₆ := emittedWordData d₅ (trList [output])
  let d₇ := emittedWordData d₆
    (trList [0, 0, kind.shortOutputDesired])
  let d₈ := emittedWordData d₇ (trList [second])
  let d₉ := emittedWordData d₈
    (trList [0, 0, kind.shortInputDesired, 3])
  let d₁₀ := emittedWordData d₉ (trList [output])
  let d₁₁ := emittedWordData d₁₀
    (trList [0, 0, kind.longOutputDesired])
  let d₁₂ := emittedWordData d₁₁ (trList [first])
  let d₁₃ := emittedWordData d₁₂
    (trList [0, 0, kind.longInputDesired])
  let d₁₄ := emittedWordData d₁₃ (trList [second])
  let d₁₅ := emittedWordData d₁₄
    (trList [0, 0, kind.longInputDesired])
  have h₁ : EvalsToInTime (TM2.step program)
      (phaseCfg (.binaryStart kind) data)
      (some (phaseCfg (.binaryAfterOutput₁ kind) d₂))
      (2 * (trNat output).length + 3) := by
    simpa [d₂, d₁] using
      emitFixedThenAtom .fresh data (trList [2]) output
        (step_binaryStart data kind)
        (by simpa [TapeData.atom] using freshValue)
        scratchValue
  have h₂ : EvalsToInTime (TM2.step program)
      (phaseCfg (.binaryAfterOutput₁ kind) d₂)
      (some (phaseCfg (.binaryAfterFirst₁ kind) d₄))
      (2 * (trNat first).length + 3) := by
    simpa [d₄, d₃] using
      emitFixedThenAtom .first d₂
        (trList [0, 0, kind.shortOutputDesired]) first
        (step_binaryAfterOutput₁ d₂ kind)
        (by simpa [d₂, d₁, TapeData.atom] using firstValue)
        (by simpa [d₂, d₁] using scratchValue)
  have h₃ : EvalsToInTime (TM2.step program)
      (phaseCfg (.binaryAfterFirst₁ kind) d₄)
      (some (phaseCfg (.binaryAfterOutput₂ kind) d₆))
      (2 * (trNat output).length + 3) := by
    simpa [d₆, d₅] using
      emitFixedThenAtom .fresh d₄
        (trList [0, 0, kind.shortInputDesired, 2]) output
        (step_binaryAfterFirst₁ d₄ kind)
        (by
          simpa [d₄, d₃, d₂, d₁, TapeData.atom]
            using freshValue)
        (by simpa [d₄, d₃, d₂, d₁] using scratchValue)
  have h₄ : EvalsToInTime (TM2.step program)
      (phaseCfg (.binaryAfterOutput₂ kind) d₆)
      (some (phaseCfg (.binaryAfterSecond₁ kind) d₈))
      (2 * (trNat second).length + 3) := by
    simpa [d₈, d₇] using
      emitFixedThenAtom .second d₆
        (trList [0, 0, kind.shortOutputDesired]) second
        (step_binaryAfterOutput₂ d₆ kind)
        (by
          simpa [d₆, d₅, d₄, d₃, d₂, d₁, TapeData.atom]
            using secondValue)
        (by
          simpa [d₆, d₅, d₄, d₃, d₂, d₁]
            using scratchValue)
  have h₅ : EvalsToInTime (TM2.step program)
      (phaseCfg (.binaryAfterSecond₁ kind) d₈)
      (some (phaseCfg (.binaryAfterOutput₃ kind) d₁₀))
      (2 * (trNat output).length + 3) := by
    simpa [d₁₀, d₉] using
      emitFixedThenAtom .fresh d₈
        (trList [0, 0, kind.shortInputDesired, 3]) output
        (step_binaryAfterSecond₁ d₈ kind)
        (by
          simpa [d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁,
            TapeData.atom] using freshValue)
        (by
          simpa [d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁]
            using scratchValue)
  have h₆ : EvalsToInTime (TM2.step program)
      (phaseCfg (.binaryAfterOutput₃ kind) d₁₀)
      (some (phaseCfg (.binaryAfterFirst₂ kind) d₁₂))
      (2 * (trNat first).length + 3) := by
    simpa [d₁₂, d₁₁] using
      emitFixedThenAtom .first d₁₀
        (trList [0, 0, kind.longOutputDesired]) first
        (step_binaryAfterOutput₃ d₁₀ kind)
        (by
          simpa [d₁₀, d₉, d₈, d₇, d₆, d₅, d₄, d₃, d₂,
            d₁, TapeData.atom] using firstValue)
        (by
          simpa [d₁₀, d₉, d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁]
            using scratchValue)
  have h₇ : EvalsToInTime (TM2.step program)
      (phaseCfg (.binaryAfterFirst₂ kind) d₁₂)
      (some (phaseCfg (.binaryAfterSecond₂ kind) d₁₄))
      (2 * (trNat second).length + 3) := by
    simpa [d₁₄, d₁₃] using
      emitFixedThenAtom .second d₁₂
        (trList [0, 0, kind.longInputDesired]) second
        (step_binaryAfterFirst₂ d₁₂ kind)
        (by
          simpa [d₁₂, d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, d₄, d₃,
            d₂, d₁, TapeData.atom] using secondValue)
        (by
          simpa [d₁₂, d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, d₄, d₃,
            d₂, d₁] using scratchValue)
  have h₈ : EvalsToInTime (TM2.step program)
      (phaseCfg (.binaryAfterSecond₂ kind) d₁₄)
      (some (phaseCfg .gateDone d₁₅)) 1 := by
    simpa [d₁₅] using
      oneStep (step_binaryAfterSecond₂ d₁₄ kind)
  have composed :=
    thenRun (thenRun (thenRun (thenRun (thenRun (thenRun (thenRun h₁ h₂) h₃) h₄) h₅) h₆) h₇) h₈
  have finalData :
      d₁₅ =
        { data with
          outputReverse :=
            (trList (binaryGateFields kind output first second)).reverse ++
              data.outputReverse } := by
    rw [binaryGateFields_native]
    rcases data with
      ⟨inputWord, outputReverse, finalOutput, fresh, roots, firstRoot,
        secondRoot, scratch⟩
    cases kind <;>
      simp [d₁₅, d₁₄, d₁₃, d₁₂, d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅,
        d₄, d₃, d₂, d₁, emittedWordData, trList,
        List.reverse_append, List.append_assoc]
  rw [finalData] at composed
  convert composed using 1 <;> omega

end TransitionEvaluatorMachine
end PeriodicCNF
end LeanTrominoes
