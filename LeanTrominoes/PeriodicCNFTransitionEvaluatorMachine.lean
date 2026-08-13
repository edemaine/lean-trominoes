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

/-- Delimited-field stacks consumed by the evaluator. -/
inductive FieldSource
  | input
  | roots
  deriving DecidableEq, Fintype

namespace FieldSource

def stack : FieldSource → Stack
  | .input => .input
  | .roots => .roots

end FieldSource

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

/-- Actions selected after the finite decoder consumes a tag or payload
delimiter. -/
inductive DelimiterAction
  | wire
  | negate
  | conjunction
  | disjunction
  | constantTrue
  | wireNext
  deriving DecidableEq, Fintype

/-- Continuations of variable-atom emission.  More gate phases are added by
the evaluator layer; `done` is enough to state and test the primitive in
isolation. -/
inductive Phase
  | done
  | gateDone
  | readFresh
  | decodeNext
  | binaryReadFirst (kind : BinaryGateKind)
  | afterClearFirst
  | afterClearSecond
  | afterPushRoot
  | finalReadRoot
  | finalConstantStart
  | finalConstantTail
  | finalReverse
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
  | copyInputField (next : Phase)
  | readField (source : FieldSource) (target : AtomSource) (next : Phase)
  | prepareFreshRoot (next : Phase)
  | saveFreshRoot (next : Phase)
  | restoreFreshRoot (next : Phase)
  | clearAtom (source : AtomSource) (next : Phase)
  | reverseOutput
  | decodeTag
  | tagAfterBit₁
  | tagAfterBit₀
  | tagAfterBit₀₀
  | expectDelimiter (action : DelimiterAction)
  | readConstantValue
  | readWireSlice
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

def jump (next : Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => none) (.goto fun _ => next)

def afterDelimiterLabel : DelimiterAction → Label
  | .wire => .readWireSlice
  | .negate => .readField .roots .first (.unaryStart .negation)
  | .conjunction =>
      .readField .roots .second (.binaryReadFirst .conjunction)
  | .disjunction =>
      .readField .roots .second (.binaryReadFirst .disjunction)
  | .constantTrue => .phase (.constantStart true)
  | .wireNext =>
      .readField .input .first (.unaryStart .equalityNext)

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
  | .copyInputField next =>
      .pop .input (fun _ symbol => symbol)
        (.branch Option.isNone
          .halt
          (.branch (fun state => state = some .cons)
            (.push .outputReverse (fun state => state.getD default)
              (.load (fun _ => none) (.goto fun _ => .phase next)))
            (.push .outputReverse (fun state => state.getD default)
              (.load (fun _ => none)
                (.goto fun _ => .copyInputField next)))))
  | .readField source target next =>
      .pop source.stack (fun _ symbol => symbol)
        (.branch Option.isNone
          .halt
          (.branch (fun state => state = some .cons)
            (.load (fun _ => none)
              (.goto fun _ => .restoreAtom target next))
            (.push .scratch (fun state => state.getD default)
              (.load (fun _ => none)
                (.goto fun _ => .readField source target next)))))
  | .prepareFreshRoot next =>
      .push .roots (fun _ => .cons)
        (.load (fun _ => none) (.goto fun _ => .saveFreshRoot next))
  | .saveFreshRoot next =>
      .pop .fresh (fun _ symbol => symbol)
        (.branch Option.isNone
          (.load (fun _ => none) (.goto fun _ => .restoreFreshRoot next))
          (.push .scratch (fun state => state.getD default)
            (.load (fun _ => none)
              (.goto fun _ => .saveFreshRoot next))))
  | .restoreFreshRoot next =>
      .pop .scratch (fun _ symbol => symbol)
        (.branch Option.isNone
          (.load (fun _ => none) (.goto fun _ => .phase next))
          (.push .fresh (fun state => state.getD default)
            (.push .roots (fun state => state.getD default)
              (.load (fun _ => none)
                (.goto fun _ => .restoreFreshRoot next)))))
  | .clearAtom source next =>
      .pop source.stack (fun _ symbol => symbol)
        (.branch Option.isNone
          (.load (fun _ => none) (.goto fun _ => .phase next))
          (.load (fun _ => none) (.goto fun _ => .clearAtom source next)))
  | .reverseOutput =>
      .pop .outputReverse (fun _ symbol => symbol)
        (.branch Option.isNone
          (.load (fun _ => none) (.goto fun _ => .phase .done))
          (.push .output (fun state => state.getD default)
            (.load (fun _ => none) (.goto fun _ => .reverseOutput))))
  | .decodeTag =>
      .pop .input (fun _ symbol => symbol)
        (.branch Option.isNone
          (jump (.clearAtom .fresh .finalReadRoot))
          (.branch (fun state => state = some .cons)
            (jump .readConstantValue)
            (.branch (fun state => state = some .bit1)
              (jump .tagAfterBit₁)
              (.branch (fun state => state = some .bit0)
                (jump .tagAfterBit₀)
                .halt))))
  | .tagAfterBit₁ =>
      .pop .input (fun _ symbol => symbol)
        (.branch (fun state => state = some .cons)
          (jump .readWireSlice)
          (.branch (fun state => state = some .bit1)
            (jump (.expectDelimiter .conjunction))
            .halt))
  | .tagAfterBit₀ =>
      .pop .input (fun _ symbol => symbol)
        (.branch (fun state => state = some .bit1)
          (jump (.expectDelimiter .negate))
          (.branch (fun state => state = some .bit0)
            (jump .tagAfterBit₀₀)
            .halt))
  | .tagAfterBit₀₀ =>
      .pop .input (fun _ symbol => symbol)
        (.branch (fun state => state = some .bit1)
          (jump (.expectDelimiter .disjunction))
          .halt)
  | .expectDelimiter action =>
      .pop .input (fun _ symbol => symbol)
        (.branch (fun state => state = some .cons)
          (jump (afterDelimiterLabel action))
          .halt)
  | .readConstantValue =>
      .pop .input (fun _ symbol => symbol)
        (.branch (fun state => state = some .cons)
          (jump (.phase (.constantStart false)))
          (.branch (fun state => state = some .bit1)
            (jump (.expectDelimiter .constantTrue))
            .halt))
  | .readWireSlice =>
      .pop .input (fun _ symbol => symbol)
        (.branch (fun state => state = some .cons)
          (jump (.readField .input .first
            (.unaryStart .equalityCurrent)))
          (.branch (fun state => state = some .bit1)
            (jump (.expectDelimiter .wireNext))
            .halt))
  | .phase .done => .halt
  | .phase .gateDone =>
      jump (.clearAtom .first .afterClearFirst)
  | .phase .readFresh =>
      jump (.readField .input .fresh .decodeNext)
  | .phase .decodeNext =>
      jump .decodeTag
  | .phase (.binaryReadFirst kind) =>
      jump (.readField .roots .first (.binaryStart kind))
  | .phase .afterClearFirst =>
      jump (.clearAtom .second .afterClearSecond)
  | .phase .afterClearSecond =>
      jump (.prepareFreshRoot .afterPushRoot)
  | .phase .afterPushRoot =>
      jump (.incrementFresh .decodeNext)
  | .phase .finalReadRoot =>
      jump (.readField .roots .fresh .finalConstantStart)
  | .phase .finalConstantStart =>
      emitFixedFields [1] (.copyAtom .fresh .finalConstantTail)
  | .phase .finalConstantTail =>
      emitFixedFields [0, 0, 1] (.clearAtom .fresh .finalReverse)
  | .phase .finalReverse =>
      jump .reverseOutput
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
  main := .copyInputField .readFresh
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

def field (data : TapeData) : FieldSource → List Γ'
  | .input => data.input
  | .roots => data.roots

def setField (data : TapeData) : FieldSource → List Γ' → TapeData
  | .input, value => { data with input := value }
  | .roots, value => { data with roots := value }

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

@[simp]
theorem field_setField (data : TapeData) (source : FieldSource)
    (value : List Γ') :
    (data.setField source value).field source = value := by
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

def copyInputFieldCfg (next : Phase) (data : TapeData) :
    TM2.Cfg Alphabet Label State :=
  ⟨some (.copyInputField next), none, tapes data⟩

def readFieldCfg (source : FieldSource) (target : AtomSource)
    (next : Phase) (data : TapeData) : TM2.Cfg Alphabet Label State :=
  ⟨some (.readField source target next), none, tapes data⟩

def prepareFreshRootCfg (next : Phase) (data : TapeData) :
    TM2.Cfg Alphabet Label State :=
  ⟨some (.prepareFreshRoot next), none, tapes data⟩

def saveFreshRootCfg (next : Phase) (data : TapeData) :
    TM2.Cfg Alphabet Label State :=
  ⟨some (.saveFreshRoot next), none, tapes data⟩

def restoreFreshRootCfg (next : Phase) (data : TapeData) :
    TM2.Cfg Alphabet Label State :=
  ⟨some (.restoreFreshRoot next), none, tapes data⟩

def clearAtomCfg (source : AtomSource) (next : Phase) (data : TapeData) :
    TM2.Cfg Alphabet Label State :=
  ⟨some (.clearAtom source next), none, tapes data⟩

def reverseOutputCfg (data : TapeData) : TM2.Cfg Alphabet Label State :=
  ⟨some .reverseOutput, none, tapes data⟩

def controlCfg (label : Label) (data : TapeData) :
    TM2.Cfg Alphabet Label State :=
  ⟨some label, none, tapes data⟩

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
theorem update_tapes_input (data : TapeData) (value : List Γ') :
    Function.update (tapes data) Stack.input value =
      tapes { data with input := value } := by
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

theorem step_phase_readFresh (data : TapeData) :
    TM2.step program (phaseCfg .readFresh data) =
      some (readFieldCfg .input .fresh .decodeNext data) := by
  simp [TM2.step, program, phaseCfg, readFieldCfg, jump]

theorem step_phase_decodeNext (data : TapeData) :
    TM2.step program (phaseCfg .decodeNext data) =
      some (controlCfg .decodeTag data) := by
  simp [TM2.step, program, phaseCfg, controlCfg, jump]

theorem step_phase_binaryReadFirst (kind : BinaryGateKind)
    (data : TapeData) :
    TM2.step program (phaseCfg (.binaryReadFirst kind) data) =
      some (readFieldCfg .roots .first (.binaryStart kind) data) := by
  simp [TM2.step, program, phaseCfg, readFieldCfg, jump]

theorem step_phase_gateDone (data : TapeData) :
    TM2.step program (phaseCfg .gateDone data) =
      some (clearAtomCfg .first .afterClearFirst data) := by
  simp [TM2.step, program, phaseCfg, clearAtomCfg, jump]

theorem step_phase_afterClearFirst (data : TapeData) :
    TM2.step program (phaseCfg .afterClearFirst data) =
      some (clearAtomCfg .second .afterClearSecond data) := by
  simp [TM2.step, program, phaseCfg, clearAtomCfg, jump]

theorem step_phase_afterClearSecond (data : TapeData) :
    TM2.step program (phaseCfg .afterClearSecond data) =
      some (prepareFreshRootCfg .afterPushRoot data) := by
  simp [TM2.step, program, phaseCfg, prepareFreshRootCfg, jump]

theorem step_phase_afterPushRoot (data : TapeData) :
    TM2.step program (phaseCfg .afterPushRoot data) =
      some (incrementCfg .decodeNext data) := by
  simp [TM2.step, program, phaseCfg, incrementCfg, jump]

theorem step_phase_finalReadRoot (data : TapeData) :
    TM2.step program (phaseCfg .finalReadRoot data) =
      some (readFieldCfg .roots .fresh .finalConstantStart data) := by
  simp [TM2.step, program, phaseCfg, readFieldCfg, jump]

theorem step_finalConstantStart (data : TapeData) :
    TM2.step program (phaseCfg .finalConstantStart data) =
      some (copyCfg .fresh .finalConstantTail
        (emittedWordData data (trList [1]))) := by
  simp only [TM2.step, program, phaseCfg, emitFixedFields]
  rw [stepAux_pushOutputWord]
  simp [copyCfg, emittedWordData, tapes]

theorem step_finalConstantTail (data : TapeData) :
    TM2.step program (phaseCfg .finalConstantTail data) =
      some (clearAtomCfg .fresh .finalReverse
        (emittedWordData data (trList [0, 0, 1]))) := by
  simp only [TM2.step, program, phaseCfg, emitFixedFields]
  rw [stepAux_pushOutputWord]
  simp [clearAtomCfg, emittedWordData, tapes]

theorem step_phase_finalReverse (data : TapeData) :
    TM2.step program (phaseCfg .finalReverse data) =
      some (reverseOutputCfg data) := by
  simp [TM2.step, program, phaseCfg, reverseOutputCfg, jump]

def consumedInputData (data : TapeData) (tail : List Γ') : TapeData :=
  { data with input := tail }

theorem step_decodeTag_nil (data : TapeData) (inputValue : data.input = []) :
    TM2.step program (controlCfg .decodeTag data) =
      some (controlCfg (.clearAtom .fresh .finalReadRoot)
        (consumedInputData data [])) := by
  simp [TM2.step, program, controlCfg, consumedInputData, jump,
    inputValue, tapes]

theorem step_decodeTag_cons (data : TapeData) (tail : List Γ')
    (inputValue : data.input = .cons :: tail) :
    TM2.step program (controlCfg .decodeTag data) =
      some (controlCfg .readConstantValue
        (consumedInputData data tail)) := by
  simp [TM2.step, program, controlCfg, consumedInputData, jump,
    inputValue, tapes]

theorem step_decodeTag_bit₁ (data : TapeData) (tail : List Γ')
    (inputValue : data.input = .bit1 :: tail) :
    TM2.step program (controlCfg .decodeTag data) =
      some (controlCfg .tagAfterBit₁
        (consumedInputData data tail)) := by
  simp [TM2.step, program, controlCfg, consumedInputData, jump,
    inputValue, tapes]

theorem step_decodeTag_bit₀ (data : TapeData) (tail : List Γ')
    (inputValue : data.input = .bit0 :: tail) :
    TM2.step program (controlCfg .decodeTag data) =
      some (controlCfg .tagAfterBit₀
        (consumedInputData data tail)) := by
  simp [TM2.step, program, controlCfg, consumedInputData, jump,
    inputValue, tapes]

theorem step_tagAfterBit₁_wire (data : TapeData) (tail : List Γ')
    (inputValue : data.input = .cons :: tail) :
    TM2.step program (controlCfg .tagAfterBit₁ data) =
      some (controlCfg .readWireSlice
        (consumedInputData data tail)) := by
  simp [TM2.step, program, controlCfg, consumedInputData, jump,
    inputValue, tapes]

theorem step_tagAfterBit₁_conjunction (data : TapeData)
    (tail : List Γ') (inputValue : data.input = .bit1 :: tail) :
    TM2.step program (controlCfg .tagAfterBit₁ data) =
      some (controlCfg (.expectDelimiter .conjunction)
        (consumedInputData data tail)) := by
  simp [TM2.step, program, controlCfg, consumedInputData, jump,
    inputValue, tapes]

theorem step_tagAfterBit₀_negate (data : TapeData) (tail : List Γ')
    (inputValue : data.input = .bit1 :: tail) :
    TM2.step program (controlCfg .tagAfterBit₀ data) =
      some (controlCfg (.expectDelimiter .negate)
        (consumedInputData data tail)) := by
  simp [TM2.step, program, controlCfg, consumedInputData, jump,
    inputValue, tapes]

theorem step_tagAfterBit₀_disjunction (data : TapeData)
    (tail : List Γ') (inputValue : data.input = .bit0 :: tail) :
    TM2.step program (controlCfg .tagAfterBit₀ data) =
      some (controlCfg .tagAfterBit₀₀
        (consumedInputData data tail)) := by
  simp [TM2.step, program, controlCfg, consumedInputData, jump,
    inputValue, tapes]

theorem step_tagAfterBit₀₀_disjunction (data : TapeData)
    (tail : List Γ') (inputValue : data.input = .bit1 :: tail) :
    TM2.step program (controlCfg .tagAfterBit₀₀ data) =
      some (controlCfg (.expectDelimiter .disjunction)
        (consumedInputData data tail)) := by
  simp [TM2.step, program, controlCfg, consumedInputData, jump,
    inputValue, tapes]

theorem step_expectDelimiter (action : DelimiterAction) (data : TapeData)
    (tail : List Γ') (inputValue : data.input = .cons :: tail) :
    TM2.step program (controlCfg (.expectDelimiter action) data) =
      some (controlCfg (afterDelimiterLabel action)
        (consumedInputData data tail)) := by
  simp [TM2.step, program, controlCfg, consumedInputData, jump,
    inputValue, tapes]

theorem step_readConstantValue_false (data : TapeData) (tail : List Γ')
    (inputValue : data.input = .cons :: tail) :
    TM2.step program (controlCfg .readConstantValue data) =
      some (phaseCfg (.constantStart false)
        (consumedInputData data tail)) := by
  simp [TM2.step, program, controlCfg, phaseCfg, consumedInputData, jump,
    inputValue, tapes]

theorem step_readConstantValue_true (data : TapeData) (tail : List Γ')
    (inputValue : data.input = .bit1 :: tail) :
    TM2.step program (controlCfg .readConstantValue data) =
      some (controlCfg (.expectDelimiter .constantTrue)
        (consumedInputData data tail)) := by
  simp [TM2.step, program, controlCfg, consumedInputData, jump,
    inputValue, tapes]

theorem step_readWireSlice_current (data : TapeData) (tail : List Γ')
    (inputValue : data.input = .cons :: tail) :
    TM2.step program (controlCfg .readWireSlice data) =
      some (readFieldCfg .input .first (.unaryStart .equalityCurrent)
        (consumedInputData data tail)) := by
  simp [TM2.step, program, controlCfg, readFieldCfg, consumedInputData,
    jump, inputValue, tapes]

theorem step_readWireSlice_next (data : TapeData) (tail : List Γ')
    (inputValue : data.input = .bit1 :: tail) :
    TM2.step program (controlCfg .readWireSlice data) =
      some (controlCfg (.expectDelimiter .wireNext)
        (consumedInputData data tail)) := by
  simp [TM2.step, program, controlCfg, consumedInputData, jump,
    inputValue, tapes]

def constantTagTime (value : Bool) : Nat :=
  if value then 3 else 2

@[simp] theorem trNat_one : trNat 1 = [Γ'.bit1] := by native_decide
@[simp] theorem trNat_two : trNat 2 = [Γ'.bit0, Γ'.bit1] := by native_decide
@[simp] theorem trNat_three : trNat 3 = [Γ'.bit1, Γ'.bit1] := by native_decide
@[simp] theorem trNat_four : trNat 4 = [Γ'.bit0, Γ'.bit0, Γ'.bit1] := by
  native_decide

/-- The generated constant-instruction tag and Boolean payload select the
matching constant-gate routine. -/
def decodeConstantTag (value : Bool) (data : TapeData) (rest : List Γ')
    (inputValue :
      data.input = trList (TransitionInstruction.fields (.constant value)) ++
        rest) :
    EvalsToInTime (TM2.step program)
      (controlCfg .decodeTag data)
      (some (phaseCfg (.constantStart value)
        { data with input := rest }))
      (constantTagTime value) := by
  cases value with
  | false =>
      let d₁ := consumedInputData data (.cons :: rest)
      have h₁ := oneStep (step_decodeTag_cons data (.cons :: rest) (by
        simpa [TransitionInstruction.fields, trList] using inputValue))
      have h₂ := oneStep (step_readConstantValue_false d₁ rest (by
        simp [d₁, consumedInputData]))
      have composed := thenRun h₁ h₂
      simpa [constantTagTime, d₁, consumedInputData] using composed
  | true =>
      let d₁ := consumedInputData data (.bit1 :: .cons :: rest)
      let d₂ := consumedInputData d₁ (.cons :: rest)
      have h₁ := oneStep
        (step_decodeTag_cons data (.bit1 :: .cons :: rest) (by
          simpa [TransitionInstruction.fields, trList] using inputValue))
      have h₂ := oneStep (step_readConstantValue_true d₁
        (.cons :: rest) (by simp [d₁, consumedInputData]))
      have h₃ := oneStep
        (step_expectDelimiter .constantTrue d₂ rest (by
          simp [d₂, d₁, consumedInputData]))
      have composed := thenRun (thenRun h₁ h₂) h₃
      simpa [constantTagTime, d₂, d₁, consumedInputData,
        afterDelimiterLabel, controlCfg, phaseCfg] using composed

def wireTagTime (slice : TransitionSlice) : Nat :=
  match slice with
  | .current => 3
  | .next => 4

/-- A generated wire tag and slice payload select the right equality-gate
routine and leave the atom field ready for the native field reader. -/
def decodeWireTag (wire : TransitionWire) (data : TapeData)
    (rest : List Γ')
    (inputValue :
      data.input = trList (TransitionInstruction.fields (.wire wire)) ++
        rest) :
    EvalsToInTime (TM2.step program)
      (controlCfg .decodeTag data)
      (some (readFieldCfg .input .first
        (.unaryStart (match wire.slice with
          | .current => .equalityCurrent
          | .next => .equalityNext))
        { data with input := trList [wire.atom] ++ rest }))
      (wireTagTime wire.slice) := by
  rcases wire with ⟨slice, atom⟩
  cases slice with
  | current =>
      let d₁ := consumedInputData data (.cons :: .cons :: trList [atom] ++ rest)
      let d₂ := consumedInputData d₁ (.cons :: trList [atom] ++ rest)
      have h₁ := oneStep
        (step_decodeTag_bit₁ data
          (.cons :: .cons :: trList [atom] ++ rest) (by
            simpa [TransitionInstruction.fields, trList] using inputValue))
      have h₂ := oneStep
        (step_tagAfterBit₁_wire d₁
          (.cons :: trList [atom] ++ rest) (by
            simp [d₁, consumedInputData]))
      have h₃ := oneStep
        (step_readWireSlice_current d₂ (trList [atom] ++ rest) (by
          simp [d₂, d₁, consumedInputData]))
      have composed := thenRun (thenRun h₁ h₂) h₃
      simpa [wireTagTime, d₂, d₁, consumedInputData] using composed
  | next =>
      let d₁ := consumedInputData data
        (.cons :: .bit1 :: .cons :: trList [atom] ++ rest)
      let d₂ := consumedInputData d₁
        (.bit1 :: .cons :: trList [atom] ++ rest)
      let d₃ := consumedInputData d₂
        (.cons :: trList [atom] ++ rest)
      have h₁ := oneStep
        (step_decodeTag_bit₁ data
          (.cons :: .bit1 :: .cons :: trList [atom] ++ rest) (by
            simpa [TransitionInstruction.fields, trList] using inputValue))
      have h₂ := oneStep
        (step_tagAfterBit₁_wire d₁
          (.bit1 :: .cons :: trList [atom] ++ rest) (by
            simp [d₁, consumedInputData]))
      have h₃ := oneStep
        (step_readWireSlice_next d₂
          (.cons :: trList [atom] ++ rest) (by
            simp [d₂, d₁, consumedInputData]))
      have h₄ := oneStep
        (step_expectDelimiter .wireNext d₃ (trList [atom] ++ rest) (by
          simp [d₃, d₂, d₁, consumedInputData]))
      have composed := thenRun (thenRun (thenRun h₁ h₂) h₃) h₄
      simpa [wireTagTime, d₃, d₂, d₁, consumedInputData,
        afterDelimiterLabel, controlCfg, readFieldCfg] using composed

/-- The generated negation tag selects root-pop followed by the negation
gate. -/
def decodeNegateTag (data : TapeData) (rest : List Γ')
    (inputValue :
      data.input = trList (TransitionInstruction.fields .negate) ++ rest) :
    EvalsToInTime (TM2.step program)
      (controlCfg .decodeTag data)
      (some (readFieldCfg .roots .first (.unaryStart .negation)
        { data with input := rest })) 3 := by
  let d₁ := consumedInputData data (.bit1 :: .cons :: rest)
  let d₂ := consumedInputData d₁ (.cons :: rest)
  have h₁ := oneStep
    (step_decodeTag_bit₀ data (.bit1 :: .cons :: rest) (by
      simpa [TransitionInstruction.fields, trList] using inputValue))
  have h₂ := oneStep
    (step_tagAfterBit₀_negate d₁ (.cons :: rest) (by
      simp [d₁, consumedInputData]))
  have h₃ := oneStep
    (step_expectDelimiter .negate d₂ rest (by
      simp [d₂, d₁, consumedInputData]))
  have composed := thenRun (thenRun h₁ h₂) h₃
  simpa [d₂, d₁, consumedInputData, afterDelimiterLabel,
    controlCfg, readFieldCfg] using composed

def binaryTagTime (kind : BinaryGateKind) : Nat :=
  match kind with
  | .conjunction => 3
  | .disjunction => 4

/-- Generated binary tags select the matching first root-pop phase. -/
def decodeBinaryTag (kind : BinaryGateKind) (data : TapeData)
    (rest : List Γ')
    (inputValue : data.input = trList
      (TransitionInstruction.fields (match kind with
        | .conjunction => .conjoin
        | .disjunction => .disjoin)) ++ rest) :
    EvalsToInTime (TM2.step program)
      (controlCfg .decodeTag data)
      (some (readFieldCfg .roots .second (.binaryReadFirst kind)
        { data with input := rest }))
      (binaryTagTime kind) := by
  cases kind with
  | conjunction =>
      let d₁ := consumedInputData data (.bit1 :: .cons :: rest)
      let d₂ := consumedInputData d₁ (.cons :: rest)
      have h₁ := oneStep
        (step_decodeTag_bit₁ data (.bit1 :: .cons :: rest) (by
          simpa [TransitionInstruction.fields, trList] using inputValue))
      have h₂ := oneStep
        (step_tagAfterBit₁_conjunction d₁ (.cons :: rest) (by
          simp [d₁, consumedInputData]))
      have h₃ := oneStep
        (step_expectDelimiter .conjunction d₂ rest (by
          simp [d₂, d₁, consumedInputData]))
      have composed := thenRun (thenRun h₁ h₂) h₃
      simpa [binaryTagTime, d₂, d₁, consumedInputData,
        afterDelimiterLabel, controlCfg, readFieldCfg] using composed
  | disjunction =>
      let d₁ := consumedInputData data
        (.bit0 :: .bit1 :: .cons :: rest)
      let d₂ := consumedInputData d₁ (.bit1 :: .cons :: rest)
      let d₃ := consumedInputData d₂ (.cons :: rest)
      have h₁ := oneStep
        (step_decodeTag_bit₀ data
          (.bit0 :: .bit1 :: .cons :: rest) (by
            simpa [TransitionInstruction.fields, trList] using inputValue))
      have h₂ := oneStep
        (step_tagAfterBit₀_disjunction d₁
          (.bit1 :: .cons :: rest) (by
            simp [d₁, consumedInputData]))
      have h₃ := oneStep
        (step_tagAfterBit₀₀_disjunction d₂ (.cons :: rest) (by
          simp [d₂, d₁, consumedInputData]))
      have h₄ := oneStep
        (step_expectDelimiter .disjunction d₃ rest (by
          simp [d₃, d₂, d₁, consumedInputData]))
      have composed := thenRun (thenRun (thenRun h₁ h₂) h₃) h₄
      simpa [binaryTagTime, d₃, d₂, d₁, consumedInputData,
        afterDelimiterLabel, controlCfg, readFieldCfg] using composed

def copiedInputSymbolData (data : TapeData) (symbol : Γ')
    (tail : List Γ') : TapeData :=
  { data with
    input := tail
    outputReverse := symbol :: data.outputReverse }

def readFieldSymbolData (data : TapeData) (source : FieldSource)
    (symbol : Γ') (tail : List Γ') : TapeData :=
  { data.setField source tail with
    scratch := symbol :: data.scratch }

theorem step_copyInputField_symbol (next : Phase) (data : TapeData)
    (symbol : Γ') (tail : List Γ') (notDelimiter : symbol ≠ .cons)
    (inputValue : data.input = symbol :: tail) :
    TM2.step program (copyInputFieldCfg next data) =
      some (copyInputFieldCfg next
        (copiedInputSymbolData data symbol tail)) := by
  rcases data with
    ⟨input, outputReverse, output, fresh, roots, first, second, scratch⟩
  change input = symbol :: tail at inputValue
  subst input
  cases symbol <;>
    simp_all [TM2.step, program, copyInputFieldCfg,
      copiedInputSymbolData, tapes, Function.update]
  all_goals
    funext stack
    cases stack <;> simp [tapes, Function.update]

theorem step_copyInputField_delimiter (next : Phase) (data : TapeData)
    (tail : List Γ') (inputValue : data.input = .cons :: tail) :
    TM2.step program (copyInputFieldCfg next data) =
      some (phaseCfg next
        { data with
          input := tail
          outputReverse := .cons :: data.outputReverse }) := by
  rcases data with
    ⟨input, outputReverse, output, fresh, roots, first, second, scratch⟩
  change input = .cons :: tail at inputValue
  subst input
  simp [TM2.step, program, copyInputFieldCfg, phaseCfg, tapes,
    Function.update]

theorem step_readField_symbol (source : FieldSource)
    (target : AtomSource) (next : Phase) (data : TapeData)
    (symbol : Γ') (tail : List Γ') (notDelimiter : symbol ≠ .cons)
    (sourceValue : data.field source = symbol :: tail) :
    TM2.step program (readFieldCfg source target next data) =
      some (readFieldCfg source target next
        (readFieldSymbolData data source symbol tail)) := by
  rcases data with
    ⟨input, outputReverse, output, fresh, roots, first, second, scratch⟩
  cases source <;> cases target <;>
    simp [TapeData.field] at sourceValue <;>
    cases symbol <;>
    simp_all [TM2.step, program, readFieldCfg, readFieldSymbolData,
      tapes, TapeData.setField, FieldSource.stack, Function.update]
  all_goals
    funext stack
    cases stack <;> simp [tapes, Function.update]

theorem step_readField_delimiter (source : FieldSource)
    (target : AtomSource) (next : Phase) (data : TapeData)
    (tail : List Γ') (sourceValue : data.field source = .cons :: tail) :
    TM2.step program (readFieldCfg source target next data) =
      some (restoreCfg target next (data.setField source tail)) := by
  rcases data with
    ⟨input, outputReverse, output, fresh, roots, first, second, scratch⟩
  cases source <;> cases target <;>
    simp [TapeData.field] at sourceValue <;>
    simp [TM2.step, program, readFieldCfg, restoreCfg, tapes,
      TapeData.setField, FieldSource.stack, AtomSource.stack, sourceValue,
      Function.update]
  all_goals
    funext stack
    cases stack <;> simp [tapes, Function.update]

def preparedFreshRootData (data : TapeData) : TapeData :=
  { data with roots := .cons :: data.roots }

def savedFreshSymbolData (data : TapeData) (symbol : Γ')
    (tail : List Γ') : TapeData :=
  { data with
    fresh := tail
    scratch := symbol :: data.scratch }

def restoredFreshRootSymbolData (data : TapeData) (symbol : Γ')
    (tail : List Γ') : TapeData :=
  { data with
    fresh := symbol :: data.fresh
    roots := symbol :: data.roots
    scratch := tail }

theorem step_prepareFreshRoot (next : Phase) (data : TapeData) :
    TM2.step program (prepareFreshRootCfg next data) =
      some (saveFreshRootCfg next (preparedFreshRootData data)) := by
  simp [TM2.step, program, prepareFreshRootCfg, saveFreshRootCfg,
    preparedFreshRootData, tapes, Function.update]
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_saveFreshRoot_cons (next : Phase) (data : TapeData)
    (symbol : Γ') (tail : List Γ')
    (freshValue : data.fresh = symbol :: tail) :
    TM2.step program (saveFreshRootCfg next data) =
      some (saveFreshRootCfg next
        (savedFreshSymbolData data symbol tail)) := by
  rcases data with
    ⟨input, outputReverse, output, fresh, roots, first, second, scratch⟩
  change fresh = symbol :: tail at freshValue
  subst fresh
  simp [TM2.step, program, saveFreshRootCfg, savedFreshSymbolData,
    tapes, Function.update]
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_saveFreshRoot_nil (next : Phase) (data : TapeData)
    (freshValue : data.fresh = []) :
    TM2.step program (saveFreshRootCfg next data) =
      some (restoreFreshRootCfg next data) := by
  rcases data with
    ⟨input, outputReverse, output, fresh, roots, first, second, scratch⟩
  change fresh = [] at freshValue
  subst fresh
  simp [TM2.step, program, saveFreshRootCfg, restoreFreshRootCfg,
    tapes, Function.update]

theorem step_restoreFreshRoot_cons (next : Phase) (data : TapeData)
    (symbol : Γ') (tail : List Γ')
    (scratchValue : data.scratch = symbol :: tail) :
    TM2.step program (restoreFreshRootCfg next data) =
      some (restoreFreshRootCfg next
        (restoredFreshRootSymbolData data symbol tail)) := by
  rcases data with
    ⟨input, outputReverse, output, fresh, roots, first, second, scratch⟩
  change scratch = symbol :: tail at scratchValue
  subst scratch
  simp [TM2.step, program, restoreFreshRootCfg,
    restoredFreshRootSymbolData, tapes, Function.update]
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_restoreFreshRoot_nil (next : Phase) (data : TapeData)
    (scratchValue : data.scratch = []) :
    TM2.step program (restoreFreshRootCfg next data) =
      some (phaseCfg next data) := by
  rcases data with
    ⟨input, outputReverse, output, fresh, roots, first, second, scratch⟩
  change scratch = [] at scratchValue
  subst scratch
  simp [TM2.step, program, restoreFreshRootCfg, phaseCfg, tapes,
    Function.update]

theorem step_clearAtom_cons (source : AtomSource) (next : Phase)
    (data : TapeData) (symbol : Γ') (tail : List Γ')
    (sourceValue : data.atom source = symbol :: tail) :
    TM2.step program (clearAtomCfg source next data) =
      some (clearAtomCfg source next (data.setAtom source tail)) := by
  rcases data with
    ⟨input, outputReverse, output, fresh, roots, first, second, scratch⟩
  cases source <;>
    simp [TapeData.atom] at sourceValue <;>
    simp [TM2.step, program, clearAtomCfg, tapes, TapeData.setAtom,
      AtomSource.stack, sourceValue, Function.update]
  all_goals
    funext stack
    cases stack <;> simp [tapes, Function.update]

theorem step_clearAtom_nil (source : AtomSource) (next : Phase)
    (data : TapeData) (sourceValue : data.atom source = []) :
    TM2.step program (clearAtomCfg source next data) =
      some (phaseCfg next data) := by
  rcases data with
    ⟨input, outputReverse, output, fresh, roots, first, second, scratch⟩
  cases source <;>
    simp [TapeData.atom] at sourceValue <;>
    simp [TM2.step, program, clearAtomCfg, phaseCfg, tapes,
      AtomSource.stack, sourceValue, Function.update]

def reversedOutputSymbolData (data : TapeData) (symbol : Γ')
    (tail : List Γ') : TapeData :=
  { data with
    outputReverse := tail
    output := symbol :: data.output }

theorem step_reverseOutput_cons (data : TapeData) (symbol : Γ')
    (tail : List Γ')
    (reverseValue : data.outputReverse = symbol :: tail) :
    TM2.step program (reverseOutputCfg data) =
      some (reverseOutputCfg
        (reversedOutputSymbolData data symbol tail)) := by
  rcases data with
    ⟨input, outputReverse, output, fresh, roots, first, second, scratch⟩
  change outputReverse = symbol :: tail at reverseValue
  subst outputReverse
  simp [TM2.step, program, reverseOutputCfg, reversedOutputSymbolData,
    tapes, Function.update]
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_reverseOutput_nil (data : TapeData)
    (reverseValue : data.outputReverse = []) :
    TM2.step program (reverseOutputCfg data) =
      some (phaseCfg .done data) := by
  rcases data with
    ⟨input, outputReverse, output, fresh, roots, first, second, scratch⟩
  change outputReverse = [] at reverseValue
  subst outputReverse
  simp [TM2.step, program, reverseOutputCfg, phaseCfg, tapes,
    Function.update]

/-- Copy one delimiter-terminated field directly from the request stream into
the reverse-output accumulator. -/
def copyInputField_to_phase (next : Phase) (data : TapeData)
    (word rest : List Γ')
    (noDelimiter : ∀ symbol ∈ word, symbol ≠ Γ'.cons)
    (inputValue : data.input = word ++ .cons :: rest) :
    EvalsToInTime (TM2.step program)
      (copyInputFieldCfg next data)
      (some (phaseCfg next
        { data with
          input := rest
          outputReverse :=
            (word ++ [Γ'.cons]).reverse ++ data.outputReverse }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_copyInputField_delimiter next data rest (by
          simpa using inputValue))
      simpa using step
  | cons symbol word induction =>
      have symbolNotDelimiter : symbol ≠ Γ'.cons :=
        noDelimiter symbol (by simp)
      have tailNoDelimiter : ∀ item ∈ word, item ≠ Γ'.cons := by
        intro item membership
        exact noDelimiter item (by simp [membership])
      let nextData := copiedInputSymbolData data symbol
        (word ++ .cons :: rest)
      have first := oneStep
        (step_copyInputField_symbol next data symbol
          (word ++ .cons :: rest) symbolNotDelimiter (by
            simpa using inputValue))
      have tailInput : nextData.input = word ++ .cons :: rest := by
        simp [nextData, copiedInputSymbolData]
      have remaining := induction nextData tailNoDelimiter tailInput
      have finalData :
          { nextData with
            input := rest
            outputReverse :=
              (word ++ [Γ'.cons]).reverse ++
                nextData.outputReverse } =
          { data with
            input := rest
            outputReverse :=
              ((symbol :: word) ++ [Γ'.cons]).reverse ++
                data.outputReverse } := by
        rcases data with
          ⟨input, outputReverse, output, fresh, roots, firstRoot,
            secondRoot, scratch⟩
        simp [nextData, copiedInputSymbolData, List.reverse_cons,
          List.append_assoc]
      rw [finalData] at remaining
      have composed := thenRun first remaining
      convert composed using 1 <;> simp

def readFieldScanData (data : TapeData) (source : FieldSource)
    (word rest : List Γ') : TapeData :=
  { data.setField source rest with
    scratch := word.reverse ++ data.scratch }

/-- Scan one delimiter-terminated field into scratch, leaving the source at
the following field. -/
def readField_to_restore (source : FieldSource) (target : AtomSource)
    (next : Phase) (data : TapeData) (word rest : List Γ')
    (noDelimiter : ∀ symbol ∈ word, symbol ≠ Γ'.cons)
    (sourceValue : data.field source = word ++ .cons :: rest) :
    EvalsToInTime (TM2.step program)
      (readFieldCfg source target next data)
      (some (restoreCfg target next
        (readFieldScanData data source word rest)))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_readField_delimiter source target next data rest (by
          simpa using sourceValue))
      convert step using 1
      · rcases data with
          ⟨input, outputReverse, output, fresh, roots, firstRoot,
            secondRoot, scratch⟩
        cases source <;>
          simp [readFieldScanData, TapeData.setField]
      · simp
  | cons symbol word induction =>
      have symbolNotDelimiter : symbol ≠ Γ'.cons :=
        noDelimiter symbol (by simp)
      have tailNoDelimiter : ∀ item ∈ word, item ≠ Γ'.cons := by
        intro item membership
        exact noDelimiter item (by simp [membership])
      let nextData := readFieldSymbolData data source symbol
        (word ++ .cons :: rest)
      have first := oneStep
        (step_readField_symbol source target next data symbol
          (word ++ .cons :: rest) symbolNotDelimiter (by
            simpa using sourceValue))
      have tailSource :
          nextData.field source = word ++ .cons :: rest := by
        rcases data with
          ⟨input, outputReverse, output, fresh, roots, firstRoot,
            secondRoot, scratch⟩
        cases source <;>
          rfl
      have remaining := induction nextData tailNoDelimiter tailSource
      have finalData :
          readFieldScanData nextData source word rest =
            readFieldScanData data source (symbol :: word) rest := by
        rcases data with
          ⟨input, outputReverse, output, fresh, roots, firstRoot,
            secondRoot, scratch⟩
        cases source <;>
          simp [nextData, readFieldSymbolData, readFieldScanData,
            TapeData.setField, List.reverse_cons, List.append_assoc]
      rw [finalData] at remaining
      have composed := thenRun first remaining
      convert composed using 1 <;> simp

def saveFreshRootScanData (data : TapeData) (word : List Γ') : TapeData :=
  { data with
    fresh := []
    scratch := word.reverse ++ data.scratch }

def saveFreshRoot_to_restore (next : Phase) (data : TapeData)
    (word : List Γ') (freshValue : data.fresh = word) :
    EvalsToInTime (TM2.step program)
      (saveFreshRootCfg next data)
      (some (restoreFreshRootCfg next
        (saveFreshRootScanData data word)))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep (step_saveFreshRoot_nil next data freshValue)
      convert step using 1
      · rcases data with
          ⟨input, outputReverse, output, fresh, roots, firstRoot,
            secondRoot, scratch⟩
        change fresh = [] at freshValue
        subst fresh
        rfl
      · simp
  | cons symbol word induction =>
      let nextData := savedFreshSymbolData data symbol word
      have first := oneStep
        (step_saveFreshRoot_cons next data symbol word freshValue)
      have remaining := induction nextData (by
        simp [nextData, savedFreshSymbolData])
      have finalData :
          saveFreshRootScanData nextData word =
            saveFreshRootScanData data (symbol :: word) := by
        rcases data with
          ⟨input, outputReverse, output, fresh, roots, firstRoot,
            secondRoot, scratch⟩
        simp [nextData, savedFreshSymbolData, saveFreshRootScanData,
          List.reverse_cons, List.append_assoc]
      rw [finalData] at remaining
      have composed := thenRun first remaining
      convert composed using 1 <;> simp

def restoredFreshRootData (data : TapeData) (word : List Γ') : TapeData :=
  { data with
    fresh := word.reverse ++ data.fresh
    roots := word.reverse ++ data.roots
    scratch := [] }

def restoreFreshRoot_to_phase (next : Phase) (data : TapeData)
    (word : List Γ') (scratchValue : data.scratch = word) :
    EvalsToInTime (TM2.step program)
      (restoreFreshRootCfg next data)
      (some (phaseCfg next (restoredFreshRootData data word)))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_restoreFreshRoot_nil next data scratchValue)
      convert step using 1
      · rcases data with
          ⟨input, outputReverse, output, fresh, roots, firstRoot,
            secondRoot, scratch⟩
        change scratch = [] at scratchValue
        subst scratch
        rfl
      · simp
  | cons symbol word induction =>
      let nextData := restoredFreshRootSymbolData data symbol word
      have first := oneStep
        (step_restoreFreshRoot_cons next data symbol word scratchValue)
      have remaining := induction nextData (by
        simp [nextData, restoredFreshRootSymbolData])
      have finalData :
          restoredFreshRootData nextData word =
            restoredFreshRootData data (symbol :: word) := by
        rcases data with
          ⟨input, outputReverse, output, fresh, roots, firstRoot,
            secondRoot, scratch⟩
        simp [nextData, restoredFreshRootSymbolData,
          restoredFreshRootData, List.reverse_cons, List.append_assoc]
      rw [finalData] at remaining
      have composed := thenRun first remaining
      convert composed using 1 <;> simp

/-- Push the current fresh atom as one delimiter-terminated root field while
restoring the fresh register and clearing scratch. -/
def pushFreshRoot_to_phase (next : Phase) (data : TapeData)
    (word : List Γ') (freshValue : data.fresh = word)
    (scratchValue : data.scratch = []) :
    EvalsToInTime (TM2.step program)
      (prepareFreshRootCfg next data)
      (some (phaseCfg next
        { data with roots := word ++ .cons :: data.roots }))
      (2 * word.length + 3) := by
  let prepared := preparedFreshRootData data
  have first : EvalsToInTime (TM2.step program)
      (prepareFreshRootCfg next data)
      (some (saveFreshRootCfg next prepared)) 1 := by
    simpa [prepared] using oneStep (step_prepareFreshRoot next data)
  have saved := saveFreshRoot_to_restore next prepared word (by
    simpa [prepared, preparedFreshRootData] using freshValue)
  have restored := restoreFreshRoot_to_phase next
    (saveFreshRootScanData prepared word) word.reverse (by
      simp [saveFreshRootScanData, prepared, preparedFreshRootData,
        scratchValue])
  have finalData :
      restoredFreshRootData (saveFreshRootScanData prepared word)
          word.reverse =
        { data with roots := word ++ .cons :: data.roots } := by
    rcases data with
      ⟨input, outputReverse, output, fresh, roots, firstRoot,
        secondRoot, scratch⟩
    change fresh = word at freshValue
    change scratch = [] at scratchValue
    subst fresh
    subst scratch
    simp [prepared, preparedFreshRootData, saveFreshRootScanData,
      restoredFreshRootData, List.append_assoc]
  rw [finalData] at restored
  have composed := thenRun (thenRun first saved) restored
  convert composed using 1 <;> simp <;> omega

/-- Discard one complete atom register and reach its continuation. -/
def clearAtom_to_phase (source : AtomSource) (next : Phase)
    (data : TapeData) (word : List Γ')
    (sourceValue : data.atom source = word) :
    EvalsToInTime (TM2.step program)
      (clearAtomCfg source next data)
      (some (phaseCfg next (data.setAtom source [])))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep (step_clearAtom_nil source next data sourceValue)
      have cleared : data.setAtom source [] = data := by
        rw [← sourceValue]
        exact TapeData.setAtom_atom data source
      rw [cleared]
      exact step
  | cons symbol word induction =>
      have first := oneStep
        (step_clearAtom_cons source next data symbol word sourceValue)
      have remaining := induction (data.setAtom source word) (by simp)
      have composed := thenRun first remaining
      have collapsed :
          (data.setAtom source word).setAtom source [] =
            data.setAtom source [] := by
        rcases data with
          ⟨input, outputReverse, output, fresh, roots, firstRoot,
            secondRoot, scratch⟩
        cases source <;> rfl
      rw [collapsed] at composed
      simpa using composed

/-- Reverse the completed accumulator onto the designated output stack. -/
def reverseOutput_to_done (data : TapeData) (word : List Γ')
    (reverseValue : data.outputReverse = word) :
    EvalsToInTime (TM2.step program)
      (reverseOutputCfg data)
      (some (phaseCfg .done
        { data with
          outputReverse := []
          output := word.reverse ++ data.output }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep (step_reverseOutput_nil data reverseValue)
      have finalData :
          { data with
            outputReverse := []
            output := data.output } = data := by
        rcases data with
          ⟨input, outputReverse, output, fresh, roots, firstRoot,
            secondRoot, scratch⟩
        change outputReverse = [] at reverseValue
        subst outputReverse
        rfl
      simpa [finalData] using step
  | cons symbol word induction =>
      let nextData := reversedOutputSymbolData data symbol word
      have first := oneStep
        (step_reverseOutput_cons data symbol word reverseValue)
      have remaining := induction nextData (by
        simp [nextData, reversedOutputSymbolData])
      have finalData :
          { nextData with
            outputReverse := []
            output := word.reverse ++ nextData.output } =
          { data with
            outputReverse := []
            output := (symbol :: word).reverse ++ data.output } := by
        rcases data with
          ⟨input, outputReverse, output, fresh, roots, firstRoot,
            secondRoot, scratch⟩
        simp [nextData, reversedOutputSymbolData, List.reverse_cons,
          List.append_assoc]
      rw [finalData] at remaining
      have composed := thenRun first remaining
      convert composed using 1 <;> simp

/-- Little-endian binary successor on native words.  The evaluator only calls
this function on canonical `trNat` words. -/
theorem trPosNum_noDelimiter (number : PosNum) :
    ∀ symbol ∈ trPosNum number, symbol ≠ Γ'.cons := by
  induction number with
  | one => simp [trPosNum]
  | bit0 number induction =>
      intro symbol membership
      simp only [trPosNum, List.mem_cons] at membership
      rcases membership with rfl | membership
      · decide
      · exact induction symbol membership
  | bit1 number induction =>
      intro symbol membership
      simp only [trPosNum, List.mem_cons] at membership
      rcases membership with rfl | membership
      · decide
      · exact induction symbol membership

theorem trNat_noDelimiter (number : Nat) :
    ∀ symbol ∈ trNat number, symbol ≠ Γ'.cons := by
  unfold trNat
  cases encoded : (number : Num) with
  | zero => simp [trNum]
  | pos positive =>
      simpa [trNum] using trPosNum_noDelimiter positive

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

/-- Read one complete native field from either input or the root stack into an
empty atom register, restoring its original bit order. -/
def readField_to_phase (source : FieldSource) (target : AtomSource)
    (next : Phase) (data : TapeData) (word rest : List Γ')
    (noDelimiter : ∀ symbol ∈ word, symbol ≠ Γ'.cons)
    (sourceValue : data.field source = word ++ .cons :: rest)
    (targetValue : data.atom target = [])
    (scratchValue : data.scratch = []) :
    EvalsToInTime (TM2.step program)
      (readFieldCfg source target next data)
      (some (phaseCfg next
        { (data.setField source rest).setAtom target word with
          scratch := [] }))
      (2 * word.length + 2) := by
  have scanned := readField_to_restore source target next data word rest
    noDelimiter sourceValue
  have restored := restoreAtom_to_phase target next
    (readFieldScanData data source word rest) word.reverse (by
      simp [readFieldScanData, scratchValue])
  have finalData :
      restoredAtomData (readFieldScanData data source word rest)
          target word.reverse =
        { (data.setField source rest).setAtom target word with
          scratch := [] } := by
    rcases data with
      ⟨input, outputReverse, output, fresh, roots, firstRoot,
        secondRoot, scratch⟩
    cases source <;> cases target <;>
      simp [TapeData.field, TapeData.atom] at sourceValue targetValue <;>
      simp at scratchValue <;>
      simp [readFieldScanData, restoredAtomData, TapeData.setField,
        TapeData.setAtom, TapeData.atom, targetValue, scratchValue]
  rw [finalData] at restored
  have composed := thenRun scanned restored
  convert composed using 1 <;> simp <;> omega

/-- Native specialization of direct input-field copying. -/
def copyInputField_trNat (next : Phase) (data : TapeData)
    (atom : Nat) (rest : List Γ')
    (inputValue : data.input = trList [atom] ++ rest) :
    EvalsToInTime (TM2.step program)
      (copyInputFieldCfg next data)
      (some (phaseCfg next
        { data with
          input := rest
          outputReverse :=
            (trList [atom]).reverse ++ data.outputReverse }))
      ((trNat atom).length + 1) := by
  simpa [trList] using
    copyInputField_to_phase next data (trNat atom) rest
      (trNat_noDelimiter atom) (by simpa [trList] using inputValue)

/-- Native specialization of field decoding into an atom register. -/
def readField_trNat (source : FieldSource) (target : AtomSource)
    (next : Phase) (data : TapeData) (atom : Nat) (rest : List Γ')
    (sourceValue : data.field source = trList [atom] ++ rest)
    (targetValue : data.atom target = [])
    (scratchValue : data.scratch = []) :
    EvalsToInTime (TM2.step program)
      (readFieldCfg source target next data)
      (some (phaseCfg next
        { (data.setField source rest).setAtom target (trNat atom) with
          scratch := [] }))
      (2 * (trNat atom).length + 2) := by
  simpa [trList] using
    readField_to_phase source target next data (trNat atom) rest
      (trNat_noDelimiter atom) (by simpa [trList] using sourceValue)
      targetValue scratchValue

/-- Native specialization of pushing the fresh atom onto the root stack. -/
def pushFreshRoot_trNat (next : Phase) (data : TapeData) (atom : Nat)
    (freshValue : data.fresh = trNat atom)
    (scratchValue : data.scratch = []) :
    EvalsToInTime (TM2.step program)
      (prepareFreshRootCfg next data)
      (some (phaseCfg next
        { data with roots := trList [atom] ++ data.roots }))
      (2 * (trNat atom).length + 3) := by
  simpa [trList] using
    pushFreshRoot_to_phase next data (trNat atom)
      freshValue scratchValue

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

/-- Complete the common post-gate protocol: clear both operand registers,
push the emitted gate's fresh atom onto the root stack, increment the fresh
counter, and return to the instruction decoder. -/
def finishGate (data : TapeData) (fresh : Nat)
    (firstWord secondWord : List Γ')
    (freshValue : data.fresh = trNat fresh)
    (firstValue : data.first = firstWord)
    (secondValue : data.second = secondWord)
    (scratchValue : data.scratch = []) :
    EvalsToInTime (TM2.step program)
      (phaseCfg .gateDone data)
      (some (phaseCfg .decodeNext
        { data with
          fresh := trNat fresh.succ
          roots := trList [fresh] ++ data.roots
          first := []
          second := [] }))
      (firstWord.length + secondWord.length +
        4 * (trNat fresh).length + 12) := by
  let d₁ := data.setAtom .first []
  let d₂ := d₁.setAtom .second []
  let d₃ := { d₂ with roots := trList [fresh] ++ d₂.roots }
  let d₄ := { d₃ with fresh := trNat fresh.succ }
  have h₁ := oneStep (step_phase_gateDone data)
  have h₂ : EvalsToInTime (TM2.step program)
      (clearAtomCfg .first .afterClearFirst data)
      (some (phaseCfg .afterClearFirst d₁))
      (firstWord.length + 1) := by
    simpa [d₁] using
      clearAtom_to_phase .first .afterClearFirst data firstWord firstValue
  have h₃ := oneStep (step_phase_afterClearFirst d₁)
  have h₄ : EvalsToInTime (TM2.step program)
      (clearAtomCfg .second .afterClearSecond d₁)
      (some (phaseCfg .afterClearSecond d₂))
      (secondWord.length + 1) := by
    simpa [d₂, d₁, TapeData.setAtom, TapeData.atom] using
      clearAtom_to_phase .second .afterClearSecond d₁ secondWord (by
        simpa [d₁, TapeData.setAtom, TapeData.atom] using secondValue)
  have h₅ := oneStep (step_phase_afterClearSecond d₂)
  have h₆ : EvalsToInTime (TM2.step program)
      (prepareFreshRootCfg .afterPushRoot d₂)
      (some (phaseCfg .afterPushRoot d₃))
      (2 * (trNat fresh).length + 3) := by
    simpa [d₃, d₂, d₁, TapeData.setAtom] using
      pushFreshRoot_trNat .afterPushRoot d₂ fresh
        (by simpa [d₂, d₁, TapeData.setAtom] using freshValue)
        (by simpa [d₂, d₁, TapeData.setAtom] using scratchValue)
  have h₇ := oneStep (step_phase_afterPushRoot d₃)
  have h₈ : EvalsToInTime (TM2.step program)
      (incrementCfg .decodeNext d₃)
      (some (phaseCfg .decodeNext d₄))
      (2 * (trNat fresh).length + 3) := by
    simpa [d₄, d₃, d₂, d₁, TapeData.setAtom] using
      incrementFresh_trNat .decodeNext d₃ fresh
        (by simpa [d₃, d₂, d₁, TapeData.setAtom] using freshValue)
        (by simpa [d₃, d₂, d₁, TapeData.setAtom] using scratchValue)
  have composed :=
    thenRun (thenRun (thenRun (thenRun (thenRun (thenRun (thenRun h₁ h₂) h₃) h₄) h₅) h₆) h₇) h₈
  have finalData :
      d₄ =
        { data with
          fresh := trNat fresh.succ
          roots := trList [fresh] ++ data.roots
          first := []
          second := [] } := by
    rcases data with
      ⟨input, outputReverse, output, freshWord, roots, first, second,
        scratch⟩
    simp [d₄, d₃, d₂, d₁, TapeData.setAtom]
  rw [finalData] at composed
  convert composed using 1 <;> omega

/-- Execute one complete constant instruction from one decoder boundary to
the next. -/
def executeConstantInstruction (value : Bool) (data : TapeData)
    (fresh : Nat) (rest : List Γ')
    (inputValue :
      data.input = trList (TransitionInstruction.fields (.constant value)) ++
        rest)
    (freshValue : data.fresh = trNat fresh)
    (firstValue : data.first = [])
    (secondValue : data.second = [])
    (scratchValue : data.scratch = []) :
    EvalsToInTime (TM2.step program)
      (phaseCfg .decodeNext data)
      (some (phaseCfg .decodeNext
        { data with
          input := rest
          outputReverse :=
            (trList (constantGateFields fresh value)).reverse ++
              data.outputReverse
          fresh := trNat fresh.succ
          roots := trList [fresh] ++ data.roots
          first := []
          second := [] }))
      (constantTagTime value + 6 * (trNat fresh).length + 17) := by
  let d₁ := { data with input := rest }
  let d₂ :=
    { d₁ with
      outputReverse :=
        (trList (constantGateFields fresh value)).reverse ++
          d₁.outputReverse }
  have h₀ := oneStep (step_phase_decodeNext data)
  have h₁ : EvalsToInTime (TM2.step program)
      (controlCfg .decodeTag data)
      (some (phaseCfg (.constantStart value) d₁))
      (constantTagTime value) := by
    simpa [d₁] using decodeConstantTag value data rest inputValue
  have h₂ : EvalsToInTime (TM2.step program)
      (phaseCfg (.constantStart value) d₁)
      (some (phaseCfg .gateDone d₂))
      (2 * (trNat fresh).length + 4) := by
    simpa [d₂] using emitConstantGate d₁ fresh value
      (by simpa [d₁] using freshValue)
      (by simpa [d₁] using scratchValue)
  have h₃ := finishGate d₂ fresh [] []
    (by simpa [d₂, d₁] using freshValue)
    (by simpa [d₂, d₁] using firstValue)
    (by simpa [d₂, d₁] using secondValue)
    (by simpa [d₂, d₁] using scratchValue)
  have composed := thenRun (thenRun (thenRun h₀ h₁) h₂) h₃
  convert composed using 1 <;> simp [d₂, d₁] <;> omega

def wireUnaryKind : TransitionSlice → UnaryGateKind
  | .current => .equalityCurrent
  | .next => .equalityNext

@[simp]
theorem unaryGateFields_wireUnaryKind (wire : TransitionWire)
    (fresh : Nat) :
    unaryGateFields (wireUnaryKind wire.slice) fresh wire.atom =
      equalityGateFields fresh wire := by
  rcases wire with ⟨slice, atom⟩
  cases slice <;> rfl

/-- Execute one complete source-wire instruction, including reading its
variable-width atom payload from the instruction stream. -/
def executeWireInstruction (wire : TransitionWire) (data : TapeData)
    (fresh : Nat) (rest : List Γ')
    (inputValue :
      data.input = trList (TransitionInstruction.fields (.wire wire)) ++
        rest)
    (freshValue : data.fresh = trNat fresh)
    (firstValue : data.first = [])
    (secondValue : data.second = [])
    (scratchValue : data.scratch = []) :
    EvalsToInTime (TM2.step program)
      (phaseCfg .decodeNext data)
      (some (phaseCfg .decodeNext
        { data with
          input := rest
          outputReverse :=
            (trList (equalityGateFields fresh wire)).reverse ++
              data.outputReverse
          fresh := trNat fresh.succ
          roots := trList [fresh] ++ data.roots
          first := []
          second := [] }))
      (wireTagTime wire.slice + 8 * (trNat fresh).length +
        7 * (trNat wire.atom).length + 28) := by
  let kind := wireUnaryKind wire.slice
  let d₁ := { data with input := trList [wire.atom] ++ rest }
  let d₂ :=
    { (d₁.setField .input rest).setAtom .first (trNat wire.atom) with
      scratch := [] }
  let d₃ :=
    { d₂ with
      outputReverse :=
        (trList (equalityGateFields fresh wire)).reverse ++
          d₂.outputReverse }
  have h₀ := oneStep (step_phase_decodeNext data)
  have h₁ : EvalsToInTime (TM2.step program)
      (controlCfg .decodeTag data)
      (some (readFieldCfg .input .first (.unaryStart kind) d₁))
      (wireTagTime wire.slice) := by
    simpa [kind, wireUnaryKind, d₁] using
      decodeWireTag wire data rest inputValue
  have h₂ : EvalsToInTime (TM2.step program)
      (readFieldCfg .input .first (.unaryStart kind) d₁)
      (some (phaseCfg (.unaryStart kind) d₂))
      (2 * (trNat wire.atom).length + 2) := by
    simpa [d₂] using
      readField_trNat .input .first (.unaryStart kind) d₁ wire.atom rest
        (by simp [d₁, TapeData.field, trList])
        (by simpa [d₁, TapeData.atom] using firstValue)
        (by simpa [d₁] using scratchValue)
  have h₃ : EvalsToInTime (TM2.step program)
      (phaseCfg (.unaryStart kind) d₂)
      (some (phaseCfg .gateDone d₃))
      (4 * (trNat fresh).length +
        4 * (trNat wire.atom).length + 13) := by
    have emitted := emitUnaryGate kind d₂ fresh wire.atom
      (by simpa [d₂, d₁, TapeData.setField, TapeData.setAtom,
        TapeData.atom] using freshValue)
      (by simp [d₂, d₁, TapeData.setField, TapeData.setAtom])
      (by simp [d₂])
    have gateEq :
        unaryGateFields kind fresh wire.atom =
          equalityGateFields fresh wire := by
      simpa [kind] using unaryGateFields_wireUnaryKind wire fresh
    rw [gateEq] at emitted
    simpa [d₃] using emitted
  have h₄ := finishGate d₃ fresh (trNat wire.atom) []
    (by simpa [d₃, d₂, d₁, TapeData.setField, TapeData.setAtom,
      TapeData.atom] using freshValue)
    (by simp [d₃, d₂, d₁, TapeData.setField, TapeData.setAtom])
    (by simpa [d₃, d₂, d₁, TapeData.setField, TapeData.setAtom,
      TapeData.atom] using secondValue)
    (by simp [d₃, d₂])
  have composed := thenRun (thenRun (thenRun (thenRun h₀ h₁) h₂) h₃) h₄
  convert composed using 1 <;>
    simp [d₃, d₂, d₁, kind, TapeData.setField, TapeData.setAtom,
      TapeData.atom, scratchValue, Nat.add_comm] <;>
    ring

/-- Execute one complete negation instruction, popping its unique operand
root and replacing it by the fresh output root. -/
def executeNegateInstruction (data : TapeData) (fresh input : Nat)
    (remainingRoots : List Γ') (rest : List Γ')
    (inputValue :
      data.input = trList (TransitionInstruction.fields .negate) ++ rest)
    (freshValue : data.fresh = trNat fresh)
    (rootsValue : data.roots = trList [input] ++ remainingRoots)
    (firstValue : data.first = [])
    (secondValue : data.second = [])
    (scratchValue : data.scratch = []) :
    EvalsToInTime (TM2.step program)
      (phaseCfg .decodeNext data)
      (some (phaseCfg .decodeNext
        { data with
          input := rest
          outputReverse :=
            (trList (notGateFields fresh (gateOutput input))).reverse ++
              data.outputReverse
          fresh := trNat fresh.succ
          roots := trList [fresh] ++ remainingRoots
          first := []
          second := [] }))
      (8 * (trNat fresh).length + 7 * (trNat input).length + 31) := by
  let d₁ := { data with input := rest }
  let d₂ :=
    { (d₁.setField .roots remainingRoots).setAtom .first (trNat input) with
      scratch := [] }
  let d₃ :=
    { d₂ with
      outputReverse :=
        (trList (notGateFields fresh (gateOutput input))).reverse ++
          d₂.outputReverse }
  have h₀ := oneStep (step_phase_decodeNext data)
  have h₁ : EvalsToInTime (TM2.step program)
      (controlCfg .decodeTag data)
      (some (readFieldCfg .roots .first (.unaryStart .negation) d₁)) 3 := by
    simpa [d₁] using decodeNegateTag data rest inputValue
  have h₂ : EvalsToInTime (TM2.step program)
      (readFieldCfg .roots .first (.unaryStart .negation) d₁)
      (some (phaseCfg (.unaryStart .negation) d₂))
      (2 * (trNat input).length + 2) := by
    simpa [d₂] using
      readField_trNat .roots .first (.unaryStart .negation) d₁ input
        remainingRoots
        (by simpa [d₁, TapeData.field] using rootsValue)
        (by simpa [d₁, TapeData.atom] using firstValue)
        (by simpa [d₁] using scratchValue)
  have h₃ : EvalsToInTime (TM2.step program)
      (phaseCfg (.unaryStart .negation) d₂)
      (some (phaseCfg .gateDone d₃))
      (4 * (trNat fresh).length + 4 * (trNat input).length + 13) := by
    simpa [d₃, unaryGateFields] using
      emitUnaryGate .negation d₂ fresh input
        (by simpa [d₂, d₁, TapeData.setField, TapeData.setAtom,
          TapeData.atom] using freshValue)
        (by simp [d₂, d₁, TapeData.setField, TapeData.setAtom])
        (by simp [d₂])
  have h₄ := finishGate d₃ fresh (trNat input) []
    (by simpa [d₃, d₂, d₁, TapeData.setField, TapeData.setAtom,
      TapeData.atom] using freshValue)
    (by simp [d₃, d₂, d₁, TapeData.setField, TapeData.setAtom])
    (by simpa [d₃, d₂, d₁, TapeData.setField, TapeData.setAtom,
      TapeData.atom] using secondValue)
    (by simp [d₃, d₂])
  have composed := thenRun (thenRun (thenRun (thenRun h₀ h₁) h₂) h₃) h₄
  convert composed using 1 <;>
    simp [d₃, d₂, d₁, TapeData.setField, TapeData.setAtom,
      TapeData.atom, scratchValue, Nat.add_comm] <;>
    ring

def binaryInstruction : BinaryGateKind → TransitionInstruction
  | .conjunction => .conjoin
  | .disjunction => .disjoin

/-- Execute one complete binary instruction, popping its right operand and
then its left operand before replacing both by the fresh output root. -/
def executeBinaryInstruction (kind : BinaryGateKind) (data : TapeData)
    (fresh first second : Nat) (remainingRoots rest : List Γ')
    (inputValue :
      data.input = trList (TransitionInstruction.fields
        (binaryInstruction kind)) ++ rest)
    (freshValue : data.fresh = trNat fresh)
    (rootsValue :
      data.roots = trList [second, first] ++ remainingRoots)
    (firstValue : data.first = [])
    (secondValue : data.second = [])
    (scratchValue : data.scratch = []) :
    EvalsToInTime (TM2.step program)
      (phaseCfg .decodeNext data)
      (some (phaseCfg .decodeNext
        { data with
          input := rest
          outputReverse :=
            (trList (binaryGateFields kind fresh first second)).reverse ++
              data.outputReverse
          fresh := trNat fresh.succ
          roots := trList [fresh] ++ remainingRoots
          first := []
          second := [] }))
      (binaryTagTime kind + 10 * (trNat fresh).length +
        7 * (trNat first).length + 7 * (trNat second).length + 40) := by
  let d₁ := { data with input := rest }
  let d₂ :=
    { (d₁.setField .roots
        (trList [first] ++ remainingRoots)).setAtom .second
          (trNat second) with
      scratch := [] }
  let d₃ :=
    { (d₂.setField .roots remainingRoots).setAtom .first (trNat first) with
      scratch := [] }
  let d₄ :=
    { d₃ with
      outputReverse :=
        (trList (binaryGateFields kind fresh first second)).reverse ++
          d₃.outputReverse }
  have h₀ := oneStep (step_phase_decodeNext data)
  have h₁ : EvalsToInTime (TM2.step program)
      (controlCfg .decodeTag data)
      (some (readFieldCfg .roots .second (.binaryReadFirst kind) d₁))
      (binaryTagTime kind) := by
    simpa [d₁, binaryInstruction] using
      decodeBinaryTag kind data rest (by
        simpa [binaryInstruction] using inputValue)
  have h₂ : EvalsToInTime (TM2.step program)
      (readFieldCfg .roots .second (.binaryReadFirst kind) d₁)
      (some (phaseCfg (.binaryReadFirst kind) d₂))
      (2 * (trNat second).length + 2) := by
    simpa [d₂] using
      readField_trNat .roots .second (.binaryReadFirst kind) d₁ second
        (trList [first] ++ remainingRoots)
        (by simpa [d₁, TapeData.field, trList, List.append_assoc]
          using rootsValue)
        (by simpa [d₁, TapeData.atom] using secondValue)
        (by simpa [d₁] using scratchValue)
  have h₃ := oneStep (step_phase_binaryReadFirst kind d₂)
  have h₄ : EvalsToInTime (TM2.step program)
      (readFieldCfg .roots .first (.binaryStart kind) d₂)
      (some (phaseCfg (.binaryStart kind) d₃))
      (2 * (trNat first).length + 2) := by
    simpa [d₃] using
      readField_trNat .roots .first (.binaryStart kind) d₂ first
        remainingRoots
        (by simp [d₂, d₁, TapeData.setField, TapeData.setAtom,
          TapeData.field])
        (by simpa [d₂, d₁, TapeData.setField, TapeData.setAtom,
          TapeData.atom] using firstValue)
        (by simp [d₂])
  have h₅ : EvalsToInTime (TM2.step program)
      (phaseCfg (.binaryStart kind) d₃)
      (some (phaseCfg .gateDone d₄))
      (6 * (trNat fresh).length + 4 * (trNat first).length +
        4 * (trNat second).length + 22) := by
    simpa [d₄] using emitBinaryGate kind d₃ fresh first second
      (by simpa [d₃, d₂, d₁, TapeData.setField, TapeData.setAtom,
        TapeData.atom] using freshValue)
      (by simp [d₃, d₂, d₁, TapeData.setField, TapeData.setAtom])
      (by simp [d₃, d₂, d₁, TapeData.setField, TapeData.setAtom])
      (by simp [d₃, d₂])
  have h₆ := finishGate d₄ fresh (trNat first) (trNat second)
    (by simpa [d₄, d₃, d₂, d₁, TapeData.setField, TapeData.setAtom,
      TapeData.atom] using freshValue)
    (by simp [d₄, d₃, d₂, d₁, TapeData.setField, TapeData.setAtom])
    (by simp [d₄, d₃, d₂, d₁, TapeData.setField, TapeData.setAtom])
    (by simp [d₄, d₃, d₂])
  have composed :=
    thenRun (thenRun (thenRun (thenRun (thenRun (thenRun h₀ h₁) h₂) h₃) h₄) h₅) h₆
  convert composed using 1 <;>
    simp [d₄, d₃, d₂, d₁, TapeData.setField, TapeData.setAtom,
      TapeData.atom, scratchValue, Nat.add_comm] <;>
    ring

@[simp]
theorem trList_append (first second : List Nat) :
    trList (first ++ second) = trList first ++ trList second := by
  induction first with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.cons_append, trList]
      rw [induction]
      simp [List.append_assoc]

/-- Exact cost obtained by recursively composing the verified instruction
scripts for an expression's postorder program. -/
def transitionExpressionTime : TransitionExpr → Nat → Nat
  | .constant value, fresh =>
      constantTagTime value + 6 * (trNat fresh).length + 17
  | .wire wire, fresh =>
      wireTagTime wire.slice + 8 * (trNat fresh).length +
        7 * (trNat wire.atom).length + 28
  | .not input, fresh =>
      let compiled := compileTransitionFields input fresh
      transitionExpressionTime input fresh +
        (8 * (trNat compiled.nextFresh).length +
          7 * (trNat compiled.root).length + 31)
  | .and first second, fresh =>
      let firstCompiled := compileTransitionFields first fresh
      let secondCompiled :=
        compileTransitionFields second firstCompiled.nextFresh
      transitionExpressionTime first fresh +
        transitionExpressionTime second firstCompiled.nextFresh +
        (binaryTagTime .conjunction +
          10 * (trNat secondCompiled.nextFresh).length +
          7 * (trNat firstCompiled.root).length +
          7 * (trNat secondCompiled.root).length + 40)
  | .or first second, fresh =>
      let firstCompiled := compileTransitionFields first fresh
      let secondCompiled :=
        compileTransitionFields second firstCompiled.nextFresh
      transitionExpressionTime first fresh +
        transitionExpressionTime second firstCompiled.nextFresh +
        (binaryTagTime .disjunction +
          10 * (trNat secondCompiled.nextFresh).length +
          7 * (trNat firstCompiled.root).length +
          7 * (trNat secondCompiled.root).length + 40)

/-- Running the compact postorder program for one expression produces exactly
the direct structural compiler's native fields and leaves its unique root on
top of the existing root stack. -/
noncomputable def executeExpressionProgram (expression : TransitionExpr)
    (data : TapeData)
    (fresh : Nat) (roots : List Nat) (rest : List Γ')
    (inputValue :
      data.input =
        trList (transitionProgramFields expression.program) ++ rest)
    (freshValue : data.fresh = trNat fresh)
    (rootsValue : data.roots = trList roots)
    (firstValue : data.first = [])
    (secondValue : data.second = [])
    (scratchValue : data.scratch = []) :
    EvalsToInTime (TM2.step program)
      (phaseCfg .decodeNext data)
      (some (phaseCfg .decodeNext
        { data with
          input := rest
          outputReverse :=
            (trList (compileTransitionFields expression fresh).fields).reverse ++
              data.outputReverse
          fresh := trNat (compileTransitionFields expression fresh).nextFresh
          roots :=
            trList ((compileTransitionFields expression fresh).root :: roots)
          first := []
          second := [] }))
      (transitionExpressionTime expression fresh) := by
  induction expression generalizing data fresh roots rest with
  | constant value =>
      simpa [transitionExpressionTime, TransitionExpr.program,
        transitionProgramFields, compileTransitionFields, trList,
        List.append_assoc, rootsValue] using
        executeConstantInstruction value data fresh rest
          (by simpa [TransitionExpr.program, transitionProgramFields]
            using inputValue)
          freshValue firstValue secondValue scratchValue
  | wire wire =>
      simpa [transitionExpressionTime, TransitionExpr.program,
        transitionProgramFields, compileTransitionFields, trList,
        List.append_assoc, rootsValue] using
        executeWireInstruction wire data fresh rest
          (by simpa [TransitionExpr.program, transitionProgramFields]
            using inputValue)
          freshValue firstValue secondValue scratchValue
  | not input induction =>
      let compiled := compileTransitionFields input fresh
      let instructionTail :=
        trList (TransitionInstruction.fields .negate) ++ rest
      let d₁ :=
        { data with
          input := instructionTail
          outputReverse :=
            (trList compiled.fields).reverse ++ data.outputReverse
          fresh := trNat compiled.nextFresh
          roots := trList (compiled.root :: roots)
          first := []
          second := [] }
      have firstRun : EvalsToInTime (TM2.step program)
          (phaseCfg .decodeNext data)
          (some (phaseCfg .decodeNext d₁))
          (transitionExpressionTime input fresh) := by
        simpa [d₁, compiled] using
          induction data fresh roots instructionTail
            (by
              simpa [TransitionExpr.program, transitionProgramFields,
                instructionTail, trList, List.append_assoc]
                using inputValue)
            freshValue rootsValue firstValue secondValue scratchValue
      have lastRun := executeNegateInstruction d₁ compiled.nextFresh
        compiled.root (trList roots) rest
        (by simp [d₁, instructionTail])
        (by simp [d₁])
        (by simp [d₁, trList, List.append_assoc])
        (by simp [d₁])
        (by simp [d₁])
        (by simpa [d₁] using scratchValue)
      have composed := thenRun firstRun lastRun
      convert composed using 1 <;>
        simp [d₁, compiled, instructionTail, transitionExpressionTime,
          compileTransitionFields, trList, List.reverse_append,
          List.append_assoc, scratchValue] <;>
        ring
  | and first second firstIH secondIH =>
      let firstCompiled := compileTransitionFields first fresh
      let secondCompiled :=
        compileTransitionFields second firstCompiled.nextFresh
      let binaryTail :=
        trList (TransitionInstruction.fields .conjoin) ++ rest
      let secondTail :=
        trList (transitionProgramFields second.program) ++ binaryTail
      let d₁ :=
        { data with
          input := secondTail
          outputReverse :=
            (trList firstCompiled.fields).reverse ++ data.outputReverse
          fresh := trNat firstCompiled.nextFresh
          roots := trList (firstCompiled.root :: roots)
          first := []
          second := [] }
      let d₂ :=
        { d₁ with
          input := binaryTail
          outputReverse :=
            (trList secondCompiled.fields).reverse ++ d₁.outputReverse
          fresh := trNat secondCompiled.nextFresh
          roots := trList
            (secondCompiled.root :: firstCompiled.root :: roots)
          first := []
          second := [] }
      have firstRun : EvalsToInTime (TM2.step program)
          (phaseCfg .decodeNext data)
          (some (phaseCfg .decodeNext d₁))
          (transitionExpressionTime first fresh) := by
        simpa [d₁, firstCompiled] using
          firstIH data fresh roots secondTail
            (by
              simpa [TransitionExpr.program, transitionProgramFields,
                secondTail, binaryTail, trList, List.append_assoc]
                using inputValue)
            freshValue rootsValue firstValue secondValue scratchValue
      have secondRun : EvalsToInTime (TM2.step program)
          (phaseCfg .decodeNext d₁)
          (some (phaseCfg .decodeNext d₂))
          (transitionExpressionTime second firstCompiled.nextFresh) := by
        simpa [d₂, secondCompiled] using
          secondIH d₁ firstCompiled.nextFresh (firstCompiled.root :: roots)
            binaryTail
            (by simp [d₁, secondTail])
            (by simp [d₁])
            (by simp [d₁])
            (by simp [d₁])
            (by simp [d₁])
            (by simpa [d₁] using scratchValue)
      have lastRun := executeBinaryInstruction .conjunction d₂
        secondCompiled.nextFresh firstCompiled.root secondCompiled.root
        (trList roots) rest
        (by simp [d₂, binaryTail, binaryInstruction])
        (by simp [d₂])
        (by simp [d₂, trList, List.append_assoc])
        (by simp [d₂])
        (by simp [d₂])
        (by simpa [d₂, d₁] using scratchValue)
      rw [show binaryGateFields .conjunction secondCompiled.nextFresh
          firstCompiled.root secondCompiled.root =
          andGateFields secondCompiled.nextFresh
            (gateOutput firstCompiled.root)
            (gateOutput secondCompiled.root) by rfl] at lastRun
      have composed := thenRun (thenRun firstRun secondRun) lastRun
      convert composed using 1 <;>
        simp [d₂, d₁, firstCompiled, secondCompiled, secondTail,
          binaryTail, transitionExpressionTime, compileTransitionFields,
          trList, List.reverse_append, List.append_assoc, scratchValue] <;>
        ring
  | or first second firstIH secondIH =>
      let firstCompiled := compileTransitionFields first fresh
      let secondCompiled :=
        compileTransitionFields second firstCompiled.nextFresh
      let binaryTail :=
        trList (TransitionInstruction.fields .disjoin) ++ rest
      let secondTail :=
        trList (transitionProgramFields second.program) ++ binaryTail
      let d₁ :=
        { data with
          input := secondTail
          outputReverse :=
            (trList firstCompiled.fields).reverse ++ data.outputReverse
          fresh := trNat firstCompiled.nextFresh
          roots := trList (firstCompiled.root :: roots)
          first := []
          second := [] }
      let d₂ :=
        { d₁ with
          input := binaryTail
          outputReverse :=
            (trList secondCompiled.fields).reverse ++ d₁.outputReverse
          fresh := trNat secondCompiled.nextFresh
          roots := trList
            (secondCompiled.root :: firstCompiled.root :: roots)
          first := []
          second := [] }
      have firstRun : EvalsToInTime (TM2.step program)
          (phaseCfg .decodeNext data)
          (some (phaseCfg .decodeNext d₁))
          (transitionExpressionTime first fresh) := by
        simpa [d₁, firstCompiled] using
          firstIH data fresh roots secondTail
            (by
              simpa [TransitionExpr.program, transitionProgramFields,
                secondTail, binaryTail, trList, List.append_assoc]
                using inputValue)
            freshValue rootsValue firstValue secondValue scratchValue
      have secondRun : EvalsToInTime (TM2.step program)
          (phaseCfg .decodeNext d₁)
          (some (phaseCfg .decodeNext d₂))
          (transitionExpressionTime second firstCompiled.nextFresh) := by
        simpa [d₂, secondCompiled] using
          secondIH d₁ firstCompiled.nextFresh (firstCompiled.root :: roots)
            binaryTail
            (by simp [d₁, secondTail])
            (by simp [d₁])
            (by simp [d₁])
            (by simp [d₁])
            (by simp [d₁])
            (by simpa [d₁] using scratchValue)
      have lastRun := executeBinaryInstruction .disjunction d₂
        secondCompiled.nextFresh firstCompiled.root secondCompiled.root
        (trList roots) rest
        (by simp [d₂, binaryTail, binaryInstruction])
        (by simp [d₂])
        (by simp [d₂, trList, List.append_assoc])
        (by simp [d₂])
        (by simp [d₂])
        (by simpa [d₂, d₁] using scratchValue)
      rw [show binaryGateFields .disjunction secondCompiled.nextFresh
          firstCompiled.root secondCompiled.root =
          orGateFields secondCompiled.nextFresh
            (gateOutput firstCompiled.root)
            (gateOutput secondCompiled.root) by rfl] at lastRun
      have composed := thenRun (thenRun firstRun secondRun) lastRun
      convert composed using 1 <;>
        simp [d₂, d₁, firstCompiled, secondCompiled, secondTail,
          binaryTail, transitionExpressionTime, compileTransitionFields,
          trList, List.reverse_append, List.append_assoc, scratchValue] <;>
        ring

/-- Once the instruction stream is empty, pop its unique root, emit the unit
clause forcing that root true, clear the last live register, and reverse the
complete output accumulator. -/
def finalizeRoot (data : TapeData) (fresh root : Nat)
    (accumulator : List Γ')
    (inputValue : data.input = [])
    (reverseValue : data.outputReverse = accumulator)
    (freshValue : data.fresh = trNat fresh)
    (rootsValue : data.roots = trList [root])
    (firstValue : data.first = [])
    (secondValue : data.second = [])
    (scratchValue : data.scratch = []) :
    EvalsToInTime (TM2.step program)
      (phaseCfg .decodeNext data)
      (some (phaseCfg .done
        { data with
          input := []
          outputReverse := []
          output := accumulator.reverse ++
            trList (constantGateFields root true) ++ data.output
          fresh := []
          roots := []
          first := []
          second := []
          scratch := [] }))
      ((trNat fresh).length + 5 * (trNat root).length +
        (trList (constantGateFields root true)).length +
        accumulator.length + 13) := by
  let d₁ := data.setAtom .fresh []
  let d₂ :=
    { (d₁.setField .roots []).setAtom .fresh (trNat root) with
      scratch := [] }
  let d₃ :=
    emittedWordData (emittedWordData d₂ (trList [1])) (trList [root])
  let d₄ := emittedWordData d₃ (trList [0, 0, 1])
  let d₅ := d₄.setAtom .fresh []
  have h₀ := oneStep (step_phase_decodeNext data)
  have consumedData : consumedInputData data [] = data := by
    rcases data with
      ⟨input, outputReverse, output, freshWord, roots, first, second,
        scratch⟩
    change input = [] at inputValue
    subst input
    rfl
  have h₁ : EvalsToInTime (TM2.step program)
      (controlCfg .decodeTag data)
      (some (clearAtomCfg .fresh .finalReadRoot data)) 1 := by
    have step := oneStep (step_decodeTag_nil data inputValue)
    rw [consumedData] at step
    simpa [controlCfg, clearAtomCfg] using step
  have h₂ : EvalsToInTime (TM2.step program)
      (clearAtomCfg .fresh .finalReadRoot data)
      (some (phaseCfg .finalReadRoot d₁))
      ((trNat fresh).length + 1) := by
    simpa [d₁] using
      clearAtom_to_phase .fresh .finalReadRoot data (trNat fresh) freshValue
  have h₃ := oneStep (step_phase_finalReadRoot d₁)
  have h₄ : EvalsToInTime (TM2.step program)
      (readFieldCfg .roots .fresh .finalConstantStart d₁)
      (some (phaseCfg .finalConstantStart d₂))
      (2 * (trNat root).length + 2) := by
    simpa [d₂] using
      readField_trNat .roots .fresh .finalConstantStart d₁ root []
        (by simpa [d₁, TapeData.setAtom, TapeData.field] using rootsValue)
        (by simp [d₁, TapeData.setAtom, TapeData.atom])
        (by simpa [d₁, TapeData.setAtom] using scratchValue)
  have h₅ : EvalsToInTime (TM2.step program)
      (phaseCfg .finalConstantStart d₂)
      (some (phaseCfg .finalConstantTail d₃))
      (2 * (trNat root).length + 3) := by
    simpa [d₃] using
      emitFixedThenAtom .fresh d₂ (trList [1]) root
        (step_finalConstantStart d₂)
        (by simp [d₂, d₁, TapeData.setField, TapeData.setAtom,
          TapeData.atom])
        (by simp [d₂])
  have h₆ : EvalsToInTime (TM2.step program)
      (phaseCfg .finalConstantTail d₃)
      (some (clearAtomCfg .fresh .finalReverse d₄)) 1 := by
    simpa [d₄] using oneStep (step_finalConstantTail d₃)
  have h₇ : EvalsToInTime (TM2.step program)
      (clearAtomCfg .fresh .finalReverse d₄)
      (some (phaseCfg .finalReverse d₅))
      ((trNat root).length + 1) := by
    simpa [d₅] using
      clearAtom_to_phase .fresh .finalReverse d₄ (trNat root) (by
        simp [d₄, d₃, d₂, d₁, emittedWordData, TapeData.setField,
          TapeData.setAtom, TapeData.atom])
  have h₈ := oneStep (step_phase_finalReverse d₅)
  have reverseAccumulator :
      d₅.outputReverse =
        (trList (constantGateFields root true)).reverse ++ accumulator := by
    rw [constantGateFields_native]
    simp [d₅, d₄, d₃, d₂, d₁, emittedWordData,
      reverseValue, trList,
      TapeData.setField, TapeData.setAtom, List.reverse_append,
      List.append_assoc]
  have h₉ := reverseOutput_to_done d₅
    ((trList (constantGateFields root true)).reverse ++ accumulator)
    reverseAccumulator
  have composed :=
    thenRun (thenRun (thenRun (thenRun (thenRun (thenRun (thenRun (thenRun (thenRun
      h₀ h₁) h₂) h₃) h₄) h₅) h₆) h₇) h₈) h₉
  convert composed using 1 <;>
    simp [d₅, d₄, d₃, d₂, d₁, emittedWordData,
      constantGateFields_native, inputValue, reverseValue, rootsValue,
      firstValue, secondValue, scratchValue, TapeData.setField,
      TapeData.setAtom, TapeData.atom, trList, List.reverse_append,
      List.append_assoc, Nat.add_comm] <;>
    ring

def initialData (input : List Γ') : TapeData :=
  ⟨input, [], [], [], [], [], [], []⟩

def outputData (output : List Γ') : TapeData :=
  ⟨[], [], output, [], [], [], [], []⟩

theorem initList_machine (input : List Γ') :
    initList machine input =
      copyInputFieldCfg .readFresh (initialData input) := by
  unfold initList machine copyInputFieldCfg initialData tapes
  congr 1
  funext stack
  cases stack <;> rfl

theorem phaseDone_outputData (output : List Γ') :
    TM2.step program (phaseCfg .done (outputData output)) =
      some (haltList machine output) := by
  unfold phaseCfg outputData haltList machine tapes
  simp [TM2.step, program]
  congr 2
  funext stack
  cases stack <;> rfl

/-- Exact end-to-end running time of the finite transition compiler on a
generated expression request. -/
def transitionMachineTime (expression : TransitionExpr) (fresh : Nat) : Nat :=
  let compiled := compileTransitionFields expression fresh
  let clauseCount := expression.clauseCount + 1
  (trNat clauseCount).length + 1 + 1 +
    (2 * (trNat fresh).length + 2) +
    transitionExpressionTime expression fresh +
    ((trNat compiled.nextFresh).length +
      5 * (trNat compiled.root).length +
      (trList (constantGateFields compiled.root true)).length +
      ((trList compiled.fields).reverse ++
        (trList [clauseCount]).reverse).length + 13) + 1

/-- The finite machine consumes every generated native compiler request and
halts with exactly the verified required-expression formula encoding. -/
noncomputable def transitionMachine_outputs (expression : TransitionExpr)
    (fresh : Nat) :
    TM2OutputsInTime machine
      (trList (transitionCompilerInputFields expression fresh))
      (some (trList (requireTransitionExprFields expression fresh)))
      (transitionMachineTime expression fresh) := by
  let compiled := compileTransitionFields expression fresh
  let clauseCount := expression.clauseCount + 1
  let programInput :=
    trList (transitionProgramFields expression.program)
  let afterHeader :=
    { initialData (trList (transitionCompilerInputFields expression fresh)) with
      input := trList [fresh] ++ programInput
      outputReverse := (trList [clauseCount]).reverse }
  let afterFresh :=
    { afterHeader with
      input := programInput
      fresh := trNat fresh
      scratch := [] }
  let afterProgram :=
    { afterFresh with
      input := []
      outputReverse :=
        (trList compiled.fields).reverse ++ afterFresh.outputReverse
      fresh := trNat compiled.nextFresh
      roots := trList [compiled.root]
      first := []
      second := [] }
  have h₀ : EvalsToInTime (TM2.step program)
      (copyInputFieldCfg .readFresh
        (initialData
          (trList (transitionCompilerInputFields expression fresh))))
      (some (phaseCfg .readFresh afterHeader))
      ((trNat clauseCount).length + 1) := by
    simpa [afterHeader, clauseCount, programInput, initialData,
      transitionCompilerInputFields, trList, List.append_assoc] using
      copyInputField_trNat .readFresh
        (initialData
          (trList (transitionCompilerInputFields expression fresh)))
        clauseCount (trList [fresh] ++ programInput) (by
          simp [initialData, transitionCompilerInputFields, clauseCount,
            programInput, trList, List.append_assoc])
  have h₁ := oneStep (step_phase_readFresh afterHeader)
  have h₂ : EvalsToInTime (TM2.step program)
      (readFieldCfg .input .fresh .decodeNext afterHeader)
      (some (phaseCfg .decodeNext afterFresh))
      (2 * (trNat fresh).length + 2) := by
    simpa [afterFresh, TapeData.setField, TapeData.setAtom] using
      readField_trNat .input .fresh .decodeNext afterHeader fresh programInput
        (by simp [afterHeader, TapeData.field])
        (by simp [afterHeader, initialData, TapeData.atom])
        (by simp [afterHeader, initialData])
  have h₃ : EvalsToInTime (TM2.step program)
      (phaseCfg .decodeNext afterFresh)
      (some (phaseCfg .decodeNext afterProgram))
      (transitionExpressionTime expression fresh) := by
    simpa [afterProgram, compiled] using
      executeExpressionProgram expression afterFresh fresh [] []
        (by simp [afterFresh, programInput])
        (by simp [afterFresh])
        (by simp [afterFresh, afterHeader, initialData])
        (by simp [afterFresh, afterHeader, initialData])
        (by simp [afterFresh, afterHeader, initialData])
        (by simp [afterFresh])
  have h₄ := finalizeRoot afterProgram compiled.nextFresh compiled.root
    ((trList compiled.fields).reverse ++ (trList [clauseCount]).reverse)
    (by simp [afterProgram])
    (by simp [afterProgram, afterFresh, afterHeader])
    (by simp [afterProgram])
    (by simp [afterProgram, trList])
    (by simp [afterProgram])
    (by simp [afterProgram])
    (by simp [afterProgram, afterFresh])
  have h₄' : EvalsToInTime (TM2.step program)
      (phaseCfg .decodeNext afterProgram)
      (some (phaseCfg .done
        (outputData
          (trList (requireTransitionExprFields expression fresh)))))
      ((trNat compiled.nextFresh).length +
        5 * (trNat compiled.root).length +
        (trList (constantGateFields compiled.root true)).length +
        ((trList compiled.fields).reverse ++
          (trList [clauseCount]).reverse).length + 13) := by
    simpa [afterProgram, afterFresh, afterHeader, initialData, outputData,
      compiled, clauseCount, requireTransitionExprFields, trList,
      List.reverse_append, List.append_assoc] using h₄
  have h₅ := oneStep
    (phaseDone_outputData
      (trList (requireTransitionExprFields expression fresh)))
  unfold TM2OutputsInTime FinTM2.step
  rw [initList_machine]
  have composed :=
    thenRun (thenRun (thenRun (thenRun (thenRun h₀ h₁) h₂) h₃) h₄') h₅
  refine
    { toEvalsTo := by
        simpa only [machine, FinTM2.Cfg, Option.map] using composed.toEvalsTo
      steps_le_m := ?_ }
  simpa [transitionMachineTime, compiled, clauseCount, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using composed.steps_le_m

end TransitionEvaluatorMachine
end PeriodicCNF
end LeanTrominoes
