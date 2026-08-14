/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFUnaryProgramTokens
import LeanTrominoes.TM2CompositionMachine

/-!
# Finalizing counted unary compact-program tokens

The unary clause-count machine retains a finite token word and appends one
tagged unit per clause.  The unary field encoder instead expects the clause
count first, followed by its delimiter and then the unary expansion of the
token word.  This file verifies a fixed finite four-stack transducer carrying
out exactly that rotation and expansion.

One input scan accumulates expanded token blocks and count units in reverse.
Draining the body stack, inserting one delimiter, and draining the header
stack produces the exact normalized unary request in linear time.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace UnaryProgramTokenFinalizer

open UnaryFieldEncoderMachine UnaryProgramTokens

abbrev Source := Token ⊕ Unit

inductive Stack
  | input
  | bodyReverse
  | headerReverse
  | output
  deriving DecidableEq, Fintype

inductive Label
  | scan
  | emitToken (token : Token)
  | emitBody
  | emitDelimiter
  | emitHeader
  deriving Fintype

/-- The scan state contains either a token or an already converted unary
symbol.  Both body and header drains use the symbol alternative. -/
abbrev State := Option (Token ⊕ Symbol)

abbrev Alphabet : Stack → Type
  | .input => Source
  | .bodyReverse | .headerReverse | .output => Symbol

def scanValue : Source → Token ⊕ Symbol
  | .inl token => .inl token
  | .inr _ => .inr .unit

def tokenFromState : State → Token
  | some (.inl token) => token
  | _ => default

def symbolFromState : State → Symbol
  | some (.inr symbol) => symbol
  | _ => default

def stateHasToken : State → Bool
  | some (.inl _) => true
  | _ => false

def pushBodyWord (word : List Symbol)
    (next : TM2.Stmt Alphabet Label State) :
    TM2.Stmt Alphabet Label State :=
  word.foldr
    (fun symbol continuation =>
      .push .bodyReverse (fun _ => symbol) continuation)
    next

def program : Label → TM2.Stmt Alphabet Label State
  | .scan =>
      .pop .input (fun _ source => source.map scanValue)
        (.branch Option.isNone
          (.goto fun _ => .emitBody)
          (.branch stateHasToken
            (.goto fun state => .emitToken (tokenFromState state))
            (.push .headerReverse symbolFromState
              (.load (fun _ => none) (.goto fun _ => .scan)))))
  | .emitToken token =>
      pushBodyWord (unaryBlock token)
        (.load (fun _ => none) (.goto fun _ => .scan))
  | .emitBody =>
      .pop .bodyReverse (fun _ symbol => symbol.map Sum.inr)
        (.branch Option.isNone
          (.goto fun _ => .emitDelimiter)
          (.push .output symbolFromState
            (.load (fun _ => none) (.goto fun _ => .emitBody))))
  | .emitDelimiter =>
      .push .output (fun _ => .delimiter)
        (.goto fun _ => .emitHeader)
  | .emitHeader =>
      .pop .headerReverse (fun _ symbol => symbol.map Sum.inr)
        (.branch Option.isNone
          .halt
          (.push .output symbolFromState
            (.load (fun _ => none) (.goto fun _ => .emitHeader))))

abbrev machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := none
  m := program

structure TapeData where
  input : List Source
  bodyReverse : List Symbol
  headerReverse : List Symbol
  output : List Symbol

def tapes (data : TapeData) : ∀ stack, List (Alphabet stack)
  | .input => data.input
  | .bodyReverse => data.bodyReverse
  | .headerReverse => data.headerReverse
  | .output => data.output

def cfg (label : Label) (state : State) (data : TapeData) :
    TM2.Cfg Alphabet Label State :=
  ⟨some label, state, tapes data⟩

def scanCfg (data : TapeData) := cfg .scan none data

def emitTokenCfg (token : Token) (data : TapeData) :=
  cfg (.emitToken token) (some (.inl token)) data

def emitBodyCfg (data : TapeData) := cfg .emitBody none data

def emitDelimiterCfg (data : TapeData) := cfg .emitDelimiter none data

def emitHeaderCfg (data : TapeData) := cfg .emitHeader none data

def haltCfg (output : List Symbol) : TM2.Cfg Alphabet Label State :=
  ⟨none, none, tapes ⟨[], [], [], output⟩⟩

def haltDataCfg (data : TapeData) : TM2.Cfg Alphabet Label State :=
  ⟨none, none, tapes data⟩

@[simp]
theorem haltDataCfg_empty_eq_haltCfg (output : List Symbol) :
    haltDataCfg ⟨[], [], [], output⟩ = haltCfg output :=
  rfl

@[simp]
theorem update_tapes_input (data : TapeData) (value : List Source) :
    Function.update (tapes data) Stack.input value =
      tapes { data with input := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_bodyReverse (data : TapeData) (value : List Symbol) :
    Function.update (tapes data) Stack.bodyReverse value =
      tapes { data with bodyReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_headerReverse (data : TapeData)
    (value : List Symbol) :
    Function.update (tapes data) Stack.headerReverse value =
      tapes { data with headerReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_output (data : TapeData) (value : List Symbol) :
    Function.update (tapes data) Stack.output value =
      tapes { data with output := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem stepAux_pushBodyWord (word : List Symbol)
    (next : TM2.Stmt Alphabet Label State) (state : State)
    (data : TapeData) :
    TM2.stepAux (pushBodyWord word next) state (tapes data) =
      TM2.stepAux next state
        (tapes { data with
          bodyReverse := word.reverse ++ data.bodyReverse }) := by
  induction word generalizing data with
  | nil => simp [pushBodyWord]
  | cons symbol word induction =>
      simp only [pushBodyWord, List.foldr_cons, TM2.stepAux]
      rw [update_tapes_bodyReverse]
      change TM2.stepAux (pushBodyWord word next) state
          (tapes { data with bodyReverse := symbol :: data.bodyReverse }) = _
      rw [induction]
      simp [List.reverse_cons, List.append_assoc]

theorem step_scan_nil (data : TapeData) (inputEq : data.input = []) :
    TM2.step program (scanCfg data) =
      some (emitBodyCfg { data with input := [] }) := by
  rcases data with ⟨input, bodyReverse, headerReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, scanCfg, emitBodyCfg, cfg, tapes]

theorem step_scan_token (data : TapeData) (token : Token)
    (tail : List Source) (inputEq : data.input = .inl token :: tail) :
    TM2.step program (scanCfg data) =
      some (emitTokenCfg token { data with input := tail }) := by
  rcases data with ⟨input, bodyReverse, headerReverse, output⟩
  change input = .inl token :: tail at inputEq
  subst input
  simp [TM2.step, program, scanCfg, emitTokenCfg, cfg, tapes,
    scanValue, stateHasToken, tokenFromState]

theorem step_scan_header (data : TapeData) (tail : List Source)
    (inputEq : data.input = .inr () :: tail) :
    TM2.step program (scanCfg data) =
      some (scanCfg
        { data with
          input := tail
          headerReverse := .unit :: data.headerReverse }) := by
  rcases data with ⟨input, bodyReverse, headerReverse, output⟩
  change input = .inr () :: tail at inputEq
  subst input
  simp [TM2.step, program, scanCfg, cfg, tapes, scanValue,
    stateHasToken, symbolFromState]

theorem step_emitToken (token : Token) (data : TapeData) :
    TM2.step program (emitTokenCfg token data) =
      some (scanCfg
        { data with
          bodyReverse :=
            (unaryBlock token).reverse ++ data.bodyReverse }) := by
  simp only [TM2.step, program, emitTokenCfg, scanCfg, cfg]
  rw [stepAux_pushBodyWord]
  rfl

theorem step_emitBody_nil (data : TapeData)
    (bodyEq : data.bodyReverse = []) :
    TM2.step program (emitBodyCfg data) =
      some (emitDelimiterCfg { data with bodyReverse := [] }) := by
  rcases data with ⟨input, bodyReverse, headerReverse, output⟩
  change bodyReverse = [] at bodyEq
  subst bodyReverse
  simp [TM2.step, program, emitBodyCfg, emitDelimiterCfg, cfg, tapes]

theorem step_emitBody_cons (data : TapeData) (symbol : Symbol)
    (tail : List Symbol) (bodyEq : data.bodyReverse = symbol :: tail) :
    TM2.step program (emitBodyCfg data) =
      some (emitBodyCfg
        { data with
          bodyReverse := tail
          output := symbol :: data.output }) := by
  rcases data with ⟨input, bodyReverse, headerReverse, output⟩
  change bodyReverse = symbol :: tail at bodyEq
  subst bodyReverse
  cases symbol <;>
    simp [TM2.step, program, emitBodyCfg, cfg, tapes, symbolFromState]

theorem step_emitDelimiter (data : TapeData) :
    TM2.step program (emitDelimiterCfg data) =
      some (emitHeaderCfg
        { data with output := .delimiter :: data.output }) := by
  rcases data with ⟨input, bodyReverse, headerReverse, output⟩
  simp [TM2.step, program, emitDelimiterCfg, emitHeaderCfg, cfg, tapes]

theorem step_emitHeader_nil (data : TapeData)
    (headerEq : data.headerReverse = []) :
    TM2.step program (emitHeaderCfg data) =
      some (haltDataCfg { data with headerReverse := [] }) := by
  rcases data with ⟨input, bodyReverse, headerReverse, output⟩
  change headerReverse = [] at headerEq
  subst headerReverse
  simp [TM2.step, program, emitHeaderCfg, haltDataCfg, cfg, tapes]

theorem step_emitHeader_cons (data : TapeData) (symbol : Symbol)
    (tail : List Symbol) (headerEq : data.headerReverse = symbol :: tail) :
    TM2.step program (emitHeaderCfg data) =
      some (emitHeaderCfg
        { data with
          headerReverse := tail
          output := symbol :: data.output }) := by
  rcases data with ⟨input, bodyReverse, headerReverse, output⟩
  change headerReverse = symbol :: tail at headerEq
  subst headerReverse
  cases symbol <;>
    simp [TM2.step, program, emitHeaderCfg, cfg, tapes, symbolFromState]

def oneStep {Configuration : Type}
    {transition : Configuration → Option Configuration}
    {first last : Configuration} (step : transition first = some last) :
    EvalsToInTime transition first (some last) 1 :=
  FiniteBlockTransducer.oneStep step

/-- Unary body contributed by token-tagged symbols. -/
def body : List Source → List Symbol
  | [] => []
  | .inl token :: sources => unaryBlock token ++ body sources
  | .inr _ :: sources => body sources

/-- Unary clause header contributed by count-tagged units. -/
def header : List Source → List Symbol
  | [] => []
  | .inl _ :: sources => header sources
  | .inr _ :: sources => .unit :: header sources

def scanTime : List Source → Nat
  | [] => 1
  | .inl _ :: sources => 2 + scanTime sources
  | .inr _ :: sources => 1 + scanTime sources

def scan_evalsInTime (sources : List Source) (data : TapeData)
    (inputEq : data.input = sources) :
    EvalsToInTime (TM2.step program) (scanCfg data)
      (some (emitBodyCfg
        { data with
          input := []
          bodyReverse := (body sources).reverse ++ data.bodyReverse
          headerReverse :=
            (header sources).reverse ++ data.headerReverse }))
      (scanTime sources) := by
  induction sources generalizing data with
  | nil =>
      have step := oneStep (step_scan_nil data inputEq)
      convert step using 1 <;> simp [body, header, scanTime]
  | cons source sources induction =>
      cases source with
      | inl token =>
          have first := oneStep
            (step_scan_token data token sources inputEq)
          let nextData := { data with input := sources }
          have emitted := oneStep (step_emitToken token nextData)
          let emittedData :=
            { nextData with
              bodyReverse :=
                (unaryBlock token).reverse ++ nextData.bodyReverse }
          have firstTwo := EvalsToInTime.trans (TM2.step program)
            1 1 (scanCfg data) (emitTokenCfg token nextData)
            (some (scanCfg emittedData)) first emitted
          have rest := induction emittedData rfl
          have composed := EvalsToInTime.trans (TM2.step program)
            2 (scanTime sources) (scanCfg data) (scanCfg emittedData)
            (some (emitBodyCfg
              { emittedData with
                input := []
                bodyReverse :=
                  (body sources).reverse ++ emittedData.bodyReverse
                headerReverse :=
                  (header sources).reverse ++ emittedData.headerReverse }))
            firstTwo rest
          convert composed using 1
          · simp [body, header, emittedData, nextData,
              List.reverse_append, List.append_assoc]
          · simp [scanTime]
            omega
      | inr element =>
          have elementEq : element = () := Subsingleton.elim _ _
          subst element
          have first := oneStep (step_scan_header data sources inputEq)
          let nextData :=
            { data with
              input := sources
              headerReverse := .unit :: data.headerReverse }
          have rest := induction nextData rfl
          have composed := EvalsToInTime.trans (TM2.step program)
            1 (scanTime sources) (scanCfg data) (scanCfg nextData)
            (some (emitBodyCfg
              { nextData with
                input := []
                bodyReverse :=
                  (body sources).reverse ++ nextData.bodyReverse
                headerReverse :=
                  (header sources).reverse ++ nextData.headerReverse }))
            first rest
          convert composed using 1
          · simp [body, header, nextData, List.reverse_cons,
              List.append_assoc]
          · simp [scanTime]
            omega

def emitBody_evalsInTime (word : List Symbol) (data : TapeData)
    (bodyEq : data.bodyReverse = word) :
    EvalsToInTime (TM2.step program) (emitBodyCfg data)
      (some (emitDelimiterCfg
        { data with
          bodyReverse := []
          output := word.reverse ++ data.output }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep (step_emitBody_nil data bodyEq)
      convert step using 1 <;> simp
  | cons symbol word induction =>
      let nextData :=
        { data with
          bodyReverse := word
          output := symbol :: data.output }
      have first := oneStep
        (step_emitBody_cons data symbol word bodyEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1) (emitBodyCfg data) (emitBodyCfg nextData)
        (some (emitDelimiterCfg
          { nextData with
            bodyReverse := []
            output := word.reverse ++ nextData.output }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

def emitHeader_evalsInTime (word : List Symbol) (data : TapeData)
    (headerEq : data.headerReverse = word) :
    EvalsToInTime (TM2.step program) (emitHeaderCfg data)
      (some (haltDataCfg
        { data with
          headerReverse := []
          output := word.reverse ++ data.output }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep (step_emitHeader_nil data headerEq)
      convert step using 1 <;> simp
  | cons symbol word induction =>
      let nextData :=
        { data with
          headerReverse := word
          output := symbol :: data.output }
      have first := oneStep
        (step_emitHeader_cons data symbol word headerEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (word.length + 1) (emitHeaderCfg data) (emitHeaderCfg nextData)
        (some (haltDataCfg
          { nextData with
            headerReverse := []
            output := word.reverse ++ nextData.output }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

/-- Put the tagged unary count suffix first, delimit it, and expand the token
body. -/
def finalize (sources : List Source) : List Symbol :=
  header sources ++ [.delimiter] ++ body sources

def totalTime (sources : List Source) : Nat :=
  scanTime sources + (body sources).length + 1 + 1 +
    (header sources).length + 1

theorem initList_eq_scanCfg (sources : List Source) :
    initList machine sources = scanCfg ⟨sources, [], [], []⟩ := by
  unfold initList machine scanCfg cfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

theorem haltList_eq_haltCfg (output : List Symbol) :
    haltList machine output = haltCfg output := by
  unfold haltList machine haltCfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

def machine_outputsInTime (sources : List Source) :
    TM2OutputsInTime machine sources (some (finalize sources))
      (totalTime sources) := by
  let initial : TapeData := ⟨sources, [], [], []⟩
  let scanned : TapeData :=
    ⟨[], (body sources).reverse, (header sources).reverse, []⟩
  let bodyEmitted : TapeData :=
    ⟨[], [], (header sources).reverse, body sources⟩
  let delimited : TapeData :=
    ⟨[], [], (header sources).reverse, .delimiter :: body sources⟩
  have scanRun := scan_evalsInTime sources initial rfl
  have bodyRun := emitBody_evalsInTime (body sources).reverse scanned rfl
  have firstTwo := EvalsToInTime.trans (TM2.step program)
    (scanTime sources) ((body sources).length + 1)
    (scanCfg initial) (emitBodyCfg scanned)
    (some (emitDelimiterCfg bodyEmitted))
    (by simpa [initial, scanned] using scanRun)
    (by simpa [scanned, bodyEmitted] using bodyRun)
  have delimiterRun := oneStep (step_emitDelimiter bodyEmitted)
  have firstThree := EvalsToInTime.trans (TM2.step program)
    ((body sources).length + 1 + scanTime sources) 1
    (scanCfg initial) (emitDelimiterCfg bodyEmitted)
    (some (emitHeaderCfg delimited)) firstTwo
    (by simpa [delimited] using delimiterRun)
  have headerRun := emitHeader_evalsInTime
    (header sources).reverse delimited rfl
  have whole := EvalsToInTime.trans (TM2.step program)
    (1 + ((body sources).length + 1 + scanTime sources))
    ((header sources).length + 1)
    (scanCfg initial) (emitHeaderCfg delimited)
    (some (haltDataCfg ⟨[], [], [], finalize sources⟩))
    firstThree (by
      simpa [delimited, finalize, List.append_assoc] using headerRun)
  refine
    { steps := whole.steps
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · change (flip bind (TM2.step program))^[whole.steps]
        (some (initList machine sources)) =
          some (haltList machine (finalize sources))
    rw [initList_eq_scanCfg, haltList_eq_haltCfg,
      ← haltDataCfg_empty_eq_haltCfg]
    convert whole.evals_in_steps using 1
    rfl
  · exact whole.steps_le_m.trans (by
      simp [totalTime]
      omega)

theorem scanTime_le (sources : List Source) :
    scanTime sources ≤ 2 * sources.length + 1 := by
  induction sources with
  | nil => simp [scanTime]
  | cons source sources induction =>
      cases source <;> simp [scanTime] at * <;> omega

theorem header_length_le (sources : List Source) :
    (header sources).length ≤ sources.length := by
  induction sources with
  | nil => simp [header]
  | cons source sources induction =>
      cases source <;> simp [header] at * <;> omega

theorem body_length_le (sources : List Source) :
    (body sources).length ≤
      sources.length * FiniteBlockTransducer.wordLengthBound unaryBlock := by
  induction sources with
  | nil => simp [body]
  | cons source sources induction =>
      cases source with
      | inl token =>
          simp only [body, List.length_append, List.length_cons]
          have block :=
            FiniteBlockTransducer.word_length_le_bound unaryBlock token
          nlinarith
      | inr element =>
          simp only [body, List.length_cons]
          have nonnegative :
              0 ≤ FiniteBlockTransducer.wordLengthBound unaryBlock :=
            Nat.zero_le _
          nlinarith

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C
      (FiniteBlockTransducer.wordLengthBound unaryBlock + 3) *
    Polynomial.X + Polynomial.C 4

@[simp]
theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length =
      (FiniteBlockTransducer.wordLengthBound unaryBlock + 3) * length + 4 := by
  simp [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul]

theorem totalTime_le (sources : List Source) :
    totalTime sources ≤ timePolynomial.eval sources.length := by
  rw [timePolynomial_eval]
  have scanBound := scanTime_le sources
  have bodyBound := body_length_le sources
  have headerBound := header_length_le sources
  unfold totalTime
  nlinarith

/-- Unary count-header rotation and finite token expansion are polynomial-time
(indeed linear-time). -/
noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime
      (List Source) (List Symbol) Source Symbol id id finalize where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial
  outputsFun sources := by
    have run := machine_outputsInTime sources
    have run' : TM2OutputsInTime machine
        (List.map (Equiv.refl Source).invFun (id sources))
        (some (List.map (Equiv.refl Symbol).invFun
          (id (finalize sources))))
        (totalTime sources) := by
      simpa only [FiniteBlockTransducer.map_refl_invFun, id_eq] using run
    exact
      { toEvalsTo := run'.toEvalsTo
        steps_le_m := run'.steps_le_m.trans (totalTime_le sources) }

/-- Complete generic postprocessing from an uncounted unary token stream to
an ordered unary request. -/
def countAndFinalize (tokens : List Token) : List Symbol :=
  finalize
    (UnaryPolynomialPaddingMachine.paddedOutput isClauseMarker [0, 1]
      tokens)

/-- Clause counting followed by unary header rotation and token expansion is
polynomial-time. -/
noncomputable def countAndFinalizeComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List Token) (List Symbol) Token Symbol id id countAndFinalize := by
  let composed := TM2CompositionMachine.computableInPolyTime
    UnaryProgramTokens.appendClauseCountComputableInPolyTime
    computableInPolyTime
  exact composed

@[simp]
theorem body_append (first second : List Source) :
    body (first ++ second) = body first ++ body second := by
  induction first with
  | nil => rfl
  | cons source first induction =>
      cases source <;> simp [body, induction, List.append_assoc]

@[simp]
theorem header_append (first second : List Source) :
    header (first ++ second) = header first ++ header second := by
  induction first with
  | nil => rfl
  | cons source first induction =>
      cases source <;> simp [header, induction]

@[simp]
theorem body_map_token (tokens : List Token) :
    body (tokens.map (fun token => (Sum.inl token : Source))) =
      unaryEncode tokens := by
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      simp [body, unaryEncode, induction]

@[simp]
theorem body_map_header (units : List Unit) :
    body (units.map (fun element => (Sum.inr element : Source))) = [] := by
  induction units with
  | nil => rfl
  | cons element units induction =>
      simp [body, induction]

@[simp]
theorem header_map_token (tokens : List Token) :
    header (tokens.map (fun token => (Sum.inl token : Source))) = [] := by
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      simp [header, induction]

@[simp]
theorem header_map_header (units : List Unit) :
    header (units.map (fun element => (Sum.inr element : Source))) =
      List.replicate units.length .unit := by
  induction units with
  | nil => rfl
  | cons element units induction =>
      simp only [List.map_cons, header, List.length_cons, induction]
      rw [List.replicate_succ]

@[simp]
theorem body_replicate_header (count : Nat) :
    body (List.replicate count (Sum.inr () : Source)) = [] := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      simp [body, induction]

@[simp]
theorem header_replicate_header (count : Nat) :
    header (List.replicate count (Sum.inr () : Source)) =
      List.replicate count .unit := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      simp only [header, induction]
      rw [List.replicate_succ]

@[simp]
theorem body_countedRequest (fresh : Nat)
    (program : TransitionProgram.Program) :
    body (UnaryProgramTokens.countedRequest fresh program) =
      unaryField fresh ++
        unaryFields (transitionProgramFields program) := by
  rw [UnaryProgramTokens.countedRequest_eq, body_append,
    body_map_token, body_replicate_header, List.append_nil,
    UnaryProgramTokens.unaryEncode_requestSource]

@[simp]
theorem header_countedRequest (fresh : Nat)
    (program : TransitionProgram.Program) :
    header (UnaryProgramTokens.countedRequest fresh program) =
      List.replicate (TransitionProgram.clauseCount program + 1) .unit := by
  rw [UnaryProgramTokens.countedRequest_eq, header_append,
    header_map_token, header_replicate_header, List.nil_append]

/-- Finalization gives the exact unary request: clause count, fresh atom, and
postorder instruction fields. -/
@[simp]
theorem finalize_countedRequest (fresh : Nat)
    (program : TransitionProgram.Program) :
    finalize (UnaryProgramTokens.countedRequest fresh program) =
      unaryFields
        ((TransitionProgram.clauseCount program + 1) :: fresh ::
          transitionProgramFields program) := by
  simp [finalize, unaryField, List.append_assoc]

/-- The complete generic postprocessor maps the emitter's exact finite source
to the normalized unary request fields. -/
@[simp]
theorem countAndFinalize_requestSource (fresh : Nat)
    (program : TransitionProgram.Program) :
    countAndFinalize (UnaryProgramTokens.requestSource fresh program) =
      unaryFields
        ((TransitionProgram.clauseCount program + 1) :: fresh ::
          transitionProgramFields program) := by
  change finalize (UnaryProgramTokens.countedRequest fresh program) = _
  exact finalize_countedRequest fresh program

end UnaryProgramTokenFinalizer
end PeriodicCNF
end LeanTrominoes
