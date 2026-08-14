/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramTokens

/-!
# Finalizing counted compact-program tokens

`BinaryCountPaddingMachine` retains a finite token word and appends its
canonical binary clause count.  The transition evaluator instead expects the
clause count first, followed by a delimiter and the native expansion of the
token word.  This file verifies a fixed finite four-stack transducer carrying
out exactly that reordering and expansion.

During one input scan, token blocks are accumulated in reverse on one stack
and the tagged count suffix on another.  Draining the token stack builds the
native body, one fixed step prepends its delimiter, and draining the header
stack prepends the canonical count.  The exact run is linear in the input and
expanded-output lengths, hence polynomial time.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace ProgramTokenFinalizer

open ProgramTokens

abbrev Source := Token ⊕ PartrecToTM2.Γ'

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

abbrev State := Option Source

abbrev Alphabet : Stack → Type
  | .input => Source
  | .bodyReverse | .headerReverse | .output => PartrecToTM2.Γ'

def tokenFromState : State → Token
  | some (.inl token) => token
  | _ => default

def symbolFromState : State → PartrecToTM2.Γ'
  | some (.inr symbol) => symbol
  | _ => default

def stateHasToken : State → Bool
  | some (.inl _) => true
  | _ => false

def pushBodyWord (word : List PartrecToTM2.Γ')
    (next : TM2.Stmt Alphabet Label State) :
    TM2.Stmt Alphabet Label State :=
  word.foldr
    (fun symbol continuation =>
      .push .bodyReverse (fun _ => symbol) continuation)
    next

def program : Label → TM2.Stmt Alphabet Label State
  | .scan =>
      .pop .input (fun _ symbol => symbol)
        (.branch Option.isNone
          (.goto fun _ => .emitBody)
          (.branch stateHasToken
            (.goto fun state => .emitToken (tokenFromState state))
            (.push .headerReverse (fun state => symbolFromState state)
              (.load (fun _ => none) (.goto fun _ => .scan)))))
  | .emitToken token =>
      pushBodyWord (nativeBlock token)
        (.load (fun _ => none) (.goto fun _ => .scan))
  | .emitBody =>
      .pop .bodyReverse (fun _ symbol => symbol.map Sum.inr)
        (.branch Option.isNone
          (.goto fun _ => .emitDelimiter)
          (.push .output symbolFromState
            (.load (fun _ => none) (.goto fun _ => .emitBody))))
  | .emitDelimiter =>
      .push .output (fun _ => .cons)
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
  bodyReverse : List PartrecToTM2.Γ'
  headerReverse : List PartrecToTM2.Γ'
  output : List PartrecToTM2.Γ'

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

def haltCfg (output : List PartrecToTM2.Γ') :
    TM2.Cfg Alphabet Label State :=
  ⟨none, none, tapes ⟨[], [], [], output⟩⟩

def haltDataCfg (data : TapeData) : TM2.Cfg Alphabet Label State :=
  ⟨none, none, tapes data⟩

@[simp]
theorem haltDataCfg_empty_eq_haltCfg
    (output : List PartrecToTM2.Γ') :
    haltDataCfg ⟨[], [], [], output⟩ = haltCfg output :=
  rfl

@[simp]
theorem update_tapes_input (data : TapeData) (value : List Source) :
    Function.update (tapes data) Stack.input value =
      tapes { data with input := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_bodyReverse
    (data : TapeData) (value : List PartrecToTM2.Γ') :
    Function.update (tapes data) Stack.bodyReverse value =
      tapes { data with bodyReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_headerReverse
    (data : TapeData) (value : List PartrecToTM2.Γ') :
    Function.update (tapes data) Stack.headerReverse value =
      tapes { data with headerReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_output
    (data : TapeData) (value : List PartrecToTM2.Γ') :
    Function.update (tapes data) Stack.output value =
      tapes { data with output := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem stepAux_pushBodyWord (word : List PartrecToTM2.Γ')
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
    stateHasToken, tokenFromState]

theorem step_scan_header (data : TapeData)
    (symbol : PartrecToTM2.Γ') (tail : List Source)
    (inputEq : data.input = .inr symbol :: tail) :
    TM2.step program (scanCfg data) =
      some (scanCfg
        { data with
          input := tail
          headerReverse := symbol :: data.headerReverse }) := by
  rcases data with ⟨input, bodyReverse, headerReverse, output⟩
  change input = .inr symbol :: tail at inputEq
  subst input
  cases symbol <;>
    simp [TM2.step, program, scanCfg, cfg, tapes, stateHasToken,
      symbolFromState]

theorem step_emitToken (token : Token) (data : TapeData) :
    TM2.step program (emitTokenCfg token data) =
      some (scanCfg
        { data with
          bodyReverse := (nativeBlock token).reverse ++ data.bodyReverse }) := by
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

theorem step_emitBody_cons (data : TapeData)
    (symbol : PartrecToTM2.Γ') (tail : List PartrecToTM2.Γ')
    (bodyEq : data.bodyReverse = symbol :: tail) :
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
      some (emitHeaderCfg { data with output := .cons :: data.output }) := by
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

theorem step_emitHeader_cons (data : TapeData)
    (symbol : PartrecToTM2.Γ') (tail : List PartrecToTM2.Γ')
    (headerEq : data.headerReverse = symbol :: tail) :
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

/-- Native body contributed by the token-tagged part of an arbitrary word. -/
def body : List Source → List PartrecToTM2.Γ'
  | [] => []
  | .inl token :: sources => nativeBlock token ++ body sources
  | .inr _ :: sources => body sources

/-- Native header contributed by the symbol-tagged part of an arbitrary word. -/
def header : List Source → List PartrecToTM2.Γ'
  | [] => []
  | .inl _ :: sources => header sources
  | .inr symbol :: sources => symbol :: header sources

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
          headerReverse := (header sources).reverse ++ data.headerReverse }))
      (scanTime sources) := by
  induction sources generalizing data with
  | nil =>
      have step := oneStep (step_scan_nil data inputEq)
      convert step using 1 <;> simp [body, header, scanTime]
  | cons source sources induction =>
      cases source with
      | inl token =>
          have first := oneStep (step_scan_token data token sources inputEq)
          let nextData := { data with input := sources }
          have emitted := oneStep (step_emitToken token nextData)
          let emittedData :=
            { nextData with
              bodyReverse :=
                (nativeBlock token).reverse ++ nextData.bodyReverse }
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
      | inr symbol =>
          have first := oneStep
            (step_scan_header data symbol sources inputEq)
          let nextData :=
            { data with
              input := sources
              headerReverse := symbol :: data.headerReverse }
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

def emitBody_evalsInTime (word : List PartrecToTM2.Γ')
    (data : TapeData) (bodyEq : data.bodyReverse = word) :
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

def emitHeader_evalsInTime (word : List PartrecToTM2.Γ')
    (data : TapeData) (headerEq : data.headerReverse = word) :
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

/-- Put the tagged suffix first, delimit it, and expand the token body. -/
def finalize (sources : List Source) : List PartrecToTM2.Γ' :=
  header sources ++ [.cons] ++ body sources

def totalTime (sources : List Source) : Nat :=
  scanTime sources + (body sources).length + 1 + 1 +
    (header sources).length + 1

theorem initList_eq_scanCfg (sources : List Source) :
    initList machine sources =
      scanCfg ⟨sources, [], [], []⟩ := by
  unfold initList machine scanCfg cfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

theorem haltList_eq_haltCfg (output : List PartrecToTM2.Γ') :
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
    ⟨[], [], (header sources).reverse, .cons :: body sources⟩
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
    (some (haltDataCfg
      ⟨[], [], [], finalize sources⟩)) firstThree (by
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
      sources.length * FiniteBlockTransducer.wordLengthBound nativeBlock := by
  induction sources with
  | nil => simp [body]
  | cons source sources induction =>
      cases source with
      | inl token =>
          simp only [body, List.length_append, List.length_cons]
          have block :=
            FiniteBlockTransducer.word_length_le_bound nativeBlock token
          nlinarith
      | inr symbol =>
          simp only [body, List.length_cons]
          have nonnegative :
              0 ≤ FiniteBlockTransducer.wordLengthBound nativeBlock :=
            Nat.zero_le _
          nlinarith

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C
      (FiniteBlockTransducer.wordLengthBound nativeBlock + 3) *
    Polynomial.X + Polynomial.C 4

@[simp]
theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length =
      (FiniteBlockTransducer.wordLengthBound nativeBlock + 3) * length + 4 := by
  simp [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul]

theorem totalTime_le (sources : List Source) :
    totalTime sources ≤ timePolynomial.eval sources.length := by
  rw [timePolynomial_eval]
  have scanBound := scanTime_le sources
  have bodyBound := body_length_le sources
  have headerBound := header_length_le sources
  unfold totalTime
  nlinarith

/-- Count-header rotation and finite token expansion are polynomial-time
(indeed linear-time). -/
noncomputable def computableInPolyTime :
    @TM2ComputableInPolyTime
      (List Source) (List PartrecToTM2.Γ')
      Source PartrecToTM2.Γ' id id finalize where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial
  outputsFun sources := by
    have run := machine_outputsInTime sources
    have run' : TM2OutputsInTime machine
        (List.map (Equiv.refl Source).invFun (id sources))
        (some (List.map (Equiv.refl PartrecToTM2.Γ').invFun
          (id (finalize sources))))
        (totalTime sources) := by
      simpa only [FiniteBlockTransducer.map_refl_invFun, id_eq] using run
    exact
      { toEvalsTo := run'.toEvalsTo
        steps_le_m := run'.steps_le_m.trans (totalTime_le sources) }

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
      nativeEncode tokens := by
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      simp [body, nativeEncode, induction]

@[simp]
theorem body_map_header (symbols : List PartrecToTM2.Γ') :
    body (symbols.map (fun symbol => (Sum.inr symbol : Source))) = [] := by
  induction symbols with
  | nil => rfl
  | cons symbol symbols induction =>
      simp [body, induction]

@[simp]
theorem header_map_token (tokens : List Token) :
    header (tokens.map (fun token => (Sum.inl token : Source))) = [] := by
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      simp [header, induction]

@[simp]
theorem header_map_header (symbols : List PartrecToTM2.Γ') :
    header (symbols.map (fun symbol => (Sum.inr symbol : Source))) =
      symbols := by
  induction symbols with
  | nil => rfl
  | cons symbol symbols induction =>
      simp [header, induction]

@[simp]
theorem body_countedRequest (fresh : Nat)
    (program : List TransitionInstruction) :
    body (ProgramTokens.countedRequest fresh program) =
      PartrecToTM2.trNat fresh ++ [.cons] ++
        PartrecToTM2.trList (transitionProgramFields program) := by
  rw [ProgramTokens.countedRequest_eq, body_append,
    body_map_token, body_map_header, List.append_nil,
    ProgramTokens.nativeEncode_requestSource]

@[simp]
theorem header_countedRequest (fresh : Nat)
    (program : List TransitionInstruction) :
    header (ProgramTokens.countedRequest fresh program) =
      PartrecToTM2.trNat (TransitionProgram.clauseCount program + 1) := by
  rw [ProgramTokens.countedRequest_eq, header_append,
    header_map_token, header_map_header, List.nil_append]

/-- The finalized counted token word is exactly the evaluator-native compact
request: clause count, fresh atom, and postorder instruction fields. -/
@[simp]
theorem finalize_countedRequest (fresh : Nat)
    (program : List TransitionInstruction) :
    finalize (ProgramTokens.countedRequest fresh program) =
      PartrecToTM2.trList
        ((TransitionProgram.clauseCount program + 1) :: fresh ::
          transitionProgramFields program) := by
  simp [finalize, PartrecToTM2.trList, List.append_assoc]

end ProgramTokenFinalizer
end PeriodicCNF
end LeanTrominoes
