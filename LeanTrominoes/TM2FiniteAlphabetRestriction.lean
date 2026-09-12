/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Computability.TuringMachine.Computable

/-!
# Restricting TM2 stack alphabets without changing running time

A finite TM2 program can push only finitely many symbols: every push reads
only the finite control state. Preserve the input and output alphabets and
restrict every other stack to the symbols written by the program.
-/

noncomputable section

namespace LeanTrominoes.TM2FiniteAlphabetRestriction

open Turing StateTransition

section Statements

variable {K : Type} {Γ : K → Type} {Λ σ : Type}

/-- Symbols that any push in this statement can write, over all control states. -/
def writtenSymbols [Fintype σ] (statement : TM2.Stmt Γ Λ σ) : Finset (Sigma Γ) := by
  classical
  exact match statement with
  | .push stack write next =>
      Finset.univ.image (fun state => ⟨stack, write state⟩) ∪ writtenSymbols next
  | .peek _ _ next | .pop _ _ next | .load _ next => writtenSymbols next
  | .branch _ yes no => writtenSymbols yes ∪ writtenSymbols no
  | .goto _ | .halt => ∅

/-- Every possible write belongs to the designated stack alphabet. -/
def WritesWithin (allowed : ∀ stack, Γ stack → Prop) : TM2.Stmt Γ Λ σ → Prop
  | .push stack write next =>
      (∀ state, allowed stack (write state)) ∧ WritesWithin allowed next
  | .peek _ _ next | .pop _ _ next | .load _ next => WritesWithin allowed next
  | .branch _ yes no => WritesWithin allowed yes ∧ WritesWithin allowed no
  | .goto _ | .halt => True

theorem writesWithin_of_writtenSymbols [Fintype σ]
    (allowed : ∀ stack, Γ stack → Prop) (statement : TM2.Stmt Γ Λ σ)
    (includes : ∀ symbol ∈ writtenSymbols statement, allowed symbol.1 symbol.2) :
    WritesWithin allowed statement := by
  classical
  induction statement with
  | push stack write next ih =>
      exact ⟨fun state => includes ⟨stack, write state⟩ (by simp [writtenSymbols]),
        ih (fun symbol member => includes symbol (by simp [writtenSymbols, member]))⟩
  | peek stack read next ih => exact ih includes
  | pop stack read next ih => exact ih includes
  | load update next ih => exact ih includes
  | branch test yes no yesIH noIH =>
      exact ⟨yesIH (fun symbol member => includes symbol (by simp [writtenSymbols, member])),
        noIH (fun symbol member => includes symbol (by simp [writtenSymbols, member]))⟩
  | goto target => trivial
  | halt => trivial

/-- Replace stack symbols by subtypes, retaining the original control flow. -/
def restrictStmt (allowed : ∀ stack, Γ stack → Prop) :
    (statement : TM2.Stmt Γ Λ σ) → WritesWithin allowed statement →
      TM2.Stmt (fun stack => {symbol // allowed stack symbol}) Λ σ
  | .push stack write next, supported =>
      .push stack (fun state => ⟨write state, supported.1 state⟩)
        (restrictStmt allowed next supported.2)
  | .peek stack read next, supported =>
      .peek stack (fun state symbol => read state (symbol.map Subtype.val))
        (restrictStmt allowed next supported)
  | .pop stack read next, supported =>
      .pop stack (fun state symbol => read state (symbol.map Subtype.val))
        (restrictStmt allowed next supported)
  | .load update next, supported => .load update (restrictStmt allowed next supported)
  | .branch test yes no, supported =>
      .branch test (restrictStmt allowed yes supported.1) (restrictStmt allowed no supported.2)
  | .goto target, _ => .goto target
  | .halt, _ => .halt

def eraseCfg {allowed : ∀ stack, Γ stack → Prop}
    (cfg : TM2.Cfg (fun stack => {symbol // allowed stack symbol}) Λ σ) :
    TM2.Cfg Γ Λ σ :=
  ⟨cfg.l, cfg.var, fun stack => (cfg.stk stack).map Subtype.val⟩

theorem eraseCfg_injective (allowed : ∀ stack, Γ stack → Prop) :
    Function.Injective (@eraseCfg K Γ Λ σ allowed) := by
  intro first second equal
  cases first with
  | mk firstLabel firstState firstStacks =>
    cases second with
    | mk secondLabel secondState secondStacks =>
      simp only [eraseCfg, TM2.Cfg.mk.injEq] at equal
      obtain ⟨rfl, rfl, stacksEqual⟩ := equal
      congr 1
      funext stack
      exact Subtype.val_injective.list_map (congrFun stacksEqual stack)

private theorem eraseStacks_update [DecidableEq K]
    (allowed : ∀ stack, Γ stack → Prop)
    (stackContents : ∀ stack, List {symbol // allowed stack symbol})
    (stack : K) (value : List {symbol // allowed stack symbol}) :
    (fun other => (Function.update stackContents stack value other).map Subtype.val) =
      Function.update (fun other => (stackContents other).map Subtype.val)
        stack (value.map Subtype.val) := by
  funext other
  by_cases equal : other = stack
  · subst other; simp
  · simp [Function.update_of_ne equal]

theorem eraseCfg_stepAux [DecidableEq K]
    (allowed : ∀ stack, Γ stack → Prop)
    (statement : TM2.Stmt Γ Λ σ) (supported : WritesWithin allowed statement)
    (state : σ) (stackContents : ∀ stack, List {symbol // allowed stack symbol}) :
    eraseCfg (TM2.stepAux (restrictStmt allowed statement supported) state stackContents) =
      TM2.stepAux statement state (fun stack => (stackContents stack).map Subtype.val) := by
  induction statement generalizing state stackContents with
  | push stack write next ih =>
      simpa only [restrictStmt, TM2.stepAux, eraseStacks_update, List.map_cons] using
        ih supported.2 state (Function.update stackContents stack (⟨write state, supported.1 state⟩ :: stackContents stack))
  | peek stack read next ih =>
      simpa only [restrictStmt, TM2.stepAux, List.head?_map] using
        ih supported (read state ((stackContents stack).head?.map Subtype.val)) stackContents
  | pop stack read next ih =>
      simpa only [restrictStmt, TM2.stepAux, List.head?_map, eraseStacks_update,
        List.map_tail] using
        ih supported (read state ((stackContents stack).head?.map Subtype.val))
          (Function.update stackContents stack (stackContents stack).tail)
  | load update next ih => exact ih supported (update state) stackContents
  | branch test yes no yesIH noIH =>
      cases decision : test state <;>
        simp only [restrictStmt, TM2.stepAux, decision]
      · exact noIH supported.2 state stackContents
      · exact yesIH supported.1 state stackContents
  | goto target => rfl
  | halt => rfl

end Statements

attribute [local instance] FinTM2.kDecidableEq FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

def programSymbols (tm : FinTM2) : Finset (Sigma tm.Γ) := by
  classical
  exact Finset.univ.biUnion (fun label => writtenSymbols (tm.m label))

def Allowed (tm : FinTM2) (stack : tm.K) (symbol : tm.Γ stack) : Prop :=
  stack = tm.k₀ ∨ stack = tm.k₁ ∨ ⟨stack, symbol⟩ ∈ programSymbols tm

theorem program_supported (tm : FinTM2) (label : tm.Λ) :
    WritesWithin (Allowed tm) (tm.m label) := by
  apply writesWithin_of_writtenSymbols
  intro symbol member
  exact Or.inr (Or.inr (by classical exact Finset.mem_biUnion.mpr ⟨label, Finset.mem_univ _, member⟩))

instance alphabetFinite (tm : FinTM2) [Finite (tm.Γ tm.k₁)] (stack : tm.K) :
    Finite {symbol // Allowed tm stack symbol} := by
  classical
  by_cases input : stack = tm.k₀
  · subst stack
    letI := tm.Γk₀Fin
    infer_instance
  by_cases output : stack = tm.k₁
  · subst stack; infer_instance
  apply Finite.of_injective
    (fun symbol : {symbol // Allowed tm stack symbol} =>
      (⟨⟨stack, symbol.val⟩, symbol.property.resolve_left input |>.resolve_left output⟩ :
        {symbol // symbol ∈ programSymbols tm}))
  intro first second equal
  exact Subtype.ext (by simpa using congrArg (fun symbol => symbol.val) equal)

abbrev machine (tm : FinTM2) [Finite (tm.Γ tm.k₁)] : FinTM2 where
  K := tm.K
  k₀ := tm.k₀
  k₁ := tm.k₁
  Γ stack := {symbol // Allowed tm stack symbol}
  Γk₀Fin := Fintype.ofFinite _
  Λ := tm.Λ
  main := tm.main
  σ := tm.σ
  initialState := tm.initialState
  m label := restrictStmt (Allowed tm) (tm.m label) (program_supported tm label)

/-- The external alphabets are preserved exactly, including when the two
external stacks coincide. -/
def externalEquiv (tm : FinTM2) (stack : tm.K)
    (external : stack = tm.k₀ ∨ stack = tm.k₁) :
    {symbol // Allowed tm stack symbol} ≃ tm.Γ stack where
  toFun := Subtype.val
  invFun symbol := ⟨symbol, external.elim Or.inl (fun equal => Or.inr (Or.inl equal))⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem eraseCfg_step (tm : FinTM2) [Finite (tm.Γ tm.k₁)]
    (cfg : (machine tm).Cfg) :
    Option.map eraseCfg ((machine tm).step cfg) = tm.step (eraseCfg cfg) := by
  cases cfg with
  | mk label state stackContents =>
    cases label with
    | none => rfl
    | some label =>
      exact congrArg some (eraseCfg_stepAux (Allowed tm) (tm.m label)
        (program_supported tm label) state stackContents)

theorem eraseCfg_initList (tm : FinTM2) [Finite (tm.Γ tm.k₁)]
    (input : List (tm.Γ tm.k₀)) :
    eraseCfg (initList (machine tm)
      (input.map (externalEquiv tm tm.k₀ (Or.inl rfl)).symm)) = initList tm input := by
  change TM2.Cfg.mk _ _ _ = TM2.Cfg.mk _ _ _
  congr 1
  funext stack
  by_cases equal : stack = tm.k₀
  · subst stack
    simp [initList, machine, externalEquiv, List.map_map, Function.comp_def]
  · simp [initList, machine, equal]

theorem eraseCfg_haltList (tm : FinTM2) [Finite (tm.Γ tm.k₁)]
    (output : List (tm.Γ tm.k₁)) :
    eraseCfg (haltList (machine tm)
      (output.map (externalEquiv tm tm.k₁ (Or.inr rfl)).symm)) = haltList tm output := by
  change TM2.Cfg.mk _ _ _ = TM2.Cfg.mk _ _ _
  congr 1
  funext stack
  by_cases equal : stack = tm.k₁
  · subst stack
    simp [haltList, machine, externalEquiv, List.map_map, Function.comp_def]
  · simp [haltList, machine, equal]

/-- Alphabet restriction preserves the exact number of machine steps. -/
def outputsInTime (tm : FinTM2) [Finite (tm.Γ tm.k₁)]
    (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (time : Nat)
    (run : TM2OutputsInTime tm input (some output) time) :
    TM2OutputsInTime (machine tm)
      (input.map (externalEquiv tm tm.k₀ (Or.inl rfl)).symm)
      (some (output.map (externalEquiv tm tm.k₁ (Or.inr rfl)).symm)) time := by
  have commute : Function.Semiconj (Option.map (@eraseCfg tm.K tm.Γ tm.Λ tm.σ (Allowed tm)))
      (fun cfg => cfg.bind (machine tm).step) (fun cfg => cfg.bind tm.step) := by
    intro cfg
    cases cfg with
    | none => rfl
    | some cfg => exact eraseCfg_step tm cfg
  refine ⟨⟨run.steps, ?_⟩, run.steps_le_m⟩
  apply Option.map_injective (eraseCfg_injective (Allowed tm))
  change Option.map eraseCfg ((fun cfg => cfg.bind (machine tm).step)^[run.steps]
      (some (initList (machine tm)
        (input.map (externalEquiv tm tm.k₀ (Or.inl rfl)).symm)))) =
    Option.map eraseCfg (some (haltList (machine tm)
      (output.map (externalEquiv tm tm.k₁ (Or.inr rfl)).symm)))
  rw [commute.iterate_right run.steps]
  simp only [Option.map_some]
  rw [eraseCfg_initList tm input, eraseCfg_haltList tm output]
  exact run.evals_in_steps

end LeanTrominoes.TM2FiniteAlphabetRestriction

end
