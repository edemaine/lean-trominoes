/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteNPTableauEncoding
import LeanTrominoes.PeriodicCNFPolySpaceRequestPadding
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2ComputableInPolyTimeCongr
import LeanTrominoes.UnaryFieldUnitLengthBroadcastCompiler

/-! # Polynomial-time source and counter preparation for the finite compiler -/
noncomputable section
namespace LeanTrominoes.FiniteNPCompilerPreparation
open Computability Turing
open UnaryPolynomialPaddingMachine
open PeriodicCNF.PolySpaceRequestPadding (polynomialCoefficients)

abbrev Symbol (Source : Type) := Source ⊕ Fin 4
instance {Source : Type} : Inhabited (Symbol Source) := ⟨.inr 0⟩

def isSource {Source : Type} : Symbol Source → Bool
  | .inl _ => true
  | .inr _ => false

def addCounter {Source : Type} (tag : Fin 4) (polynomial : Polynomial Nat)
    (word : List (Symbol Source)) : List (Symbol Source) :=
  word++List.replicate (polynomial.eval (selectedCount isSource word)) (.inr tag)

def retag {Source : Type} (tag : Fin 4) : Symbol Source ⊕ Unit → Symbol Source
  | .inl symbol => symbol
  | .inr _ => .inr tag

theorem map_paddedOutput {Source : Type} (tag : Fin 4) (polynomial : Polynomial Nat)
    (word : List (Symbol Source)) :
    (paddedOutput isSource (polynomialCoefficients polynomial) word).map (retag tag)=
      addCounter tag polynomial word := by
  simp [paddedOutput,addCounter,List.map_append,List.map_map,retag,Function.comp_def]

private theorem flatMap_singletons {A B : Type} (f : A → B) (word : List A) :
    word.flatMap (fun symbol => [f symbol])=word.map f := by
  induction word <;> simp_all

def addCounterComputableInPolyTime {Source : Type} [Fintype Source]
    (tag : Fin 4) (polynomial : Polynomial Nat) :
    TM2ComputableInPolyTime id id (addCounter (Source := Source) tag polynomial) := by
  let padded := UnaryPolynomialPaddingMachine.computableInPolyTime
    (Source := Symbol Source) isSource (polynomialCoefficients polynomial)
  let mapped := FiniteBlockTransducer.computableInPolyTime (fun symbol : Symbol Source ⊕ Unit => [retag tag symbol])
  exact TM2ComputableInPolyTime.of_eq
    (TM2CompositionMachine.computableInPolyTime padded mapped)
    (fun word => by simpa only [flatMap_singletons] using map_paddedOutput tag polynomial word)

@[simp] theorem selectedCount_mapSource {Source : Type} (word : List Source) :
    selectedCount isSource (word.map (Sum.inl : Source → Symbol Source))=word.length := by
  induction word <;> simp_all [selectedCount,isSource,Nat.add_comm]

@[simp] theorem selectedCount_replicateCounter {Source : Type} (tag : Fin 4) (count : Nat) :
    selectedCount isSource (List.replicate count (Sum.inr tag : Symbol Source))=0 := by
  induction count <;> simp_all [selectedCount,isSource,List.replicate_succ]

@[simp] theorem selectedCount_addCounter {Source : Type} (tag : Fin 4)
    (polynomial : Polynomial Nat) (word : List (Symbol Source)) :
    selectedCount isSource (addCounter tag polynomial word)=selectedCount isSource word := by
  unfold addCounter
  rw [PeriodicCNF.PolySpaceRequestPadding.selectedCount_append]
  simp


variable {Input : Type} {encoding : _root_.LeanTrominoes.FiniteEncoding Input} {language : Input → Prop}
variable (verifier : Complexity.VerifierInPolyTime encoding language)
open Complexity.VerifierInPolyTime

/-- Tags 0,1,2,3 mark certificate capacity, number of tableau slices, stack
space, and the per-slice source-plus-auxiliary variable bound. -/
def prepared (symbols : List encoding.Γ) : List (Symbol encoding.Γ) :=
  addCounter 3 (tableauSourcePolynomial verifier+tableauGatePolynomial verifier)
    (addCounter 2 (spacePolynomial verifier)
      (addCounter 1 (timePolynomial verifier+1)
        (addCounter 0 verifier.witnessBound (symbols.map Sum.inl))))

theorem prepared_eq (symbols : List encoding.Γ) : prepared verifier symbols=
    symbols.map Sum.inl++
      List.replicate (verifier.witnessBound.eval symbols.length) (.inr 0)++
      List.replicate ((timePolynomial verifier+1).eval symbols.length) (.inr 1)++
      List.replicate ((spacePolynomial verifier).eval symbols.length) (.inr 2)++
      List.replicate ((tableauSourcePolynomial verifier+tableauGatePolynomial verifier).eval symbols.length) (.inr 3) := by
  simp [prepared,addCounter,PeriodicCNF.PolySpaceRequestPadding.selectedCount_append]

def computableInPolyTime : TM2ComputableInPolyTime id id (prepared verifier) := by
  let source := FiniteBlockTransducer.computableInPolyTime
    (fun symbol : encoding.Γ => [(Sum.inl symbol : Symbol encoding.Γ)])
  let capacity := TM2CompositionMachine.computableInPolyTime source
    (addCounterComputableInPolyTime 0 verifier.witnessBound)
  let time := TM2CompositionMachine.computableInPolyTime capacity
    (addCounterComputableInPolyTime 1 (timePolynomial verifier+1))
  let space := TM2CompositionMachine.computableInPolyTime time
    (addCounterComputableInPolyTime 2 (spacePolynomial verifier))
  exact TM2ComputableInPolyTime.of_eq
    (TM2CompositionMachine.computableInPolyTime space
      (addCounterComputableInPolyTime 3 (tableauSourcePolynomial verifier+tableauGatePolynomial verifier)))
    (fun symbols => by simp [prepared,flatMap_singletons])

def sourceSymbol {Source : Type} : Symbol Source → Option Source
  | .inl symbol => some symbol
  | .inr _ => none

def sourceSymbols {Source : Type} (word : List (Symbol Source)) : List Source :=
  word.filterMap sourceSymbol

@[simp] theorem sourceSymbols_addCounter {Source : Type} (tag : Fin 4) (polynomial : Polynomial Nat)
    (word : List (Symbol Source)) : sourceSymbols (addCounter tag polynomial word)=sourceSymbols word := by
  simp [sourceSymbols,addCounter,sourceSymbol]

@[simp] theorem sourceSymbols_prepared (symbols : List encoding.Γ) :
    sourceSymbols (prepared verifier symbols)=symbols := by
  simp only [prepared,sourceSymbols_addCounter]
  simp [sourceSymbols,sourceSymbol]

def isCounter {Source : Type} (tag : Fin 4) : Symbol Source → Bool
  | .inl _ => false
  | .inr other => other==tag

def counterCount {Source : Type} (tag : Fin 4) (word : List (Symbol Source)) : Nat :=
  selectedCount (isCounter tag) word

def counterUnits {Source : Type} (tag : Fin 4) : Symbol Source → List Unit :=
  fun symbol => if isCounter tag symbol then [()] else []

theorem counterUnits_length {Source : Type} (tag : Fin 4) (word : List (Symbol Source)) :
    (word.flatMap (counterUnits tag)).length=counterCount tag word := by
  induction word with
  | nil => rfl
  | cons symbol word ih =>
    simp only [List.flatMap_cons,List.length_append,ih,counterCount,selectedCount_cons,counterUnits]
    split_ifs <;> simp

def counterComputableInPolyTime {Source : Type} [Fintype Source] (tag : Fin 4) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun word : List (Symbol Source) => [counterCount tag word]) := by
  let units := FiniteBlockTransducer.computableInPolyTime (counterUnits (Source := Source) tag)
  let counted := TM2CompositionMachine.computableInPolyTime units
    UnaryFieldUnitLengthBroadcast.singletonComputableInPolyTime
  exact TM2ComputableInPolyTime.of_eq counted
    (fun word => by simp only [counterUnits_length])

@[simp] theorem counterCount_sources {Source : Type} (tag : Fin 4) (symbols : List Source) :
    counterCount tag (symbols.map (Sum.inl : Source → Symbol Source))=0 := by
  induction symbols <;> simp_all [counterCount,selectedCount,isCounter]

@[simp] theorem counterCount_replicate {Source : Type} (tag other : Fin 4) (count : Nat) :
    counterCount tag (List.replicate count (.inr other : Symbol Source))=
      if other=tag then count else 0 := by
  by_cases same : other=tag
  · subst other
    induction count <;> simp_all [counterCount,selectedCount,isCounter,List.replicate_succ,Nat.add_comm]
  · induction count <;> simp_all [counterCount,selectedCount,isCounter,List.replicate_succ]

@[simp] theorem counterCount_append {Source : Type} (tag : Fin 4) (first second : List (Symbol Source)) :
    counterCount tag (first++second)=counterCount tag first+counterCount tag second :=
  PeriodicCNF.PolySpaceRequestPadding.selectedCount_append _ _ _

theorem counterCount_prepared (symbols : List encoding.Γ) (tag : Fin 4) :
    counterCount tag (prepared verifier symbols)=
      match tag.val with
      | 0 => verifier.witnessBound.eval symbols.length
      | 1 => (timePolynomial verifier+1).eval symbols.length
      | 2 => (spacePolynomial verifier).eval symbols.length
      | _ => (tableauSourcePolynomial verifier+tableauGatePolynomial verifier).eval symbols.length := by
  rw [prepared_eq]
  fin_cases tag <;> simp


end LeanTrominoes.FiniteNPCompilerPreparation
