/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.NormalizedOrientationBoundedPreparation
import LeanTrominoes.UnaryColumnFieldLookup

/-! # A polynomially bounded drawing reconstructed from arbitrary binary input

Well-formed encoded drawings are unchanged. On arbitrary input, dimensions and
cell values come from the bounded decoder, so rendering the full table cannot
expand an enormous binary count into an enormous unary object.
-/
noncomputable section
namespace LeanTrominoes.Gadget.NormalizedOrientation.SafePreparation
open Turing UnaryColumn PeriodicOrthogonalDrawing FlatEncoding
abbrev Symbol := PeriodicCNFFlatEncoding.Symbol

def value (s : List Symbol) (index : Nat) : Nat := (BoundedPreparation.prepare s).getD index 0

def safeCell (n : Nat) : OrthogonalCellType :=
  (decodeCell ((n-1)%BoundedPreparation.cellBound)).getD .blank

theorem safeCell_code (c : OrthogonalCellType) : safeCell (cellCode c+1) = c := by
  simp [safeCell,Nat.mod_eq_of_lt (BoundedPreparation.cellCode_lt c)]

def drawing (s : List Symbol) : PeriodicOrthogonalDrawing where
  horizontalPeriodPred := value s 0-2
  verticalPeriodPred := value s 1-2
  cellTypes := (List.range ((value s 0-2+1)*(value s 1-2+1))).map
    (fun n => safeCell (value s (n+2)))

theorem value_encoded (d : PeriodicOrthogonalDrawing) (wf : d.IsWellFormed)
    (n : Nat) (hn : n < (fields d).length) : value (finEncoding.encode d) n = (fields d).getD n 0+1 := by
  rw [value,BoundedPreparation.prepare_encoded d wf]
  rw [List.getD_eq_getElem _ _ (by simp; omega),List.getElem_append_left (by simpa using hn),
    List.getElem_map,List.getD_eq_getElem _ _ hn]

theorem drawing_encoded (d : PeriodicOrthogonalDrawing) (wf : d.IsWellFormed) :
    drawing (finEncoding.encode d) = d := by
  have hw := value_encoded d wf 0 (by simp [fields])
  have hh := value_encoded d wf 1 (by simp [fields])
  have wp : value (finEncoding.encode d) 0-2 = d.horizontalPeriodPred := by
    simp only [fields,List.getD_cons_zero,horizontalPeriod] at hw
    omega
  have hp : value (finEncoding.encode d) 1-2 = d.verticalPeriodPred := by
    simp only [fields,List.getD_cons_succ,List.getD_cons_zero,verticalPeriod] at hh
    omega
  have cells : (drawing (finEncoding.encode d)).cellTypes = d.cellTypes := by
    change (List.range ((value (finEncoding.encode d) 0-2+1)*(value (finEncoding.encode d) 1-2+1))).map
      (fun n => safeCell (value (finEncoding.encode d) (n+2))) = d.cellTypes
    rw [wp,hp,← wf.1]
    apply List.ext_getElem
    · simp
    · intro n hn hm
      simp only [List.getElem_map,List.getElem_range]
      have bound : n+2 < (fields d).length := by simp [fields]; omega
      have atField : (fields d).getD (n+2) 0 = cellCode d.cellTypes[n] := by
        rw [List.getD_eq_getElem _ _ bound]
        simp only [fields,List.getElem_cons_succ,List.getElem_map]
      rw [value_encoded d wf (n+2) bound,atField,safeCell_code]
  have extensional (a b : PeriodicOrthogonalDrawing)
      (hw : a.horizontalPeriodPred = b.horizontalPeriodPred)
      (hh : a.verticalPeriodPred = b.verticalPeriodPred)
      (hc : a.cellTypes = b.cellTypes) : a = b := by
    cases a
    cases b
    cases hw
    cases hh
    cases hc
    rfl
  exact extensional (drawing (finEncoding.encode d)) d wp hp cells

def valueCompiler (index : Nat) : ScalarCompiler (fun s => value s index) := by
  have query : Compiler (fun _ : List Symbol => [()]) (fun _ _ => index) :=
    TM2ConstantValueCompiler.computableInPolyTime id UnaryFieldEncoderMachine.unaryFields [index]
  exact fieldLookup query BoundedPreparation.compiler

def dimensionCompiler (index : Nat) : ScalarCompiler (fun s => value s index-2+1) := by
  let raw : Compiler (fun _ : List Symbol => [()]) (fun s _ => value s index) := valueCompiler index
  exact add (sub raw (constant raw 2)) (constant raw 1)

def widthCompiler : ScalarCompiler (fun s => (drawing s).horizontalPeriod) := dimensionCompiler 0

def heightCompiler : ScalarCompiler (fun s => (drawing s).verticalPeriod) := dimensionCompiler 1

end LeanTrominoes.Gadget.NormalizedOrientation.SafePreparation
end
