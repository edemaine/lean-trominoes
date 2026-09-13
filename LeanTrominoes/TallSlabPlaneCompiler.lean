/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55CompilerComputability
import LeanTrominoes.KeyedComplementRepeatMask

/-! # Compile a larger keyed period around the same periodic source -/

namespace LeanTrominoes.TwoConnectedPolycubes.TallSlabCompiler

abbrev Input := Theorem55Compiler.Input

def period (height : Nat) (input : Input) : Nat := (height+1)*(3*input.1)

def planeCompile (height : Nat) (input : Input) : List Cell :=
  ((Theorem55Compiler.squareList (period height input)).filter
    (fun c => !Theorem55Compiler.refinedContains input c)).map
      (KeyedPeriodicComplement.repack (period height input))

def compiledHoles (height : Nat) (input : Input) : Polyomino :=
  (KeyedPeriodicComplement.square (period height input)).filter
    (fun c => Theorem55Compiler.refinedContains input c = true)

theorem planeCompile_eq_tile (height : Nat) (input : Input) :
    (planeCompile height input).toFinset =
      KeyedPeriodicComplement.tile (period height input) (compiledHoles height input) := by
  have background : ((Theorem55Compiler.squareList (period height input)).filter
      (fun c => !Theorem55Compiler.refinedContains input c)).toFinset =
      KeyedPeriodicComplement.background (period height input) (compiledHoles height input) := by
    ext c
    simp only [KeyedPeriodicComplement.background,compiledHoles,Finset.mem_sdiff,Finset.mem_filter,
      ← Theorem55Compiler.squareList_toFinset,List.mem_toFinset,List.mem_filter]
    cases Theorem55Compiler.refinedContains input c <;> simp
  ext c
  simp only [planeCompile,List.mem_toFinset,List.mem_map,KeyedPeriodicComplement.tile,
    Finset.mem_image,← background,List.mem_toFinset]

theorem compiledHoles_eq_repeatMask (height : Nat) (input : Input) (holes : Polyomino)
    (membership : ∀ c, Theorem55Compiler.refinedContains input c = true ↔
      c ∈ KeyedPeriodicComplement.holesRegion (3*input.1) holes) :
    compiledHoles height input = KeyedPeriodicComplement.repeatMask (height+1) (3*input.1) holes := by
  ext c
  simp only [compiledHoles,KeyedPeriodicComplement.repeatMask,Finset.mem_filter,period,
    membership,KeyedPeriodicComplement.holesRegion,Set.mem_setOf_eq]

theorem compiledHoles_source (height : Nat) {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    compiledHoles height (Theorem55Compiler.sourceInput presentation) =
      KeyedPeriodicComplement.repeatMask (height+1) (3*Theorem55Source.period presentation)
        (Theorem55Source.holes presentation) := by
  apply compiledHoles_eq_repeatMask
  intro c
  change Theorem55Compiler.refinedContains (Theorem55Compiler.sourceInput presentation) c = true ↔
    c ∈ KeyedPeriodicComplement.holesRegion (3*Theorem55Source.period presentation) (Theorem55Source.holes presentation)
  rw [Theorem55Compiler.refinedContains_source,Theorem55Source.holes_carrier]

theorem period_primrec (height : Nat) : Primrec (period height) :=
  Primrec.nat_mul.comp (Primrec.const (height+1))
    (Primrec.nat_mul.comp (Primrec.const 3) Primrec.fst)

theorem planeCompile_primrec (height : Nat) : Primrec (planeCompile height) := by
  have keep : PrimrecRel (fun (c : Cell) (a : Input) => (!Theorem55Compiler.refinedContains a c) = true) := by
    apply (Primrec.eq.comp₂ Theorem55Compiler.refinedContains_primrec.swap (Primrec₂.const true)).not.of_eq
    intro c a
    change (¬ Theorem55Compiler.refinedContains a c = true) ↔ (!Theorem55Compiler.refinedContains a c) = true
    cases Theorem55Compiler.refinedContains a c <;> decide
  have filtered : Primrec (fun a : Input => (Theorem55Compiler.squareList (period height a)).filter
      (fun c => !Theorem55Compiler.refinedContains a c)) := by
    apply (keep.listFilter.comp (Theorem55Compiler.squareList_primrec.comp (period_primrec height)) Primrec.id).of_eq
    intro a
    simp only [Bool.decide_coe,id_eq]
  exact Primrec.list_map filtered
    (Theorem55Compiler.repack_primrec.comp₂ ((period_primrec height).comp₂ Primrec₂.left) Primrec₂.right)

end LeanTrominoes.TwoConnectedPolycubes.TallSlabCompiler
