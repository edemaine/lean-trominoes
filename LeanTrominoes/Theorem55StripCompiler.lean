/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55StripGeometry
import LeanTrominoes.Theorem55Compiler

/-! # An executable two-tile compiler for arbitrary periodic-strip sources -/

namespace LeanTrominoes.Theorem55StripCompiler

instance paddingMembershipDecidable (n : Nat) (c : Cell) :
    Decidable (c ∈ StripTrominoPadding.region n) :=
  inferInstanceAs (Decidable ((_ ∨ _) ∧ _ ∧ _))

def preparedContains (source : PeriodicStrip) (c : Cell) : Bool :=
  source.contains (Cell.add (0,-10) c) ||
    decide (c ∈ StripTrominoPadding.region (Theorem55StripSource.period source))

def refinedContains (source : PeriodicStrip) (c : Cell) : Bool :=
  preparedContains source (PlusRefinement.parent c) && decide (PlusRefinement.subcell c ∈ PlusRefinement.cross)

/-- Enumerate the complement and transfer only the horizontal key. -/
def tileCells (source : PeriodicStrip) : List Cell :=
  ((Theorem55Compiler.squareList (3 * Theorem55StripSource.period source)).filter
    (fun c => !refinedContains source c)).map (KeyedStripComplement.repack (3 * Theorem55StripSource.period source))

/-- Malformed source presentations map to a rejected target instance. -/
def compile (source : PeriodicStrip) : Theorem55.StripInput :=
  if source.IsWellFormed then (3 * Theorem55StripSource.period source,tileCells source) else (0,[])

theorem preparedContains_correct (source : PeriodicStrip) (c : Cell) :
    preparedContains source c = true ↔ c ∈ Theorem55StripSource.region source := by
  simp only [preparedContains,Bool.or_eq_true,decide_eq_true_eq,PeriodicStrip.contains_eq_true_iff]
  rfl

theorem refinedContains_correct (source : PeriodicStrip) (c : Cell) :
    refinedContains source c = true ↔ c ∈ PlusRefinement.region (Theorem55StripSource.region source) := by
  rw [PlusRefinement.mem_region_iff]
  simp only [refinedContains,Bool.and_eq_true,decide_eq_true_eq,preparedContains_correct]

theorem tileCells_correct (source : PeriodicStrip) :
    (tileCells source).toFinset = KeyedStripComplement.tile (3 * Theorem55StripSource.period source)
      (Theorem55StripSource.holes source) := by
  have background :
      ((Theorem55Compiler.squareList (3 * Theorem55StripSource.period source)).filter
        (fun c => !refinedContains source c)).toFinset =
      KeyedPeriodicComplement.background (3 * Theorem55StripSource.period source)
        (Theorem55StripSource.holes source) := by
    ext c
    simp only [KeyedPeriodicComplement.background,Finset.mem_sdiff,Theorem55StripSource.holes,
      KeyedPeriodicComplement.mem_mask, ← Theorem55Compiler.squareList_toFinset,
      List.mem_toFinset,List.mem_filter, ← refinedContains_correct]
    cases refinedContains source c <;> simp
  ext c
  simp only [tileCells,List.mem_toFinset,List.mem_map,KeyedStripComplement.tile,
    Finset.mem_image, ← background,List.mem_toFinset]

theorem compile_correct (source : PeriodicStrip) :
    Theorem55.stripProblem (compile source) ↔ PeriodicStripTrominoTiling .I source := by
  by_cases valid : source.IsWellFormed
  · simp only [compile,PeriodicStripTrominoTiling,valid,true_and]
    exact Theorem55StripSource.stripProblem_iff source valid.2.1 _ (tileCells_correct source)
  · simp [compile,valid,Theorem55.stripProblem,PeriodicStripTrominoTiling]

end LeanTrominoes.Theorem55StripCompiler
