/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FixedPolyominoSeedReduction
import LeanTrominoes.FixedPolyominoSeedReverse

/-! # Corollary 5.7: finite-seed completion by two fixed polyominoes is co-r.e. complete -/
noncomputable section
set_option synthInstance.maxSize 2048
namespace LeanTrominoes.FixedPolyominoSeed
open LeanWang PlusRefinement Gadget KeyedPeriodicComplement PeriodicCNF.SignedDecoder
local instance : DecidableEq FinalVariable := PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
local instance : DecidableEq PolarityVariable := inferInstanceAs (DecidableEq (FinalVariable ⊕ _))
attribute [local irreducible] BooleanTransport.middleSeed BooleanTransport.matchingSeed

theorem reduction_reverse (code : Nat.Partrec.Code) (completed : Problem (reduction code)) :
    ¬ (Nat.Partrec.Code.eval code 0).Dom := by
  by_cases consistent : Consistent (BooleanTransport.middleSeed code)
  · rw [reduction,if_pos consistent] at completed
    obtain ⟨ps,tiling,retained⟩ := (VertexEncoding.problem_iff _).1 completed
    exact BooleanTransport.reverse code consistent ps tiling
      (retained referencePlacement List.mem_cons_self)
      (fun p member => retained p (List.mem_cons_of_mem _ member))
  · rw [reduction,if_neg consistent] at completed
    exact False.elim (impossibleSeed_not_completed completed)

theorem reduction_correct (code : Nat.Partrec.Code) :
    Problem (reduction code) ↔ ¬ (Nat.Partrec.Code.eval code 0).Dom :=
  ⟨reduction_reverse code,reduction_forward code⟩

theorem coREHard : CoREHard Problem := by
  intro A _ predicate hs
  obtain ⟨reduce,computed,correct⟩ := coRE_manyOneReducible_fixedNonhalting predicate hs
  exact ⟨reduction ∘ reduce,reduction_computable.comp computed,
    fun a => (correct a).trans (reduction_correct (reduce a)).symm⟩

theorem coREComplete : CoREComplete Problem := ⟨coRE,coREHard⟩

theorem corollary57 : ∃ p q : Polyomino,
    p.card = 15 ∧ p.IsConnected ∧ q.Nonempty ∧
      CoREComplete (FinitePolyominoCompletion.fixedProblem p.toList q.toList) :=
  ⟨smallTile,largeTile,smallTile_properties.1,smallTile_properties.2,largeTile_nonempty,coREComplete⟩

open Lean Elab Command in
run_cmd do
  for name in [``reduction_correct,``reduction_computable,``coREComplete,``corollary57] do
    let axioms ← Lean.collectAxioms name
    let extra := axioms.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.FixedPolyominoSeed
