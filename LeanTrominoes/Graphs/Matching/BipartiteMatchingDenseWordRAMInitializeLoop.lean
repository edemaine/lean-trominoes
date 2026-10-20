/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMInitializeRepresentation

/-! # Complete bounded-word execution of search-root initialization -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM

theorem initializeLoop_exec {B : Nat} (input : Input)
    (matching : State (Fin input.1) (Fin input.2.1)) (remaining : Nat)
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d) (pathBound : PathsBound input paths)
    (bounded : NaturalData.Bounded B d) (room : (Layout.ofInput input).frontier≤B)
    (enough : d.1 Reg.index+remaining=input.1)
    (done : ∀ l : Fin input.1, l.val<d.1 Reg.index → paths l=DenseSearch.initial matching l) :
    ∃ result cost, Natural.Exec B (.loop (.lt Reg.index Reg.n) initializeBody) d result cost ∧
      cost≤9*remaining+2 ∧ Representation input matching (DenseSearch.initial matching) result ∧
      NaturalData.Bounded B result ∧ result.1 Reg.index=input.1 := by
  induction remaining generalizing d paths with
  | zero =>
    have index : d.1 Reg.index=input.1 := by omega
    have same : paths=DenseSearch.initial matching := by
      funext l
      exact done l (by rw [index]; exact l.isLt)
    subst paths
    refine ⟨d,2,Natural.Exec.loop_done ?_,by omega,rep,bounded,index⟩
    simp only [Natural.Holds,rep.n,index,lt_self_iff_false,not_false_eq_true]
  | succ remaining ih =>
    have inside : d.1 Reg.index< input.1 := by omega
    let l : Fin input.1 := ⟨d.1 Reg.index,inside⟩
    have nBound : input.1≤(Layout.ofInput input).frontier := by
      dsimp [Layout.ofInput,Layout.frontier]
      omega
    have leftPtr := rep.pointers Slot.partnerLeft
    have lengthPtr := rep.pointers Slot.lengths
    change d.1 Reg.partnerLeft=(Layout.ofInput input).base Slot.partnerLeft at leftPtr
    change d.1 Reg.lengths=(Layout.ofInput input).base Slot.lengths at lengthPtr
    have first := initializeBody_exec d bounded
      (by rw [leftPtr]; exact ((Layout.ofInput input).address_bound Slot.partnerLeft l.val l.isLt).le.trans room)
      (by rw [lengthPtr]; exact ((Layout.ofInput input).address_bound Slot.lengths l.val l.isLt).le.trans room)
      (by rw [rep.one]; exact (show d.1 Reg.index+1≤ input.1 by omega).trans (nBound.trans room))
    have nextRep := initializeState_represents input matching paths d rep pathBound l rfl
    have nextBound := PathsBound.update_empty input paths pathBound l (DenseSearch.initial matching l)
      (initial_path_empty input matching l)
    have nextDone : ∀ a : Fin input.1, a.val<(initializeState d).1 Reg.index →
        Function.update paths l (DenseSearch.initial matching l) a=DenseSearch.initial matching a := by
      intro a marked
      rw [initializeState_index,rep.one] at marked
      by_cases same : a=l
      · subst a; simp
      · have different : a.val≠d.1 Reg.index := by intro eq; exact same (Fin.ext eq)
        rw [Function.update_of_ne same]
        exact done a (by omega)
    obtain ⟨result,cost,later,budget,finalRep,finalBound,finalIndex⟩ := ih _ _ nextRep nextBound (first.bounded bounded)
      (by rw [initializeState_index,rep.one]; omega) nextDone
    refine ⟨result,initializeCost d+cost+2,Natural.Exec.loop_more ?_ first later,?_,finalRep,finalBound,finalIndex⟩
    · simpa only [Natural.Holds,rep.n] using inside
    · have bodyBudget := initializeCost_bound d
      omega

theorem initial_paths_bound (input : Input) (matching : State (Fin input.1) (Fin input.2.1)) :
    PathsBound input (DenseSearch.initial matching) := by
  intro l prior marked
  rw [initial_path_empty input matching l prior marked]
  simp

/-- The entire search-root pass, including its initial counter assignment,
uses at most `9*n+3` primitive instructions. -/
theorem initializeSearch_exec {B : Nat} (input : Input)
    (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d) (pathBound : PathsBound input paths)
    (bounded : NaturalData.Bounded B d) (room : (Layout.ofInput input).frontier≤B) :
    ∃ result cost, Natural.Exec B initializeSearch d result cost ∧ cost≤9*input.1+3 ∧
      Representation input matching (DenseSearch.initial matching) result ∧ NaturalData.Bounded B result := by
  have first : Natural.Exec B (constant Reg.index 0) d (d.set Reg.index 0) 1 :=
    Natural.Exec.atom (Natural.Step.constant d Reg.index 0 (Nat.zero_le B))
  have startRep := rep.set_scalar input matching paths d Reg.index 0
    (scalarRegister_of_large _ (by decide)) (by decide)
  obtain ⟨result,cost,later,budget,finalRep,finalBound,_⟩ := initializeLoop_exec input matching input.1 paths
    (d.set Reg.index 0) startRep pathBound (first.bounded bounded) room (by simp [NaturalData.set])
    (by intro l marked; simp [NaturalData.set] at marked)
  exact ⟨result,1+cost,first.seq later,by omega,finalRep,finalBound⟩

end LeanTrominoes.BipartiteMatching.DenseWordRAM
