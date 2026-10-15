/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientation
import Lean.Util.CollectAxioms

/-! # Effective CNF compilation of periodic graph orientations -/
namespace LeanTrominoes.TrichromaticGraphOrientation
open Gadget PeriodicOneInThree Computability
set_option maxHeartbeats 2000000

private theorem edge_data_primrec : Primrec (@PeriodicEdge.equivData Nat) := Primrec.of_equiv

theorem edgeEnds_primrec : Primrec edgeEnds := by
  let edge : Primrec (fun t : (PeriodicEdge Nat × WireColor) × Nat => t.1.1) :=
    Primrec.fst.comp Primrec.fst
  let source := Primrec.fst.comp (edge_data_primrec.comp edge)
  let target := Primrec.fst.comp (Primrec.snd.comp (edge_data_primrec.comp edge))
  let offset := Primrec.snd.comp (Primrec.snd.comp (edge_data_primrec.comp edge))
  let color : Primrec (fun t : (PeriodicEdge Nat × WireColor) × Nat => t.1.2) :=
    Primrec.snd.comp Primrec.fst
  have sourceLiteral : Primrec (fun t : (PeriodicEdge Nat × WireColor) × Nat =>
      (⟨t.2,(0,0),false⟩ : PeriodicLiteral Nat)) :=
    (PeriodicLiteral.equivData_symm_primrec.comp
      (Primrec.pair Primrec.snd (Primrec.const ((0,0),false)))).of_eq (fun _ => rfl)
  have targetLiteral : Primrec (fun t : (PeriodicEdge Nat × WireColor) × Nat =>
      (⟨t.2,Cell.sub (0,0) t.1.1.offset,true⟩ : PeriodicLiteral Nat)) :=
    (PeriodicLiteral.equivData_symm_primrec.comp
      (Primrec.pair Primrec.snd (Primrec.pair
        (cell_sub_primrec.comp (Primrec.const (0,0)) offset) (Primrec.const true)))).of_eq
      (fun _ => rfl)
  exact (Primrec.list_cons.comp (Primrec.pair source (Primrec.pair sourceLiteral color))
    (Primrec.list_cons.comp (Primrec.pair target (Primrec.pair targetLiteral color))
      (Primrec.const []))).of_eq (fun _ => rfl)

theorem ends_primrec : Primrec ends :=
  Primrec.list_flatMap (PeriodicThreeSATThree.zipIdx_primrec.comp Primrec.snd)
    (edgeEnds_primrec.comp Primrec.snd)

theorem endsAt_primrec : Primrec₂ endsAt := by
  have incidenceMatch : PrimrecRel fun (incidence : End) (v : Nat) => incidence.1 = v :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact incidenceMatch.listFilter.comp (ends_primrec.comp Primrec.fst) Primrec.snd

theorem incoming_primrec : Primrec₂ incoming :=
  Primrec.list_map endsAt_primrec (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))

theorem colors_primrec : Primrec₂ colors :=
  Primrec.list_map endsAt_primrec (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

theorem coherenceClauses_primrec : Primrec coherenceClauses := by
  have pair : Primrec₂ fun (l r : PeriodicLiteral Nat) => [negate l,r] :=
    Primrec.list_cons.comp (negate_primrec.comp Primrec.fst)
      (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
  exact Primrec.list_flatMap Primrec.id
    (Primrec.list_map Primrec.fst (pair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))

theorem vertexClauses_primrec : Primrec₂ vertexClauses := by
  have kind : Primrec₂ fun (input : Input) (v : Nat) => input.1.getD v false :=
    (Primrec.list_getD false).comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have exactOne : Primrec (@PeriodicExactOneCNF.clause Nat) :=
    Primrec.list_cons.comp Primrec.id PeriodicExactOneCNF.mutex_primrec
  apply (Primrec.cond kind (coherenceClauses_primrec.comp incoming_primrec)
    (exactOne.comp incoming_primrec)).of_eq
  intro p
  cases p.1.1.getD p.2 false <;> simp [vertexClauses]

theorem formula_primrec : Primrec formula := by
  exact (PeriodicCNF.equivData_symm_primrec.comp
    (Primrec.list_flatMap (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst))
      vertexClauses_primrec)).of_eq (fun _ => rfl)

private theorem edgeCheck_primrec : PrimrecRel fun (edge : PeriodicEdge Nat × WireColor) (input : Input) =>
    edge.1.source < input.1.length ∧ edge.1.target < input.1.length := by
  let edge : Primrec fun p : (PeriodicEdge Nat × WireColor) × Input =>
      PeriodicEdge.equivData p.1.1 :=
    edge_data_primrec.comp (Primrec.fst.comp Primrec.fst)
  let length : Primrec fun p : (PeriodicEdge Nat × WireColor) × Input => p.2.1.length :=
    Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)
  apply ((Primrec.nat_lt.comp (Primrec.fst.comp edge) length).and
    (Primrec.nat_lt.comp (Primrec.fst.comp (Primrec.snd.comp edge)) length)).of_eq
  intro p
  rfl

private theorem edgesCheck_primrec : PrimrecPred fun input : Input =>
    ∀ edge ∈ input.2, edge.1.source < input.1.length ∧ edge.1.target < input.1.length := by
  have listsCheck : PrimrecRel fun (edges : List (PeriodicEdge Nat × WireColor)) (input : Input) =>
      ∀ edge ∈ edges, edge.1.source < input.1.length ∧ edge.1.target < input.1.length :=
    edgeCheck_primrec.forall_mem_list
  exact listsCheck.comp (Primrec.snd : Primrec fun input : Input => input.2) Primrec.id

private theorem color_count_primrec : Primrec₂ fun (c : WireColor) (xs : List WireColor) =>
    xs.count c := by
  classical
  have step : Primrec₂ fun (p : WireColor × List WireColor) (q : WireColor × Nat) =>
      if q.1 = p.1 then q.2+1 else q.2 :=
    Primrec.ite
      (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
      (Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 1))
      (Primrec.snd.comp Primrec.snd)
  apply (Primrec.list_foldr Primrec.snd (Primrec.const 0) step).of_eq
  intro p
  induction p.2 with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldr_cons,List.count_cons]
      rw [ih]
      split <;> simp_all

theorem wellFormed_primrec : PrimrecPred IsWellFormed := by
  have countCheck (c : WireColor) : PrimrecPred fun p : Input × Nat =>
      (colors p.1 p.2).count c = 1 :=
    Primrec.eq.comp (color_count_primrec.comp (Primrec.const c) colors_primrec) (Primrec.const 1)
  have rainbow : PrimrecPred fun p : Input × Nat =>
      ∀ c : WireColor, (colors p.1 p.2).count c = 1 := by
    apply ((countCheck .red).and ((countCheck .green).and (countCheck .blue))).of_eq
    intro p
    constructor
    · rintro ⟨red,green,blue⟩ c; cases c <;> assumption
    · intro h; exact ⟨h .red,h .green,h .blue⟩
  have equalColor : PrimrecRel fun (c : WireColor) (p : Input × Nat) =>
      ∀ b ∈ colors p.1 p.2, b = c := by
    have computedColors : Primrec fun p : WireColor × (Input × Nat) => colors p.2.1 p.2.2 :=
      colors_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
    exact Primrec.eq.forall_mem_list.comp computedColors Primrec.fst
  have mono : PrimrecPred fun p : Input × Nat =>
      ∃ c : WireColor, ∀ b ∈ colors p.1 p.2, b = c := by
    apply (equalColor.exists_mem_list.comp (Primrec.const [.red,.green,.blue]) Primrec.id).of_eq
    intro p
    constructor
    · rintro ⟨c,_,h⟩; exact ⟨c,h⟩
    · rintro ⟨c,h⟩; refine ⟨c,?_,h⟩; cases c <;> simp
  have kind : PrimrecPred fun p : Input × Nat => p.1.1.getD p.2 false = true :=
    Primrec.eq.comp
      ((Primrec.list_getD false).comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (Primrec.const true)
  have vertexCheck : PrimrecPred fun p : Input × Nat =>
      (colors p.1 p.2).length = 3 ∧
        if p.1.1.getD p.2 false then ∀ c : WireColor, (colors p.1 p.2).count c = 1
        else ∃ c : WireColor, ∀ b ∈ colors p.1 p.2, b = c := by
    apply ((Primrec.eq.comp (Primrec.list_length.comp colors_primrec) (Primrec.const 3)).and
      ((kind.and rainbow).or (kind.not.and mono))).of_eq
    intro p
    cases p.1.1.getD p.2 false <;> simp
  have verticesCheck : PrimrecPred fun input : Input =>
      ∀ v < input.1.length,
        (colors input v).length = 3 ∧
          if input.1.getD v false then ∀ c : WireColor, (colors input v).count c = 1
          else ∃ c : WireColor, ∀ b ∈ colors input v, b = c := by
    exact (vertexCheck.primrecRel.swap.forall_mem_list.comp
      (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst)) Primrec.id).of_eq
      (fun _ => by simp)
  apply (edgesCheck_primrec.and verticesCheck).of_eq
  intro input
  rfl

/-- This upper bound applies to every periodic colored graph, independently
of dimension-two planarity or any chosen drawing. -/
theorem hasOrientation_coRE : LeanWang.CoREPred HasOrientation := by
  have upper := LeanWang.REPred.comp (PeriodicCNF.satisfiable_coRE (V := Nat))
    formula_primrec.to_comp
  exact upper.of_eq fun input => not_congr (formula_satisfiable_iff input)

/-- Invalid graph records are rejected, rather than treated as a promise. -/
theorem problem_coRE : LeanWang.CoREPred Problem := by
  have obstruction := LeanWang.REPred.exists_nat
    (p := fun input r => ¬ (IsWellFormed input ∧
      PeriodicCNF.FiniteSearch.Check (PeriodicCNF.FiniteSearch.instantiate (formula input) r)))
    ((wellFormed_primrec.comp Primrec.fst).and
      (PeriodicCNF.FiniteSearch.check_primrec.comp
        (PeriodicCNF.FiniteSearch.instantiate_primrec.comp
          (formula_primrec.comp Primrec.fst) Primrec.snd))).not.computablePred
  exact obstruction.of_eq fun input => by
    rw [← not_forall]
    apply not_congr
    simp only [forall_and,forall_const,← PeriodicCNF.FiniteSearch.satisfiable_iff,
      formula_satisfiable_iff,Problem]

open Lean Elab Command in
run_cmd do
  let name := ``problem_coRE
  let axioms ← Lean.collectAxioms name
  let extra := axioms.filter fun ax =>
    ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
  unless extra.isEmpty do
    throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.TrichromaticGraphOrientation
