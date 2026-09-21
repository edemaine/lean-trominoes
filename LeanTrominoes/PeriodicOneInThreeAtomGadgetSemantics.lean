/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOneInThreeAtomDescriptors

/-! # Atom descriptors agree with the numeric clause gadget -/
namespace LeanTrominoes.PeriodicOneInThree.AtomDescriptors
open PeriodicCNF.UnaryProgramClauseProfile
set_option maxHeartbeats 1000000

noncomputable def clauseAtoms (source : PeriodicCNF Nat) (i : Nat) (c : PeriodicClause Nat) : List Nat :=
  (clauseClauses i c).flatMap (fun clause => clause.map (fun l => Numeric.atomMap source l.atom))

theorem evaluate_block (source : PeriodicCNF Nat) (i : Nat) (c : PeriodicClause Nat)
    (active : source.clauses[i]? = some c) (p : ClauseProfile)
    (profile : c.map LiteralProfile.ofLiteral = p.literals) (tail : List Nat) :
    evaluate (c.map PeriodicLiteral.atom ++ tail) i 0 (block p) = clauseAtoms source i c := by
  have len := congrArg List.length profile
  simp only [List.length_map] at len
  cases p with
  | unary a =>
    obtain ⟨x,rfl⟩ := List.length_eq_one_iff.mp len
    simp [block,evaluate,originalStep,clauseStep,clauseAtoms,clauseClauses,
      disjunctionGadget,liftLiteral,negate,padding,forcePaddingFalse,auxiliary,
      Numeric.atomMap,Numeric.auxiliaryCode_active source i _ active]
  | binary a b =>
    obtain ⟨x,y,rfl⟩ := List.length_eq_two.mp len
    simp [block,evaluate,originalStep,clauseStep,clauseAtoms,clauseClauses,
      disjunctionGadget,liftLiteral,negate,padding,forcePaddingFalse,auxiliary,
      Numeric.atomMap,Numeric.auxiliaryCode_active source i _ active]
  | ternary a b c =>
    obtain ⟨x,y,z,rfl⟩ := List.length_eq_three.mp len
    simp [block,evaluate,originalStep,clauseStep,clauseAtoms,clauseClauses,
      disjunctionGadget,liftLiteral,negate,padding,forcePaddingFalse,auxiliary,
      Numeric.atomMap,Numeric.auxiliaryCode_active source i _ active]

theorem evaluate_after_prefix (leading original : List Nat) (clause occurrence : Nat)
    (ds : List Descriptor) :
    evaluate (leading ++ original) clause (leading.length + occurrence) ds =
      evaluate original clause occurrence ds := by
  induction ds generalizing clause occurrence with
  | nil => rfl
  | cons d ds ih =>
    simp only [evaluate,Nat.add_assoc,ih]
    congr 1
    cases d.1 with
    | none => rw [List.getD_append_right _ _ _ _ (by omega)]; simp
    | some k => rfl

noncomputable def gadgetAtoms (source : PeriodicCNF Nat) : Nat → List (PeriodicClause Nat) → List Nat
  | _, [] => []
  | i, c :: cs => clauseAtoms source i c ++ gadgetAtoms source (i+1) cs

theorem evaluate_blocks (source : PeriodicCNF Nat) (cs : List (PeriodicClause Nat))
    (ps : List ClauseProfile) (i : Nat)
    (active : ∀ j c, cs[j]? = some c → source.clauses[i+j]? = some c)
    (profiles : cs.map (List.map LiteralProfile.ofLiteral) = ps.map ClauseProfile.literals) :
    evaluate (cs.flatMap (List.map PeriodicLiteral.atom)) i 0 (ps.flatMap block) =
      gadgetAtoms source i cs := by
  induction cs generalizing ps i with
  | nil =>
    have : ps=[] := by simpa using (List.map_eq_nil_iff.mp profiles.symm)
    subst ps
    rfl
  | cons c cs ih =>
    cases ps with
    | nil => simp at profiles
    | cons p ps =>
      simp only [List.map_cons,List.cons.injEq] at profiles
      have lengthEq : c.length=p.literals.length := by
        simpa using congrArg List.length profiles.1
      have firstActive := active 0 c (by simp)
      simp only [Nat.add_zero] at firstActive
      have restActive : ∀ j d,cs[j]?=some d → source.clauses[(i+1)+j]?=some d := by
        intro j d hd
        simpa only [List.getElem?_cons_succ,Nat.add_assoc,Nat.add_comm 1 j] using
          active (j+1) d hd
      rw [List.flatMap_cons,List.flatMap_cons,evaluate_append,block_clause_sum,block_original_sum]
      rw [evaluate_block source i c firstActive p profiles.1]
      simp only [Nat.zero_add,← lengthEq]
      have shift := evaluate_after_prefix (c.map PeriodicLiteral.atom)
        (cs.flatMap (List.map PeriodicLiteral.atom)) (i+1) 0 (ps.flatMap block)
      simp only [List.length_map,Nat.add_zero] at shift
      rw [shift,ih ps (i+1) restActive profiles.2]
      rfl

theorem gadgetAtoms_zipIdx (source : PeriodicCNF Nat) (i : Nat)
    (cs : List (PeriodicClause Nat)) :
    gadgetAtoms source i cs = (cs.zipIdx i).flatMap (fun p => clauseAtoms source p.2 p.1) := by
  induction cs generalizing i with
  | nil => rfl
  | cons c cs ih => simp [gadgetAtoms,List.zipIdx_cons,ih]

end LeanTrominoes.PeriodicOneInThree.AtomDescriptors
