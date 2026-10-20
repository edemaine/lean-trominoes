/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATCompiledInput

/-! # One unused variable makes cover generation uniform at zero variables -/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM
open PeriodicLatticeGraph ImplicationGraph
variable {n d : ℕ}

def liftLiteral (a : Literal (Fin n) d) : Literal (Fin (n+1)) d :=
  ((a.1.1.castSucc,a.1.2),a.2)
def liftClause (c : Clause (Fin n) d) : Clause (Fin (n+1)) d :=
  c.map (fun ab => (liftLiteral ab.1,liftLiteral ab.2))
def liftFormula (f : Formula (Fin n) d) : Formula (Fin (n+1)) d := f.map liftClause

def liftArc (e : Arc (Signed (Fin n)) d) : Arc (Signed (Fin (n+1))) d :=
  ⟨(e.source.1.castSucc,e.source.2),(e.target.1.castSucc,e.target.2),e.offset⟩

theorem liftClause_holds (c : Clause (Fin n) d) (model : Fin (n+1) → Lattice d → Prop) (z : Lattice d) :
    Holds model z (liftClause c) ↔ Holds (fun a => model a.castSucc) z c := by
  cases c with
  | none => rfl
  | some pair => rcases pair with ⟨a,b⟩; rfl

theorem liftFormula_satisfiable (f : Formula (Fin n) d) : Satisfiable (liftFormula f) ↔ Satisfiable f := by
  constructor
  · rintro ⟨model,satisfied⟩
    refine ⟨fun a => model a.castSucc,?_⟩
    intro c member z
    exact (liftClause_holds c model z).mp (satisfied _ (List.mem_map.mpr ⟨c,member,rfl⟩) z)
  · rintro ⟨model,satisfied⟩
    let extended : Fin (n+1) → Lattice d → Prop := Fin.lastCases (fun _ => True) model
    refine ⟨extended,?_⟩
    intro c member z
    obtain ⟨original,originalMem,rfl⟩ := List.mem_map.mp member
    apply (liftClause_holds original extended z).mpr
    simpa only [extended,Fin.lastCases_castSucc] using satisfied original originalMem z

theorem liftFormula_local (f : Formula (Fin n) d) (locality : LocalDifferences f) : LocalDifferences (liftFormula f) := by
  intro a b member j
  obtain ⟨c,hc,equal⟩ := List.mem_map.mp member
  cases c with
  | none => simp [liftClause] at equal
  | some pair =>
    rcases pair with ⟨x,y⟩
    have same : (liftLiteral x,liftLiteral y)=(a,b) := Option.some.inj equal
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
    exact locality x y hc j

theorem liftFormula_none (f : Formula (Fin n) d) : none ∈ liftFormula f ↔ none ∈ f := by
  constructor
  · intro member
    obtain ⟨c,hc,equal⟩ := List.mem_map.mp member
    cases c with
    | none => exact hc
    | some pair => simp [liftClause] at equal
  · intro member
    exact List.mem_map.mpr ⟨none,member,rfl⟩

theorem clauseArcs_lift (c : Clause (Fin n) d) : clauseArcs (liftClause c)=(clauseArcs c).map liftArc := by
  cases c with
  | none => rfl
  | some pair => rcases pair with ⟨a,b⟩; rfl

theorem arcs_lift (f : Formula (Fin n) d) : arcs (liftFormula f)=(arcs f).map liftArc := by
  simp [arcs,liftFormula,List.flatMap_map,clauseArcs_lift,List.map_flatMap]

theorem lifted_arc_source (f : Formula (Fin n) d) (e : Arc (Signed (Fin (n+1))) d)
    (member : e ∈ arcs (liftFormula f)) : e.source.1.val<n := by
  rw [arcs_lift] at member
  obtain ⟨original,member,rfl⟩ := List.mem_map.mp member
  exact original.source.1.isLt

theorem unused_coverReach {M : ℕ} (f : Formula (Fin n) d) (sign : Bool) (z : CoverLattice d M)
    (v : Signed (Fin (n+1)) × CoverLattice d M)
    (path : CoverReach (arcs (liftFormula f)) M ((Fin.last n,sign),z) v) :
    v=((Fin.last n,sign),z) := by
  induction path with
  | refl => rfl
  | @tail u v path edge ih =>
    obtain ⟨e,member,source,target,offset⟩ := edge
    have bound := lifted_arc_source f e member
    have equal := congrArg (fun a => a.1.val) source
    rw [ih] at equal
    simp only [Fin.val_last] at equal
    omega

def liftedPairs (n d : ℕ) : Fin n →
    Fin ((n+1)*2*(period (Fin (n+1)) d)^d) × Fin ((n+1)*2*(period (Fin (n+1)) d)^d) :=
  fun a => (coverIndex (n+1) d (period (Fin (n+1)) d) ((a.castSucc,true),0),
    coverIndex (n+1) d (period (Fin (n+1)) d) ((a.castSucc,false),0))

def uniformInput (f : Formula (Fin n) d) : Horn.WordRAM.Input :=
  ⟨n*2*((n+1)*2*(period (Fin (n+1)) d)^d)+1,
    appendMarkers (TwoSATBatch.input (paddedCoverEdges (by omega) (liftFormula f) (period (Fin (n+1)) d))
      (liftedPairs n d)) (clauseFlags f)⟩

theorem uniformInput_correct (f : Formula (Fin n) d) (locality : LocalDifferences f) :
    Horn.Satisfiable (uniformInput f).2.rules.toList ↔ Satisfiable f := by
  rw [← liftFormula_satisfiable f,localDifferences_cover _ (liftFormula_local f locality)]
  change Horn.Satisfiable (appendMarkers _ _).rules.toList ↔ _
  rw [appendMarkers_correct,TwoSATBatch.input_correct,clauseFlags_correct,liftFormula_none]
  simp only [TwoSATBatch.Consistent,liftedPairs,paddedCoverEdges_reach]
  have all : (∀ a : Fin (n+1), ¬(CoverReach (arcs (liftFormula f)) (period (Fin (n+1)) d) ((a,true),0) ((a,false),0) ∧
      CoverReach (arcs (liftFormula f)) (period (Fin (n+1)) d) ((a,false),0) ((a,true),0))) ↔
    (∀ a : Fin n, ¬(CoverReach (arcs (liftFormula f)) (period (Fin (n+1)) d) ((a.castSucc,true),0) ((a.castSucc,false),0) ∧
      CoverReach (arcs (liftFormula f)) (period (Fin (n+1)) d) ((a.castSucc,false),0) ((a.castSucc,true),0))) := by
    constructor
    · intro all a
      exact all a.castSucc
    · intro original a
      refine Fin.lastCases ?_ (fun a => original a) a
      rintro ⟨forward,backward⟩
      have equal := unused_coverReach f true 0 _ forward
      have bad := congrArg (fun a => a.1.2) equal
      cases bad
  tauto

theorem uniformInput_rules (f : Formula (Fin n) d) :
    (uniformInput f).2.rules.size=3*n+2*n*(2*f.length*(period (Fin (n+1)) d)^d)+f.length := by
  simp [uniformInput,appendMarkers_rules,TwoSATBatch.input_rules,paddedCoverEdges_length,clauseFlags,liftFormula]

theorem uniformInput_occurrences (f : Formula (Fin n) d) :
    (Horn.Indexed.edges (uniformInput f).2).length=2*n+2*n*(2*f.length*(period (Fin (n+1)) d)^d) := by
  simp [uniformInput,appendMarkers_occurrences,TwoSATBatch.input_occurrences,paddedCoverEdges_length,liftFormula]

theorem uniformInput_size (f : Formula (Fin n) d) :
    Horn.WordRAM.size (uniformInput f)=
      4*n*(n+1)*(period (Fin (n+1)) d)^d+5*n+8*n*f.length*(period (Fin (n+1)) d)^d+f.length+2 := by
  simp only [Horn.WordRAM.size,uniformInput,appendMarkers_rules,appendMarkers_occurrences,
    TwoSATBatch.input_rules,TwoSATBatch.input_occurrences,paddedCoverEdges_length,clauseFlags,liftFormula,List.length_map]
  ring

end LeanTrominoes.PeriodicTwoSAT.WordRAM
