/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GraphAbstractBridge

/-! # Transferring constraint results to public product and list data

All conversions are confined to this proof bridge. They are computable
bijections and preserve the flat binary input words exactly.
-/
namespace LeanTrominoes.GraphConstraintsAbstractBridge

abbrev Cell := ℤ × ℤ
abbrev Literal := ℕ × Cell × Bool
abbrev Formula := List (List Literal)

def Literal.atom (l : Literal) : ℕ := l.1
def Literal.offset (l : Literal) : Cell := l.2.1
def Literal.value (l : Literal) : Bool := l.2.2
def Formula.clauses (f : Formula) : List (List Literal) := f

def Satisfies (f : Formula) (a : ℕ → Cell → Bool) : Prop :=
  ∀ (z : Cell) c, c∈f.clauses → ∃ l∈c,
    a l.atom (z.1+l.offset.1,z.2+l.offset.2)=l.value

def Satisfiable (f : Formula) : Prop := ∃ a, Satisfies f a

def LocalFormula (f : Formula) : Prop :=
  ∀ c∈f.clauses, ∀ l∈c, ∀ r∈c,
    (l.offset.1-r.offset.1).natAbs+(l.offset.2-r.offset.2).natAbs≤1

def WidthAtMost (k : ℕ) (f : Formula) : Prop := ∀ c∈f.clauses, c.length≤k

def OccurrencesAtMost (k : ℕ) (f : Formula) : Prop :=
  ∀ v, (f.clauses.flatMap fun c => c.map Literal.atom).count v≤k

def ZeroDimensional (f : Formula) : Prop := ∀ c∈f.clauses, ∀ l∈c, l.offset=(0,0)

def OneDimensional (f : Formula) : Prop := ∀ c∈f.clauses, ∀ l∈c, l.offset.2=0

def LineLocal (f : Formula) : Prop :=
  ∀ c∈f.clauses, ∀ l∈c, ∀ r∈c, (l.offset.1-r.offset.1).natAbs≤1

def LineSAT (f : Formula) : Prop :=
  (∃ a : ℕ → ℤ → Bool, ∀ (z : ℤ) c, c∈f.clauses →
    ∃ l∈c, a l.atom (z+l.offset.1)=l.value) ∧ OneDimensional f ∧ LineLocal f

def ExactlyOneSatisfiable (f : Formula) : Prop :=
  ∃ a : ℕ → Cell → Bool, ∀ (z : Cell) c, c∈f.clauses →
    (c.map fun l => a l.atom (z.1+l.offset.1,z.2+l.offset.2)==l.value).count true=1

def literalFields (l : Literal) : List ℕ :=
  [l.atom,Encodable.encode l.offset.1,Encodable.encode l.offset.2,if l.value then 1 else 0]

def clauseFields (c : List Literal) : List ℕ := c.length::c.flatMap literalFields

def encoding (f : Formula) : List ComplexityAbstract.Symbol :=
  ComplexityAbstract.binaryFields (f.clauses.length::f.clauses.flatMap clauseFields)

def literalEquiv : Literal ≃ PeriodicLiteral ℕ := PeriodicLiteral.equivData.symm

def clauseEquiv : List Literal ≃ PeriodicClause ℕ := Equiv.listEquivOfEquiv literalEquiv

def formulaEquiv : Formula ≃ PeriodicCNF ℕ :=
  (Equiv.listEquivOfEquiv clauseEquiv).trans PeriodicCNF.equivData.symm

theorem formulaEquiv_computable : Computable formulaEquiv := by
  have literals : Primrec (literalEquiv : Literal → PeriodicLiteral ℕ) :=
    PeriodicLiteral.equivData_symm_primrec
  have clauses := Primrec.list_map Primrec.id (literals.comp Primrec.snd).to₂
  have formulas := Primrec.list_map Primrec.id (clauses.comp Primrec.snd).to₂
  exact (PeriodicCNF.equivData_symm_primrec.comp formulas).to_comp

theorem formulaEquiv_symm_computable : Computable formulaEquiv.symm := by
  have literals : Primrec (literalEquiv.symm : PeriodicLiteral ℕ → Literal) :=
    PeriodicLiteral.equivData_primrec
  have clauses := Primrec.list_map Primrec.id (literals.comp Primrec.snd).to₂
  have formulas := Primrec.list_map Primrec.id (clauses.comp Primrec.snd).to₂
  exact (formulas.comp PeriodicCNF.equivData_primrec).to_comp

@[simp] theorem formulaEquiv_clauses (f : Formula) :
    (formulaEquiv f).clauses=f.map (fun c => c.map literalEquiv) := rfl

@[simp] theorem literalEquiv_atom (l : Literal) : (literalEquiv l).atom=l.atom := rfl
@[simp] theorem literalEquiv_offset (l : Literal) : (literalEquiv l).offset=l.offset := rfl
@[simp] theorem literalEquiv_value (l : Literal) : (literalEquiv l).value=l.value := rfl

theorem clauseFields_eq (c : List Literal) :
    PeriodicCNFFlatEncoding.clauseFields (c.map literalEquiv)=clauseFields c := by
  simp only [PeriodicCNFFlatEncoding.clauseFields,clauseFields,List.length_map,List.flatMap_map]
  congr 1

theorem encoding_eq (f : Formula) : encoding f=PeriodicCNFFlatEncoding.finEncoding.encode (formulaEquiv f) := by
  change ComplexityAbstract.binaryFields (f.length::f.flatMap clauseFields)=
    PeriodicCNFFlatEncoding.encodeNatFields (PeriodicCNFFlatEncoding.formulaFields (formulaEquiv f))
  rw [PeriodicCNFFlatEncoding.encodeNatFields_eq_trList]
  change Turing.PartrecToTM2.trList _=Turing.PartrecToTM2.trList _
  congr 1
  simp only [PeriodicCNFFlatEncoding.formulaFields,formulaEquiv_clauses,List.length_map,List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro c hc
  exact (clauseFields_eq c).symm

private theorem exists_mem_map_iff {A B : Type} (f : A → B) (xs : List A) (p : B → Prop) :
    (∃ y∈xs.map f, p y) ↔ ∃ x∈xs, p (f x) := by
  constructor
  · rintro ⟨y,member,h⟩
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp member
    exact ⟨x,hx,h⟩
  · rintro ⟨x,hx,h⟩
    exact ⟨f x,List.mem_map.mpr ⟨x,hx,rfl⟩,h⟩

macro "constraint_conversion" : tactic => `(tactic|
  simp only [Satisfiable,Satisfies,LocalFormula,WidthAtMost,OccurrencesAtMost,ZeroDimensional,
    OneDimensional,LineLocal,LineSAT,ExactlyOneSatisfiable,
    GraphAbstractBridge.Data.Satisfiable,GraphAbstractBridge.Data.Satisfies,
    GraphAbstractBridge.Data.LocalFormula,GraphAbstractBridge.Data.WidthAtMost,
    GraphAbstractBridge.Data.OccurrencesAtMost,GraphAbstractBridge.Data.ZeroDimensional,
    GraphAbstractBridge.Data.OneDimensional,GraphAbstractBridge.Data.LineSAT,
    GraphAbstractBridge.Data.ExactlyOneSatisfiable,PeriodicCNF.IsLocalOnLine,
    PeriodicClause.IsLocalOnLine,PeriodicClause.offsetDistanceOnLine,
    Formula.clauses,formulaEquiv_clauses,List.forall_mem_map,exists_mem_map_iff,
    List.flatMap_map,List.map_map,List.length_map,Function.comp_apply,Function.comp_def,
    literalEquiv_atom,literalEquiv_offset,literalEquiv_value])

theorem satisfiable_iff (f : Formula) :
    Satisfiable f ↔ GraphAbstractBridge.Data.Satisfiable (formulaEquiv f) := by constraint_conversion

theorem local_iff (f : Formula) :
    LocalFormula f ↔ GraphAbstractBridge.Data.LocalFormula (formulaEquiv f) := by constraint_conversion

theorem width_iff (k : ℕ) (f : Formula) :
    WidthAtMost k f ↔ GraphAbstractBridge.Data.WidthAtMost k (formulaEquiv f) := by constraint_conversion

theorem occurrences_iff (k : ℕ) (f : Formula) :
    OccurrencesAtMost k f ↔ GraphAbstractBridge.Data.OccurrencesAtMost k (formulaEquiv f) := by constraint_conversion

theorem zero_iff (f : Formula) :
    ZeroDimensional f ↔ GraphAbstractBridge.Data.ZeroDimensional (formulaEquiv f) := by constraint_conversion

theorem line_iff (f : Formula) :
    OneDimensional f ↔ GraphAbstractBridge.Data.OneDimensional (formulaEquiv f) := by constraint_conversion

theorem lineSAT_iff (f : Formula) :
    LineSAT f ↔ GraphAbstractBridge.Data.LineSAT (formulaEquiv f) := by constraint_conversion

theorem exactOne_iff (f : Formula) :
    ExactlyOneSatisfiable f ↔ GraphAbstractBridge.Data.ExactlyOneSatisfiable (formulaEquiv f) := by constraint_conversion

private theorem coRE_transfer (p : Formula → Prop) (q : PeriodicCNF ℕ → Prop)
    (correct : ∀ f, p f ↔ q (formulaEquiv f)) (complete : LeanWang.CoREComplete q) :
    LeanWang.CoREComplete p :=
  ComplexityAbstractBridge.coRE_recode formulaEquiv formulaEquiv_computable formulaEquiv_symm_computable
    p q correct complete

private theorem pspace_transfer (p : Formula → Prop) (q : PeriodicCNF ℕ → Prop)
    (correct : ∀ f, p f ↔ q (formulaEquiv f))
    (complete : ComplexityAbstract.PSPACEComplete PeriodicCNFFlatEncoding.finEncoding.encode q) :
    ComplexityAbstract.PSPACEComplete encoding p :=
  ComplexityAbstractBridge.pspaceComplete_recode encoding PeriodicCNFFlatEncoding.finEncoding.encode
    formulaEquiv (Equiv.refl _) (by intro f; change (encoding f).map id=_; rw [List.map_id]; exact encoding_eq f) p q correct complete

theorem line_sat : ComplexityAbstract.PSPACEComplete encoding LineSAT :=
  pspace_transfer _ _ lineSAT_iff GraphAbstractBridge.Data.line_sat

theorem line_three_sat : ComplexityAbstract.PSPACEComplete encoding
    (fun f => LineSAT f ∧ WidthAtMost 3 f) :=
  pspace_transfer _ _ (fun f => and_congr (lineSAT_iff f) (width_iff 3 f))
    GraphAbstractBridge.Data.line_three_sat

theorem line_three_sat_three : ComplexityAbstract.PSPACEComplete encoding
    (fun f => LineSAT f ∧ WidthAtMost 3 f ∧ OccurrencesAtMost 3 f) :=
  pspace_transfer _ _ (fun f => and_congr (lineSAT_iff f) (and_congr (width_iff 3 f) (occurrences_iff 3 f)))
    GraphAbstractBridge.Data.line_three_sat_three

theorem plane_three_sat : LeanWang.CoREComplete
    (fun f => Satisfiable f ∧ LocalFormula f ∧ WidthAtMost 3 f) :=
  coRE_transfer _ _ (fun f => and_congr (satisfiable_iff f) (and_congr (local_iff f) (width_iff 3 f)))
    GraphAbstractBridge.Data.plane_three_sat

theorem plane_three_sat_three : LeanWang.CoREComplete
    (fun f => Satisfiable f ∧ LocalFormula f ∧ WidthAtMost 3 f ∧ OccurrencesAtMost 3 f) :=
  coRE_transfer _ _ (fun f => and_congr (satisfiable_iff f)
    (and_congr (local_iff f) (and_congr (width_iff 3 f) (occurrences_iff 3 f))))
    GraphAbstractBridge.Data.plane_three_sat_three

theorem plane_exact_one : LeanWang.CoREComplete
    (fun f => ExactlyOneSatisfiable f ∧ LocalFormula f ∧ WidthAtMost 3 f ∧ OccurrencesAtMost 3 f) :=
  coRE_transfer _ _ (fun f => and_congr (exactOne_iff f)
    (and_congr (local_iff f) (and_congr (width_iff 3 f) (occurrences_iff 3 f))))
    GraphAbstractBridge.Data.plane_exact_one

theorem line_exact_one : ComplexityAbstract.PSPACEComplete encoding
    (fun f => ExactlyOneSatisfiable f ∧ OneDimensional f ∧ LocalFormula f ∧ WidthAtMost 3 f) :=
  pspace_transfer _ _ (fun f => and_congr (exactOne_iff f)
    (and_congr (line_iff f) (and_congr (local_iff f) (width_iff 3 f))))
    GraphAbstractBridge.Data.line_exact_one

theorem line_exact_one_three : ComplexityAbstract.PSPACEComplete encoding
    (fun f => ExactlyOneSatisfiable f ∧ OneDimensional f ∧ LocalFormula f ∧
      WidthAtMost 3 f ∧ OccurrencesAtMost 3 f) :=
  pspace_transfer _ _ (fun f => and_congr (exactOne_iff f)
    (and_congr (line_iff f) (and_congr (local_iff f) (and_congr (width_iff 3 f) (occurrences_iff 3 f)))))
    GraphAbstractBridge.Data.line_exact_one_three

theorem cook_levin : ComplexityAbstract.NPHard encoding
    (fun f => Satisfiable f ∧ ZeroDimensional f ∧ WidthAtMost 3 f) :=
  ComplexityAbstractBridge.npHard_recode encoding PeriodicCNFFlatEncoding.finEncoding.encode
    formulaEquiv (Equiv.refl _) (by intro f; change (encoding f).map id=_; rw [List.map_id]; exact encoding_eq f) _ _
    (fun f => and_congr (satisfiable_iff f) (and_congr (zero_iff f) (width_iff 3 f)))
    GraphAbstractBridge.Data.cook_levin

end LeanTrominoes.GraphConstraintsAbstractBridge
