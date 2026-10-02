/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFCoRE

/-! # Periodic Boolean constraints over an arbitrary computable lattice -/
namespace LeanTrominoes.PeriodicConstraints
open Computability
variable (G : Type) [AddCommGroup G]
abbrev Literal := (Nat × G) × Bool
abbrev Formula := List (List (Literal G))
abbrev Ground := List (List ((Nat × G) × Bool))

def Holds (f : Formula G) (a : Nat → G → Bool) : Prop :=
  ∀ z c, c ∈ f → ∃ l ∈ c, a l.1.1 (z+l.1.2)=l.2

def Satisfiable (f : Formula G) : Prop := ∃ a, Holds G f a

def groundHolds (g : Ground G) (a : Nat × G → Bool) : Prop :=
  ∀ c ∈ g, ∃ l ∈ c, a l.1=l.2

variable {G} [DecidableEq G]
def check (g : Ground G) : Prop :=
  ∃ selected ∈ PlaneTilingSearch.subsets (g.flatMap fun c => c.map Prod.fst),
    groundHolds G g (fun a => decide (a ∈ selected))

instance (g : Ground G) : Decidable (check g) := by
  unfold check groundHolds
  infer_instance

theorem check_iff (g : Ground G) : check g ↔ ∃ a, groundHolds G g a := by
  constructor
  · rintro ⟨s,_,h⟩; exact ⟨_,h⟩
  · rintro ⟨a,h⟩
    let atoms := g.flatMap fun c => c.map Prod.fst
    refine ⟨atoms.filter a,PlaneTilingSearch.filter_mem_subsets _ _,?_⟩
    intro c hc
    obtain ⟨l,hl,value⟩ := h c hc
    refine ⟨l,hl,?_⟩
    have member : l.1 ∈ atoms := List.mem_flatMap.mpr ⟨c,hc,List.mem_map.mpr ⟨l,hl,rfl⟩⟩
    simp [List.mem_filter,member,value]

variable [Primcodable G]
def translates (r : Nat) : List G := (List.range (r+1)).filterMap Encodable.decode

def instantiate (f : Formula G) (r : Nat) : Ground G :=
  (translates (G := G) r).flatMap fun z =>
    f.map fun c => c.map fun l => ((l.1.1,z+l.1.2),l.2)

theorem mem_translates (g : G) : g ∈ translates (Encodable.encode g) := by
  apply List.mem_filterMap.mpr
  exact ⟨Encodable.encode g,List.mem_range.mpr (by omega),Encodable.encodek g⟩

theorem translates_mono (r : Nat) : translates (G := G) r ⊆ translates (r+1) := by
  intro g hg
  obtain ⟨n,hn,eq⟩ := List.mem_filterMap.mp hg
  exact List.mem_filterMap.mpr ⟨n,List.mem_range.mpr (by have := List.mem_range.mp hn; omega),eq⟩

theorem ground_instantiate (f : Formula G) (r : Nat) (a : Nat × G → Bool) :
    groundHolds G (instantiate f r) a ↔
      ∀ z ∈ translates r, ∀ c ∈ f, ∃ l ∈ c, a (l.1.1,z+l.1.2)=l.2 := by
  simp only [groundHolds,instantiate,List.forall_mem_flatMap,List.forall_mem_map]
  simp only [List.mem_map,exists_exists_and_eq_and]

local instance : TopologicalSpace Bool := ⊥
local instance : DiscreteTopology Bool := discreteTopology_bot _
local instance : CompactSpace Bool := Finite.compactSpace

private theorem clause_closed (c : List ((Nat × G) × Bool)) :
    IsClosed {a : Nat × G → Bool | ∃ l ∈ c, a l.1=l.2} := by
  induction c with
  | nil => simp
  | cons l ls ih =>
    have one : IsClosed {a : Nat × G → Bool | a l.1=l.2} :=
      isClosed_singleton.preimage (continuous_apply l.1)
    simpa only [List.mem_cons,exists_eq_or_imp,Set.setOf_or] using one.union ih

private theorem ground_closed (g : Ground G) : IsClosed {a | groundHolds G g a} := by
  unfold groundHolds
  convert isClosed_iInter (fun c => isClosed_iInter (fun (_ : c ∈ g) => clause_closed c)) using 1
  ext a; simp

theorem satisfiable_iff_checks (f : Formula G) : Satisfiable G f ↔ ∀ r, check (instantiate f r) := by
  constructor
  · rintro ⟨a,h⟩ r
    apply (check_iff _).mpr
    exact ⟨fun q => a q.1 q.2,(ground_instantiate _ _ _).mpr (fun z _ c hc => h z c hc)⟩
  · intro checked
    let patches (r : Nat) : Set (Nat × G → Bool) := {a | groundHolds G (instantiate f r) a}
    have nonempty (r : Nat) : (patches r).Nonempty := (check_iff _).mp (checked r)
    have closed (r : Nat) : IsClosed (patches r) := ground_closed _
    have decreasing (r : Nat) : patches (r+1) ⊆ patches r := by
      intro a ha
      apply (ground_instantiate _ _ _).mpr
      intro z hz c hc
      exact (ground_instantiate _ _ _).mp ha z (translates_mono r hz) c hc
    obtain ⟨a,ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      patches decreasing nonempty (closed 0).isCompact closed
    have all : ∀ r, a ∈ patches r := by simpa using ha
    refine ⟨fun v z => a (v,z),?_⟩
    intro z c hc
    exact (ground_instantiate _ _ _).mp (all (Encodable.encode z)) z (mem_translates z) c hc

/-- Only addition needs an effectiveness assumption; dimension and geometry are irrelevant. -/
theorem satisfiable_coRE (add_primrec : Primrec₂ (fun x y : G => x+y)) :
    LeanWang.CoREPred (Satisfiable G) := by
  have holds : PrimrecRel fun (g : Ground G) (s : List (Nat × G)) =>
      groundHolds G g (fun a => decide (a ∈ s)) := by
    have literal : PrimrecRel fun (l : (Nat × G) × Bool) (s : List (Nat × G)) =>
        decide (l.1 ∈ s)=l.2 :=
      Primrec.eq.comp (PeriodicCNF.FiniteSearch.mem_primrec.decide.comp
        (Primrec.fst.comp Primrec.fst) Primrec.snd) (Primrec.snd.comp Primrec.fst)
    exact literal.exists_mem_list.forall_mem_list
  have check_pr : PrimrecPred (@check G _) :=
    holds.swap.exists_mem_list.comp
      (PlaneTilingSearch.subsets_primrec.comp
        (Primrec.list_flatMap Primrec.id (Primrec.list_map Primrec.snd (Primrec.fst.comp Primrec.snd).to₂))) Primrec.id
  have tr_pr : Primrec (@translates G _) :=
    Primrec.listFilterMap (Primrec.list_range.comp Primrec.succ) (Primrec.decode.comp Primrec.snd)
  have literal_pr : Primrec₂ fun (z : G) (l : Literal G) => ((l.1.1,z+l.1.2),l.2) :=
    Primrec.pair (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (add_primrec.comp Primrec.fst (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp Primrec.snd)
  have clause_pr : Primrec₂ fun (z : G) (c : List (Literal G)) =>
      c.map fun l => ((l.1.1,z+l.1.2),l.2) :=
    Primrec.list_map Primrec.snd (literal_pr.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have at_pr : Primrec₂ fun (f : Formula G) (z : G) =>
      f.map fun c => c.map fun l => ((l.1.1,z+l.1.2),l.2) :=
    Primrec.list_map Primrec.fst (clause_pr.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
  have inst_pr : Primrec₂ (@instantiate G _ _) :=
    Primrec.list_flatMap (tr_pr.comp Primrec.snd) (at_pr.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have obstruction := LeanWang.REPred.exists_nat
    (p := fun f r => ¬ check (instantiate f r)) (check_pr.comp inst_pr).not.computablePred
  exact obstruction.of_eq fun f => by
    rw [satisfiable_iff_checks]
    exact not_forall.symm

end LeanTrominoes.PeriodicConstraints
