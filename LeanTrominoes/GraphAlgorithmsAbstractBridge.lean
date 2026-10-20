/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GraphAbstractBridge
import LeanTrominoes.SAT.Horn.HornWordRAMLinearTime
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMPolynomialTime

/-! # Operational bridge for the graph abstract's algorithms

The public data are products and lists. The translations below merely change
the proof view of the original input words; their wire encodings agree exactly.
Thus the transferred bounds count the original fixed RAM programs in full.
-/
namespace LeanTrominoes.GraphAlgorithmsAbstractBridge
namespace Data
abbrev HornRule (V : Type) := List V × Option V

def HornSatisfies {V : Type} (rules : List (HornRule V)) (model : V → Prop) : Prop :=
  ∀ rule∈rules, (∀ atom∈rule.1, model atom) →
    match rule.2 with | none => False | some atom => model atom

def HornSatisfiable {V : Type} (rules : List (HornRule V)) : Prop := ∃ model, HornSatisfies rules model

def DualHornSatisfiable {V : Type} (rules : List (HornRule V)) : Prop :=
  ∃ model : V → Prop, HornSatisfies rules (fun atom => ¬model atom)

def PeriodicHornSatisfies {V G : Type} [Add G] (rules : List (HornRule (V×G))) (model : V → G → Prop) : Prop :=
  ∀ rule∈rules, ∀ z, (∀ premise∈rule.1, model premise.1 (z+premise.2)) →
    match rule.2 with | none => False | some head => model head.1 (z+head.2)

def PeriodicHornSatisfiable {V G : Type} [Add G] (rules : List (HornRule (V×G))) : Prop := ∃ model, PeriodicHornSatisfies rules model

def PeriodicDualHornSatisfies {V G : Type} [Add G] (rules : List (HornRule (V×G))) (model : V → G → Prop) : Prop :=
  PeriodicHornSatisfies rules (fun v z => ¬model v z)

def PeriodicDualHornSatisfiable {V G : Type} [Add G] (rules : List (HornRule (V×G))) : Prop := ∃ model, PeriodicDualHornSatisfies rules model

abbrev HornInput := Σ n : Nat, List (HornRule (Fin n))

def hornOccurrences (input : HornInput) : List (Fin input.1 × Nat) :=
  (List.finRange input.2.length).flatMap fun rule => (input.2.get rule).1.map fun v => (v,rule.val)

def hornAtomCode {n : Nat} : Option (Fin n) → Nat | none => 0 | some v => v.val+1

def hornEncoding (input : HornInput) : List Int :=
  ([input.1,input.2.length,(hornOccurrences input).length]++
    (List.finRange input.2.length).map (fun rule => hornAtomCode (input.2.get rule).2)++
    (hornOccurrences input).map (fun (occurrence : Fin input.1 × Nat) => occurrence.1.val+1)++
    (hornOccurrences input).map Prod.snd).map Int.ofNat

def hornSize (input : HornInput) : Nat := input.1+input.2.length+(hornOccurrences input).length+1

abbrev Lattice (d : Nat) := Fin d → Int
abbrev BipartiteEdge (L R : Type) (d : Nat) := L × R × Lattice d

def BipartiteAdjacent {L R : Type} {d : Nat} (es : List (BipartiteEdge L R d))
    (u : L × Lattice d) (v : R × Lattice d) : Prop :=
  ∃ e∈es, e.1=u.1 ∧ e.2.1=v.1 ∧ v.2=u.2+e.2.2

def PerfectMatching {L R : Type} {d : Nat} (es : List (BipartiteEdge L R d)) : Prop :=
  ∃ f : (L × Lattice d) ≃ (R × Lattice d), ∀ u, BipartiteAdjacent es u (f u)
def PeriodOneMatching {L R : Type} {d : Nat} (es : List (BipartiteEdge L R d)) : Prop :=
  ∃ f : (L × Lattice d) ≃ (R × Lattice d),
    (∀ u, BipartiteAdjacent es u (f u)) ∧ ∀ l z t, f (l,z+t)=((f (l,z)).1,(f (l,z)).2+t)
def QuotientMatching {L R : Type} {d : Nat} (es : List (BipartiteEdge L R d)) : Prop :=
  ∃ f : L ≃ R, ∀ l, ∃ e∈es, e.1=l ∧ e.2.1=f l

abbrev MatchingInput (d : Nat) := Σ n : Nat, Σ m : Nat, List (BipartiteEdge (Fin n) (Fin m) d)
def matchingEncoding {d : Nat} (input : MatchingInput d) : List Int :=
  ([input.1,input.2.1,input.2.2.length]++input.2.2.map (fun edge => edge.1.val)++
    input.2.2.map (fun edge => edge.2.1.val)).map Int.ofNat
def matchingSize {d : Nat} (input : MatchingInput d) := input.1+input.2.1+input.2.2.length+1


def PeriodOneBipartitePartial {L R : Type} {d : Nat} (es : List (BipartiteEdge L R d))
    (left : L × Lattice d → Option (R × Lattice d))
    (right : R × Lattice d → Option (L × Lattice d)) : Prop :=
  (∀ u v, left u=some v ↔ right v=some u) ∧
  (∀ u v, left u=some v → BipartiteAdjacent es u v) ∧
  (∀ l z t, left (l,z+t)=(left (l,z)).map (fun v => (v.1,v.2+t))) ∧
  ∀ r z t, right (r,z+t)=(right (r,z)).map (fun u => (u.1,u.2+t))

def PerfectBipartitePartial {L R : Type} {d : Nat}
    (left : L × Lattice d → Option (R × Lattice d))
    (right : R × Lattice d → Option (L × Lattice d)) : Prop :=
  (∀ u, left u≠none) ∧ ∀ v, right v≠none

def IsShortBipartiteAugmentingPath {L R : Type} [Fintype L] [Fintype R] {d : Nat}
    (es : List (BipartiteEdge L R d))
    (left : L × Lattice d → Option (R × Lattice d))
    (right : R × Lattice d → Option (L × Lattice d))
    (pairs : List ((L × Lattice d) × (R × Lattice d))) : Prop :=
  pairs≠[] ∧
  (∀ pair∈pairs, BipartiteAdjacent es pair.1 pair.2 ∧ left pair.1≠some pair.2) ∧
  (∀ pair, pairs.head?=some pair → left pair.1=none) ∧
  (∀ pair, pairs.getLast?=some pair → right pair.2=none) ∧
  (∀ i (hi : i+1<pairs.length), right pairs[i].2=some pairs[i+1].1) ∧
  (pairs.flatMap (fun pair => [Sum.inl pair.1.1,Sum.inr pair.2.1])).Nodup ∧
  2*pairs.length-1<Fintype.card L+Fintype.card R

end Data
open Data ComplexityAbstract.RAM

private def nativeRule {V : Type} (rule : HornRule V) : Horn.Rule V := ⟨rule.1,rule.2⟩
private def nativePeriodicRule {V G : Type} (rule : HornRule (V×G)) : Horn.PeriodicRule V G := ⟨rule.1,rule.2⟩

private theorem finite_satisfies {V : Type} (rules : List (HornRule V)) (model : V → Prop) :
    Horn.Satisfies (rules.map nativeRule) model ↔ HornSatisfies rules model := by
  simp only [Horn.Satisfies,Horn.Rule.Holds,HornSatisfies,List.forall_mem_map,nativeRule]
  rfl

private theorem periodic_satisfies {V G : Type} [Add G] (rules : List (HornRule (V×G))) (model : V → G → Prop) :
    Horn.PeriodicSatisfies (rules.map nativePeriodicRule) model ↔ PeriodicHornSatisfies rules model := by
  simp only [Horn.PeriodicSatisfies,Horn.PeriodicRule.Holds,PeriodicHornSatisfies,List.forall_mem_map,nativePeriodicRule]
  rfl

theorem horn_period_one {V G : Type} [AddGroup G] (rules : List (HornRule (V×G)))
    (h : PeriodicHornSatisfiable rules) : ∃ model : V → Prop, PeriodicHornSatisfies rules (fun v _ => model v) := by
  obtain ⟨model,satisfied⟩ := h
  obtain ⟨constant,correct⟩ := Horn.exists_period_one (rules.map nativePeriodicRule) ⟨model,(periodic_satisfies rules model).mpr satisfied⟩
  exact ⟨constant,(periodic_satisfies rules _).mp correct⟩

theorem dual_horn_period_one {V G : Type} [AddGroup G] (rules : List (HornRule (V×G)))
    (h : PeriodicDualHornSatisfiable rules) : ∃ model : V → Prop, PeriodicDualHornSatisfies rules (fun v _ => model v) := by
  classical
  obtain ⟨model,satisfied⟩ := h
  obtain ⟨constant,correct⟩ := horn_period_one rules ⟨(fun v z => ¬model v z),satisfied⟩
  exact ⟨(fun v => ¬constant v),by simpa only [PeriodicDualHornSatisfies,not_not] using correct⟩

private def nativeHornInput (input : HornInput) : Horn.WordRAM.Input := ⟨input.1,⟨(input.2.map nativeRule).toArray⟩⟩

private theorem horn_get_total {n : Nat} (rules : List (HornRule (Fin n))) (i : Nat) (within : i<rules.length) :
    rules[i]=(rules[i]?).getD ([],none) := by simp only [List.getElem?_eq_getElem within,Option.getD_some]

private theorem horn_words (input : HornInput) : Horn.WordRAM.encode (nativeHornInput input)=hornEncoding input := by
  dsimp only [nativeHornInput,Horn.WordRAM.encode,Horn.WordRAM.words,Horn.Indexed.edges]
  simp only [List.size_toArray,List.length_map]
  simp [Horn.WordRAM.atomCode,nativeRule,hornEncoding,hornOccurrences,hornAtomCode,List.map_map,List.map_flatMap,Function.comp_def]
  simp only [horn_get_total]
  have count : (input.2.map nativeRule).toArray.size=input.2.length := List.size_toArray.trans (List.length_map _)
  rw [count]
  exact ⟨rfl,rfl⟩

private theorem horn_size (input : HornInput) : Horn.WordRAM.size (nativeHornInput input)=hornSize input := by
  dsimp only [nativeHornInput,Horn.WordRAM.size,Horn.Indexed.edges]
  simp only [List.size_toArray,List.length_map]
  simp [nativeRule,hornSize,hornOccurrences]
  simp only [horn_get_total]
  have count : (input.2.map nativeRule).toArray.size=input.2.length := List.size_toArray.trans (List.length_map _)
  rw [count]

private theorem horn_correct (input : HornInput) : Horn.Satisfiable (nativeHornInput input).2.rules.toList ↔ HornSatisfiable input.2 := by
  simp only [nativeHornInput,List.toList_toArray,Horn.Satisfiable,HornSatisfiable]
  exact exists_congr (fun model => finite_satisfies input.2 model)

/-- Reusing identical input words preserves exact operational decision bounds. -/
private theorem transfer {A B : Type} (encodeA : A → List Int) (encodeB : B → List Int)
    (p : A → Prop) (q : B → Prop) (time bits : A → Nat) (nativeTime nativeBits : B → Nat)
    (f : A → B) (words : ∀ a, encodeB (f a)=encodeA a)
    (times : ∀ a, nativeTime (f a)=time a) (widths : ∀ a, nativeBits (f a)=bits a)
    (answers : ∀ a, q (f a) ↔ p a) (checked : DecidesWithin encodeB q nativeTime nativeBits) :
    DecidesWithin encodeA p time bits := by
  obtain ⟨registers,program,run⟩ := checked
  refine ⟨registers,program,?_⟩
  intro a w width fits
  obtain ⟨steps,value,execution,budget,boolean,correct⟩ := run (f a) w
    (by simpa only [widths] using width) (by simpa only [words] using fits)
  exact ⟨steps,value,by simpa only [words] using execution,by simpa only [times] using budget,boolean,correct.trans (answers a)⟩

theorem horn_linear : DecidesWithin hornEncoding (fun input => HornSatisfiable input.2)
    (fun input => 120*(hornSize input+1)) (fun input => 27*Nat.log2 (hornSize input+2)+2) := by
  apply transfer hornEncoding Horn.WordRAM.encode (fun input => HornSatisfiable input.2) (fun input => Horn.Satisfiable input.2.rules.toList)
    (fun input => 120*(hornSize input+1)) (fun input => 27*Nat.log2 (hornSize input+2)+2)
    (fun input => 120*(Horn.WordRAM.size input+1)) (fun input => 27*Nat.log2 (Horn.WordRAM.size input+2)+2)
    nativeHornInput horn_words
    (by intro input; rw [horn_size]) (by intro input; rw [horn_size]) horn_correct
  exact Horn.WordRAM.decidesWithin


theorem dual_horn_linear : DecidesWithin hornEncoding (fun input => DualHornSatisfiable input.2)
    (fun input => 120*(hornSize input+1)) (fun input => 27*Nat.log2 (hornSize input+2)+2) := by
  classical
  have equivalent (input : HornInput) : HornSatisfiable input.2 ↔ DualHornSatisfiable input.2 := by
    constructor
    · rintro ⟨model,satisfied⟩
      exact ⟨fun atom => ¬model atom,by simpa only [not_not] using satisfied⟩
    · rintro ⟨model,satisfied⟩
      exact ⟨fun atom => ¬model atom,satisfied⟩
  obtain ⟨registers,program,checked⟩ := horn_linear
  refine ⟨registers,program,?_⟩
  intro input w width fits
  obtain ⟨cost,value,run,budget,boolean,correct⟩ := checked input w width fits
  exact ⟨cost,value,run,budget,boolean,correct.trans (equivalent input)⟩

private def nativeEdges {L R : Type} {d : Nat} (edges : List (BipartiteEdge L R d)) : List (PeriodicBipartite.Edge L R d) :=
  edges.map fun edge => ⟨edge.1,edge.2.1,edge.2.2⟩
private theorem native_adj {L R : Type} {d : Nat} (edges : List (BipartiteEdge L R d))
    (u : L × Lattice d) (v : R × Lattice d) :
    PeriodicBipartite.Adj (nativeEdges edges) u v ↔ BipartiteAdjacent edges u v := by
  simp [PeriodicBipartite.Adj,nativeEdges,BipartiteAdjacent,List.mem_map]
private theorem native_perfect {L R : Type} {d : Nat} (edges : List (BipartiteEdge L R d)) :
    PeriodicBipartite.HasPerfectMatching (nativeEdges edges) ↔ PerfectMatching edges := by
  simp only [PeriodicBipartite.HasPerfectMatching,PerfectMatching,native_adj]
private theorem native_periodic {L R : Type} {d : Nat} (edges : List (BipartiteEdge L R d)) :
    PeriodicBipartite.HasPeriodOneMatching (nativeEdges edges) ↔ PeriodOneMatching edges := by
  simp only [PeriodicBipartite.HasPeriodOneMatching,PeriodicBipartite.TranslationInvariant,PeriodOneMatching,native_adj]
private theorem native_quotient {L R : Type} {d : Nat} (edges : List (BipartiteEdge L R d)) :
    PeriodicBipartite.HasQuotientMatching (nativeEdges edges) ↔ QuotientMatching edges := by
  simp [PeriodicBipartite.HasQuotientMatching,PeriodicBipartite.QuotientAdj,QuotientMatching,nativeEdges,List.mem_map]

theorem matching_period_one {L R : Type} [Fintype L] [Fintype R] {d : Nat}
    (edges : List (BipartiteEdge L R d)) :
    (PerfectMatching edges ↔ QuotientMatching edges) ∧ (PerfectMatching edges → PeriodOneMatching edges) := by
  simpa only [native_perfect,native_quotient,native_periodic] using
    GraphAbstractBridge.Native.matching_period_one (nativeEdges edges)

private def nativeMatchingInput {d : Nat} (input : MatchingInput d) : BipartiteMatching.DenseWordRAM.Input :=
  ⟨input.1,input.2.1,input.2.2.map (fun edge => (edge.1,edge.2.1))⟩
private theorem matching_words {d : Nat} (input : MatchingInput d) :
    BipartiteMatching.DenseWordRAM.encode (nativeMatchingInput input)=matchingEncoding input := by
  simp [BipartiteMatching.DenseWordRAM.encode,BipartiteMatching.DenseWordRAM.words,nativeMatchingInput,matchingEncoding,List.map_map,Function.comp_def]
private theorem matching_size {d : Nat} (input : MatchingInput d) :
    BipartiteMatching.DenseWordRAM.size (nativeMatchingInput input)=matchingSize input := by
  simp [BipartiteMatching.DenseWordRAM.size,nativeMatchingInput,matchingSize]
private theorem matching_correct {d : Nat} (input : MatchingInput d) :
    BipartiteMatching.DenseWordRAM.predicate (nativeMatchingInput input) ↔ PerfectMatching input.2.2 := by
  rw [(matching_period_one input.2.2).1]
  simp only [BipartiteMatching.DenseWordRAM.predicate,BipartiteMatching.HasFiniteMatching,
    QuotientMatching,nativeMatchingInput,BipartiteMatching.DenseSearch.mem_edgeBuckets,List.mem_map,Prod.mk.injEq]

theorem matching_algorithm {d : Nat} : DecidesWithin (matchingEncoding (d:=d)) (fun input => PerfectMatching input.2.2)
    (fun input => 1000*(matchingSize input+1)^4) (fun input => 8*Nat.log2 (matchingSize input+2)+2) := by
  apply transfer matchingEncoding BipartiteMatching.DenseWordRAM.encode (fun input => PerfectMatching input.2.2)
    BipartiteMatching.DenseWordRAM.predicate
    (fun input => 1000*(matchingSize input+1)^4) (fun input => 8*Nat.log2 (matchingSize input+2)+2)
    (fun input => 1000*(BipartiteMatching.DenseWordRAM.size input+1)^4)
    (fun input => 8*Nat.log2 (BipartiteMatching.DenseWordRAM.size input+2)+2)
    nativeMatchingInput matching_words (by intro input; rw [matching_size])
    (by intro input; rw [matching_size]) matching_correct
  exact BipartiteMatching.DenseWordRAM.decidesWithin_quartic


private def nativePartial {L R : Type} {d : Nat} (es : List (BipartiteEdge L R d))
    (left : L × Lattice d → Option (R × Lattice d)) (right : R × Lattice d → Option (L × Lattice d))
    (h : PeriodOneBipartitePartial es left right) : PeriodicBipartite.PeriodOnePartial (nativeEdges es) where
  partners := ⟨left,right⟩
  consistent := h.1
  supported := fun u v paired => (native_adj es u v).mpr (h.2.1 u v paired)
  left_translate := h.2.2.1
  right_translate := h.2.2.2

private theorem pairs_nonempty {A B : Type} (path : BlockingPath.Route A B) : BipartiteMatching.routePairs path≠[] := by
  cases path <;> simp [BipartiteMatching.routePairs]
private theorem pairs_length {A B : Type} (path : BlockingPath.Route A B) :
    (BipartiteMatching.routePairs path).length=path.vertices.length := by
  induction path <;> simp_all [BipartiteMatching.routePairs,BlockingPath.Route.vertices]
private theorem pairs_first {A B : Type} (path : BlockingPath.Route A B) (pair : A×B)
    (head : (BipartiteMatching.routePairs path).head?=some pair) : pair.1=path.first := by
  cases path <;> simp only [BipartiteMatching.routePairs,List.head?_cons,Option.some.injEq] at head
  all_goals subst pair; rfl
private theorem pairs_last {A B : Type} (path : BlockingPath.Route A B) (pair : A×B)
    (last : (BipartiteMatching.routePairs path).getLast?=some pair) : pair.2=path.target := by
  induction path with
  | last a b => simpa [BipartiteMatching.routePairs,BlockingPath.Route.target] using congrArg (Option.map Prod.snd) last.symm
  | cons a b rest ih =>
    have nonempty := pairs_nonempty rest
    cases h : BipartiteMatching.routePairs rest with
    | nil => exact False.elim (nonempty h)
    | cons first tail =>
      simp only [BipartiteMatching.routePairs,h,List.getLast?_cons,Option.getD_some] at last
      apply ih
      simpa only [h,List.getLast?_cons] using last
private theorem pairs_adj {A B : Type} {adj : A→B→Prop} {state : BipartiteMatching.State A B}
    {path : BlockingPath.Route A B} (h : BipartiteMatching.Alternating adj state path) :
    ∀ pair∈BipartiteMatching.routePairs path, adj pair.1 pair.2 := by
  induction h with
  | @last a b edge free =>
    intro pair member
    have equal : pair=(a,b) := by simpa only [BipartiteMatching.routePairs,List.mem_singleton] using member
    subst pair
    exact edge
  | @cons a b rest edge mate later ih =>
    intro pair member
    rcases List.mem_cons.mp member with rfl | member
    · exact edge
    · exact ih pair member
private theorem pairs_steps {A B : Type} {adj : A→B→Prop} {state : BipartiteMatching.State A B}
    {path : BlockingPath.Route A B} (h : BipartiteMatching.Alternating adj state path) :
    ∀ i (within : i+1<(BipartiteMatching.routePairs path).length),
      state.right (BipartiteMatching.routePairs path)[i].2=some (BipartiteMatching.routePairs path)[i+1].1 := by
  induction h with
  | @last a b edge free => intro i within; simp only [BipartiteMatching.routePairs,List.length_singleton] at within; omega
  | @cons a b rest edge mate later ih =>
    intro i within
    cases i with
    | zero => cases rest <;> simpa only [BipartiteMatching.routePairs,List.getElem_cons_zero,List.getElem_cons_succ,BlockingPath.Route.first] using mate
    | succ i =>
      have laterBound : i+1<(BipartiteMatching.routePairs rest).length := by
        simp only [BipartiteMatching.routePairs,List.length_cons] at within
        omega
      simpa only [BipartiteMatching.routePairs,List.getElem_cons_succ,Nat.succ_add] using ih i laterBound
private theorem pairs_projection {L R : Type} {d : Nat}
    (path : BlockingPath.Route (L×Lattice d) (R×Lattice d)) :
    (BipartiteMatching.routePairs path).flatMap (fun pair => [Sum.inl pair.1.1,Sum.inr pair.2.1])=
      (path.map Prod.fst Prod.fst).allVertices := by
  induction path <;> simp_all [BipartiteMatching.routePairs,BlockingPath.Route.map,BlockingPath.Route.allVertices]

theorem short_augmenting_path {L R : Type} [DecidableEq L] [DecidableEq R] [Fintype L] [Fintype R] {d : Nat}
    (es : List (BipartiteEdge L R d)) (perfect : PerfectMatching es)
    (left : L × Lattice d → Option (R × Lattice d)) (right : R × Lattice d → Option (L × Lattice d))
    (matching : PeriodOneBipartitePartial es left right) :
    PerfectBipartitePartial left right ∨ ∃ pairs, IsShortBipartiteAugmentingPath es left right pairs := by
  let native := nativePartial es left right matching
  rcases PeriodicBipartite.perfect_or_short_augmenting (nativeEdges es) ((native_perfect es).mpr perfect) native with full | paths
  · exact Or.inl full
  · right
    obtain ⟨path⟩ := paths
    refine ⟨BipartiteMatching.routePairs path.route,pairs_nonempty _,?_,?_,?_,pairs_steps path.alternating,?_,?_⟩
    · intro pair member
      exact ⟨(native_adj es pair.1 pair.2).mp (pairs_adj path.alternating pair member),path.forward_unmatched pair.1 pair.2 member⟩
    · intro pair head
      rw [pairs_first _ pair head]
      exact path.free
    · intro pair last
      rw [pairs_last _ pair last]
      exact path.target_free
    · rw [pairs_projection]
      exact path.protoSimple
    · rw [pairs_length,←BlockingPath.Route.allVertices_length]
      exact path.length

end LeanTrominoes.GraphAlgorithmsAbstractBridge
