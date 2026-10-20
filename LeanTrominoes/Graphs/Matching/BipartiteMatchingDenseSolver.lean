/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDensePaths

/-! # Correctness of the dense matching solver -/
namespace LeanTrominoes.BipartiteMatching.DenseSearch
open BlockingPath
variable {L R : Type*} [DecidableEq L] [DecidableEq R]

def prepend : List (L × R) → Route L R → Route L R
  | [],suffix => suffix
  | (l,r)::rest,suffix => .cons l r (prepend rest suffix)

theorem prepend_append (a b : List (L × R)) (suffix : Route L R) :
    prepend (a++b) suffix=prepend a (prepend b suffix) := by
  induction a with
  | nil => rfl
  | cons edge rest ih => cases edge; simp [prepend,ih]

theorem prepend_pairs (prior : List (L × R)) (suffix : Route L R) :
    routePairs (prepend prior suffix)=prior++routePairs suffix := by
  induction prior with
  | nil => rfl
  | cons edge rest ih => cases edge; simp [prepend,routePairs,ih]

theorem Prefix.prepend {adj : L → R → Prop} {matching : State L R} {l : L} {prior : List (L × R)}
    (path : Prefix adj matching l prior) (suffix : Route L R) (begins : suffix.first=l)
    (alternating : Alternating adj matching suffix) :
    Alternating adj matching (prepend prior suffix) ∧ matching.left (prepend prior suffix).first=none := by
  induction path generalizing suffix with
  | start free => exact ⟨alternating,by simpa [DenseSearch.prepend,begins] using free⟩
  | @step l prior r next earlier edge mate ih =>
    have step := Alternating.cons edge (by simpa [begins] using mate) alternating
    simpa [prepend_append,DenseSearch.prepend] using ih (.cons l r suffix) rfl step

variable [Fintype L] [Fintype R]

def edgeBuckets (edges : List (L × R)) (l : L) : List R :=
  (edges.filter (fun e => e.1=l)).map Prod.snd

theorem mem_edgeBuckets (edges : List (L × R)) (l : L) (r : R) :
    r∈edgeBuckets edges l ↔ (l,r)∈edges := by
  simp only [edgeBuckets,List.mem_map,List.mem_filter,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨a,b⟩,⟨member,eq⟩,right⟩
    simp only [Prod.fst,Prod.snd] at eq right
    subst a; subst b; exact member
  · intro member
    exact ⟨(l,r),⟨member,rfl⟩,rfl⟩

def terminal (matching : State L R) (paths : Paths L R) (edges : List (L × R)) : Option (L × R) :=
  edges.find? (fun e => (paths e.1).isSome && (matching.right e.2).isNone)

def next (matching : State L R) (edges : List (L × R)) : Option (State L R) :=
  let paths := search matching edges (Fintype.card L)
  match terminal matching paths edges with
  | none => none
  | some (l,r) => some (applyRoute matching (prepend ((paths l).getD []) (.last l r)))

theorem terminal_spec (matching : State L R) (paths : Paths L R) (edges : List (L × R))
    (l : L) (r : R) (found : terminal matching paths edges=some (l,r)) :
    (l,r)∈edges ∧ reached paths l ∧ matching.right r=none := by
  have member := List.mem_of_find?_eq_some found
  have test := List.find?_some found
  have flags := Bool.and_eq_true_iff.mp test
  exact ⟨member,Option.isSome_iff_exists.mp flags.1,Option.isNone_iff_eq_none.mp flags.2⟩

theorem terminal_none (matching : State L R) (paths : Paths L R) (edges : List (L × R))
    (missing : terminal matching paths edges=none) (l : L) (r : R) (edge : (l,r)∈edges)
    (known : reached paths l) (free : matching.right r=none) : False := by
  have absent := List.find?_eq_none.mp missing (l,r) edge
  obtain ⟨prior,known⟩ := known
  simp [known,free] at absent

theorem next_spec (matching : State L R) (edges : List (L × R))
    (consistent : Consistent matching) (supported : Supported (fun l r => (l,r)∈edges) matching) :
    match next matching edges with
    | none => HasFiniteMatching (edgeBuckets edges) → Full matching
    | some result => Consistent result ∧ Supported (fun l r => (l,r)∈edges) result ∧ size result=size matching+1 := by
  have inv := search_invariant (fun l r => (l,r)∈edges) matching edges (fun _ h => h) (Fintype.card L)
  unfold next
  cases found : terminal matching (search matching edges (Fintype.card L)) edges with
  | none =>
    simp only [found]
    intro perfect
    by_contra imperfect
    obtain ⟨l,r,member,free,marked⟩ := search_complete edges matching consistent perfect imperfect
    exact terminal_none matching _ edges found l r member marked free
  | some edge =>
    obtain ⟨l,r⟩ := edge
    obtain ⟨member,⟨prior,marked⟩,free⟩ := terminal_spec matching _ edges l r found
    have path := (inv.path l prior marked).prepend (.last l r) rfl (Alternating.last member free)
    have simple : (prepend prior (.last l r)).vertices.Nodup := by
      rw [← routePairs_fst,prepend_pairs]
      simpa [routePairs] using inv.simple l prior marked
    simpa only [found,marked,Option.getD_some] using
      ⟨(applyRoute_correct (fun l r => (l,r)∈edges) matching _ consistent supported path.1 simple path.2).1,
       (applyRoute_correct (fun l r => (l,r)∈edges) matching _ consistent supported path.1 simple path.2).2,
       applyRoute_size (fun l r => (l,r)∈edges) matching consistent _ path.1 simple path.2⟩

def run (edges : List (L × R)) : Nat → State L R → Option (State L R)
  | 0,matching => some matching
  | fuel+1,matching => (next matching edges).bind (run edges fuel)

def solve (edges : List (L × R)) : Option (State L R) := run edges (Fintype.card L) empty

theorem full_iff_size (matching : State L R) : Full matching ↔ size matching=Fintype.card L := by
  have equal : domain matching=Finset.univ ↔ Full matching := by
    constructor
    · intro same l
      have member : l∈domain matching := by rw [same]; simp
      simpa [domain,Option.isSome_iff_ne_none] using member
    · intro full
      ext l
      simp [domain,Option.isSome_iff_ne_none,full l]
  rw [← equal]
  exact (Finset.card_eq_iff_eq_univ (domain matching)).symm

theorem run_spec (edges : List (L × R)) (fuel : Nat) (matching : State L R)
    (consistent : Consistent matching) (supported : Supported (fun l r => (l,r)∈edges) matching)
    (enough : size matching+fuel=Fintype.card L) :
    match run edges fuel matching with
    | none => ¬HasFiniteMatching (edgeBuckets edges)
    | some result => Consistent result ∧ Supported (fun l r => (l,r)∈edges) result ∧ Full result := by
  induction fuel generalizing matching with
  | zero => exact ⟨consistent,supported,(full_iff_size matching).mpr (by omega)⟩
  | succ fuel ih =>
    have step := next_spec matching edges consistent supported
    cases found : next matching edges with
    | none =>
      simp only [found] at step
      simp only [run,found,Option.bind_none]
      intro perfect
      have full := (full_iff_size matching).mp (step perfect)
      omega
    | some result =>
      simp only [found] at step
      simpa only [run,found,Option.bind_some] using ih result step.1 step.2.1 (by omega)

theorem solve_spec (edges : List (L × R)) :
    match solve edges with
    | none => ¬HasFiniteMatching (edgeBuckets edges)
    | some result => Consistent result ∧ Supported (fun l r => (l,r)∈edges) result ∧ Full result := by
  apply run_spec edges _ empty empty_consistent (empty_supported _)
  simp [size,domain,empty]

theorem solve_iff (edges : List (L × R)) (balanced : Fintype.card L=Fintype.card R) :
    (solve edges).isSome=true ↔ HasFiniteMatching (edgeBuckets edges) := by
  have spec := solve_spec edges
  cases found : solve edges with
  | none => simpa only [found,Option.isSome_none,Bool.false_eq_true,false_iff] using spec
  | some result =>
    simp only [found] at spec
    have supported : Supported (fun l r => r∈edgeBuckets edges l) result := by
      intro l r paired
      exact (mem_edgeBuckets edges l r).mpr (spec.2.1 l r paired)
    have perfect := full_equiv (edgeBuckets edges) result spec.1 supported balanced spec.2.2
    simp [perfect]

end LeanTrominoes.BipartiteMatching.DenseSearch
