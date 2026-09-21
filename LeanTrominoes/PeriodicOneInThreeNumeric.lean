/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicExactOneInjectiveRenaming
import LeanTrominoes.PeriodicOneInThreeCorrectness
import LeanTrominoes.PeriodicOneInThreeOccurrences
import LeanTrominoes.PeriodicOneInThreeOneDimensional
import LeanTrominoes.PeriodicOneInThreeComputability
import LeanTrominoes.PeriodicCNFTransition

/-! # Compact numeric atoms for the Figure 7 exact-one reduction

Original atoms use even codes. Active auxiliaries use codes linear in their
source clause index. The unused auxiliary names occupy a disjoint residue
class, making the renaming globally injective.
-/
noncomputable section
namespace LeanTrominoes.PeriodicOneInThree.Numeric

def kindCode : OneInThreeAux → Nat
  | .firstChoice => 0
  | .secondChoice => 1
  | .firstSlack => 2
  | .secondSlack => 3
  | .firstPadding => 4
  | .secondPadding => 5
  | .thirdPadding => 6

theorem kindCode_lt (k : OneInThreeAux) : kindCode k < 7 := by cases k <;> decide

theorem kindCode_injective : Function.Injective kindCode := by
  intro a b h
  cases a <;> cases b <;> simp_all [kindCode]

abbrev Auxiliary := (Nat × PeriodicClause Nat) × OneInThreeAux

def auxiliaryCode (source : PeriodicCNF Nat) (a : Auxiliary) : Nat :=
  if source.clauses[a.1.1]? = some a.1.2 then
    4*(7*a.1.1+kindCode a.2)+1
  else 4*Encodable.encode a+3

theorem auxiliaryCode_odd (source : PeriodicCNF Nat) (a : Auxiliary) :
    auxiliaryCode source a % 2 = 1 := by
  unfold auxiliaryCode
  split <;> omega

theorem auxiliaryCode_injective (source : PeriodicCNF Nat) :
    Function.Injective (auxiliaryCode source) := by
  rintro ⟨⟨i,c⟩,k⟩ ⟨⟨j,d⟩,l⟩ h
  have hk := kindCode_lt k
  have hl := kindCode_lt l
  by_cases hi : source.clauses[i]?=some c <;> by_cases hj : source.clauses[j]?=some d
  · simp only [auxiliaryCode,hi,hj,if_true] at h
    have ij : i=j := by omega
    have kl : k=l := kindCode_injective (by omega)
    subst j
    have cd : c=d := Option.some.inj (hi.symm.trans hj)
    subst d; subst l; rfl
  · simp only [auxiliaryCode,hi,hj,if_true,if_false] at h
    omega
  · simp only [auxiliaryCode,hi,hj,if_true,if_false] at h
    omega
  · simp only [auxiliaryCode,hi,hj,if_false] at h
    exact Encodable.encode_injective (by omega)

def atomMap (source : PeriodicCNF Nat) : OneInThreeVariable Nat → Nat
  | .inl a => 2*a
  | .inr a => auxiliaryCode source a

theorem atomMap_injective (source : PeriodicCNF Nat) : Function.Injective (atomMap source) := by
  intro a b h
  cases a with
  | inl a => cases b with
    | inl b => have : a=b := by change 2*a=2*b at h; omega
               exact congrArg Sum.inl this
    | inr b => have hb := auxiliaryCode_odd source b
               change 2*a=auxiliaryCode source b at h
               omega
  | inr a => cases b with
    | inl b => have ha := auxiliaryCode_odd source a
               change auxiliaryCode source a=2*b at h
               omega
    | inr b => exact congrArg Sum.inr (auxiliaryCode_injective source h)

def formula (source : PeriodicCNF Nat) : PeriodicCNF Nat :=
  (PeriodicOneInThree.formula source).rename (atomMap source)

theorem satisfiable_iff (source : PeriodicCNF Nat) (hw : source.WidthAtMost 3) :
    Satisfiable (formula source) ↔ source.Satisfiable := by
  rw [formula,satisfiable_rename_iff _ _ (atomMap_injective source)]
  exact (PeriodicOneInThree.satisfiable_iff source hw).symm

theorem width_three (source : PeriodicCNF Nat) : (formula source).WidthAtMost 3 :=
  (PeriodicCNF.width_rename _ _ 3).mpr (formula_widthAtMostThree source)

theorem oneDimensional (source : PeriodicCNF Nat) (h : source.IsOneDimensional) :
    (formula source).IsOneDimensional :=
  (PeriodicCNF.oneDimensional_rename _ _).mpr (formula_isOneDimensional h)

theorem occurrences_three (source : PeriodicCNF Nat) (hw : source.WidthAtMost 3)
    (ho : source.OccurrencesAtMost 3) : (formula source).OccurrencesAtMost 3 := by
  apply PeriodicCNF.occurrences_rename _ _ (atomMap_injective source) 3
  exact PeriodicCNF.occurrencesAtMost_congr_beq _ _ _ _ _ _ (formula_occurrencesAtMostThree source hw ho)

theorem auxiliaryCode_active (source : PeriodicCNF Nat) (i : Nat)
    (c : PeriodicClause Nat) (h : source.clauses[i]?=some c) (k : OneInThreeAux) :
    auxiliaryCode source ((i,c),k) = 28*i+4*kindCode k+1 := by
  simp only [auxiliaryCode,h,if_true]
  omega

theorem rename_auxiliary (source : PeriodicCNF Nat) (i : Nat)
    (c : PeriodicClause Nat) (h : source.clauses[i]?=some c) (k : OneInThreeAux) (v : Bool) :
    (auxiliary i c k v).rename (atomMap source) =
      ⟨28*i+4*kindCode k+1,anchor c,v⟩ := by
  simp only [auxiliary,PeriodicLiteral.rename,atomMap,auxiliaryCode_active source i c h k]

theorem forward (source : PeriodicCNF Nat) (h : source.IsForwardLocal) :
    (formula source).IsForwardLocal := by
  have raw : (PeriodicOneInThree.formula source).IsForwardLocal := by
    intro c hc l hl
    simp only [PeriodicOneInThree.formula,List.mem_flatMap] at hc
    obtain ⟨⟨original,i⟩,mem,hc⟩ := hc
    have supported := clauseClauses_supported i original c hc l hl
    have originalMem := List.fst_mem_of_mem_zipIdx mem
    rcases supported with ⟨old,oldMem,offset⟩ | offset
    · simpa only [PeriodicLiteral.IsForwardLocal,offset] using h original originalMem old oldMem
    · cases original with
      | nil => simp [PeriodicLiteral.IsForwardLocal,offset,anchor]
      | cons first rest =>
        have firstForward := h (first::rest) originalMem first (by simp)
        simpa [PeriodicLiteral.IsForwardLocal,offset,anchor] using firstForward
  simpa [formula,PeriodicCNF.rename,PeriodicCNF.renameClause,PeriodicCNF.IsForwardLocal,
    PeriodicLiteral.IsForwardLocal,PeriodicLiteral.rename] using raw

theorem localOnLine (source : PeriodicCNF Nat) (hd : source.IsOneDimensional)
    (hl : source.IsLocalOnLine) : (formula source).IsLocalOnLine := by
  apply (PeriodicCNF.localOnLine_rename _ _).mpr
  apply (PeriodicCNF.isLocal_iff_isLocalOnLine (formula_isOneDimensional hd)).mp
  exact formula_isLocal ((PeriodicCNF.isLocal_iff_isLocalOnLine hd).mpr hl)

end LeanTrominoes.PeriodicOneInThree.Numeric
