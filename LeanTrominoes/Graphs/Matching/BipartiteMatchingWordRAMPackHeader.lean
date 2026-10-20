/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingWordRAMPackMetadata

/-! # Checked cold-input header stores and invocation registers -/
namespace LeanTrominoes.BipartiteMatching.PackWordRAM
open ComplexityAbstract.RAM

private def put (data : Data 128) (reg : Fin 128) (value : Int) : Data 128 := (Function.update data.1 reg value,data.2)
private def write (data : Data 128) (address : Nat) (value : Int) : Data 128 := (data.1,Function.update data.2 address value)

private theorem constant_exec {w : Nat} (data : Data 128) (reg : Fin 128) (value : Int) (fits : Fits w value) :
    Structured.Exec w (.atom (.constant reg value)) data (put data reg value) 1 := by
  exact .atom (by simp [Structured.Primitive.eval,put,fits])
private theorem arithmetic_exec {w : Nat} (data : Data 128) (op : Arithmetic) (dst left right : Fin 128)
    (value : Int) (equal : op.eval (data.1 left) (data.1 right)=value) (fits : Fits w value) :
    Structured.Exec w (.atom (.arithmetic op dst left right)) data (put data dst value) 1 := by
  exact .atom (by simp [Structured.Primitive.eval,put,equal,fits])
private theorem register_copy_exec {w : Nat} (data : Data 128) (dst src : Fin 128) (value : Int)
    (equal : data.1 src=value) (fits : Fits w value) :
    Structured.Exec w (.atom (.copy dst src)) data (put data dst value) 1 := by
  exact .atom (by simp [Structured.Primitive.eval,put,equal,fits])
private theorem store_exec {w address : Nat} (data : Data 128) (pointer src : Fin 128) (value : Int)
    (pointerEq : data.1 pointer=address) (valueEq : data.1 src=value)
    (addressFits : Fits w address) (valueFits : Fits w value) :
    Structured.Exec w (.atom (.store pointer src)) data (write data address value) 1 := by
  have range := Allocation.nat_address addressFits
  have castRange : (address : Int)<2^w := by exact_mod_cast range
  exact .atom (by simp [Structured.Primitive.eval,write,pointerEq,valueEq,valueFits,not_le.mpr castRange])

def footerCode : Structured.Code 128 :=
  .seq (.atom (.constant 0 0)) <| .seq (.atom (.constant 1 2)) <|
  .seq (.atom (.arithmetic .mul 1 83 1)) <| .seq (.atom (.constant 2 3)) <|
  .seq (.atom (.arithmetic .add 1 1 2)) <| .seq (.atom (.store 0 1)) <|
  .seq (.atom (.constant 0 1)) <| .seq (.atom (.store 0 84)) <|
  .seq (.atom (.constant 0 2)) <| .seq (.atom (.store 0 84)) <|
  .seq (.atom (.constant 0 3)) <| .seq (.atom (.store 0 83)) <|
  .seq (.atom (.constant 0 1)) <| .seq (.atom (.arithmetic .add 1 1 0)) <|
  .seq (.atom (.copy 2 1)) (.atom (.copy 5 85))

theorem footer_exec {n edges w : Nat} (data : Data 128)
    (nValue : data.1 84=n) (edgesValue : data.1 83=edges) (capValue : data.1 85=coldCapacity n edges)
    (capFits : Fits w (coldCapacity n edges)) :
    ∃ result, Structured.Exec w footerCode data result 16 ∧
      result.2=headerMemory data.2 n edges ∧ result.1 1=(4+2*edges : Nat) ∧
      result.1 2=(4+2*edges : Nat) ∧ result.1 5=coldCapacity n edges ∧
      (∀ reg : Fin 128, reg≠0 → reg≠1 → reg≠2 → reg≠5 → result.1 reg=data.1 reg) := by
  let base := 2*n+edges+3
  have positive : 1≤base := by dsimp [base]; omega
  have power : base≤base^8 := by simpa only [pow_one] using (pow_le_pow_right₀ positive (show 1≤8 by decide))
  have scaled := Nat.mul_le_mul_left 4 power
  have room : 4+2*edges≤coldCapacity n edges := by dsimp [base] at scaled; unfold coldCapacity; omega
  have word (x : Nat) (bound : x≤4+2*edges) : Fits w x := Allocation.nat_fits_le capFits (bound.trans room)
  have small0 := word 0 (by omega)
  have small1 := word 1 (by omega)
  have small2 := word 2 (by omega)
  have small3 := word 3 (by omega)
  have doubled := word (2*edges) (by omega)
  have headerLength := word (2*edges+3) (by omega)
  have start := word (2*edges+4) (by omega)
  have nFits : Fits w n := by
    apply Allocation.nat_fits_le capFits
    have basePow := Nat.mul_le_mul_left 4 power
    dsimp [base] at basePow
    unfold coldCapacity
    omega
  have edgeFits := word edges (by omega)
  let a := put data 0 0
  let b := put a 1 2
  let c := put b 1 (2*edges : Nat)
  let e := put c 2 3
  let f := put e 1 (2*edges+3 : Nat)
  let g := write f 0 (2*edges+3 : Nat)
  let h := put g 0 1
  let i := write h 1 n
  let j := put i 0 2
  let k := write j 2 n
  let l := put k 0 3
  let m := write l 3 edges
  let p := put m 0 1
  let q := put p 1 (2*edges+4 : Nat)
  let r := put q 2 (2*edges+4 : Nat)
  let result := put r 5 (coldCapacity n edges)
  have t1 := constant_exec data 0 0 small0
  have t2 := constant_exec a 1 2 small2
  have t3 := arithmetic_exec b .mul 1 83 1 (2*edges : Nat) (by simp [b,a,put,edgesValue,Arithmetic.eval]; ring) doubled
  have t4 := constant_exec c 2 3 small3
  have t5 := arithmetic_exec e .add 1 1 2 (2*edges+3 : Nat) (by simp [e,c,put,Arithmetic.eval,Nat.cast_add,Nat.cast_mul]) headerLength
  have t6 := store_exec f 0 1 (2*edges+3 : Nat) (by simp [f,e,c,b,a,put]) (by simp [f,put]) small0 headerLength
  have t7 := constant_exec g 0 1 small1
  have t8 := store_exec h 0 84 n (by simp [h,put]) (by simp [h,g,f,e,c,b,a,put,write,nValue]) small1 nFits
  have t9 := constant_exec i 0 2 small2
  have t10 := store_exec j 0 84 n (by simp [j,put]) (by simp [j,i,h,g,f,e,c,b,a,put,write,nValue]) small2 nFits
  have t11 := constant_exec k 0 3 small3
  have t12 := store_exec l 0 83 edges (by simp [l,put]) (by simp [l,k,j,i,h,g,f,e,c,b,a,put,write,edgesValue]) small3 edgeFits
  have t13 := constant_exec m 0 1 small1
  have t14 := arithmetic_exec p .add 1 1 0 (2*edges+4 : Nat)
    (by simp [p,m,l,k,j,i,h,g,f,put,write,Arithmetic.eval,Nat.cast_add,Nat.cast_mul]; ring) start
  have t15 := register_copy_exec q 2 1 (2*edges+4 : Nat) (by simp [q,put]) start
  have t16 := register_copy_exec r 5 85 (coldCapacity n edges)
    (by simp [r,q,p,m,l,k,j,i,h,g,f,e,c,b,a,put,write,capValue]) capFits
  refine ⟨result,t1.seq (t2.seq (t3.seq (t4.seq (t5.seq (t6.seq (t7.seq (t8.seq (t9.seq (t10.seq (t11.seq (t12.seq (t13.seq (t14.seq (t15.seq t16)))))))))))))),?_,?_,?_,?_,?_⟩
  · simp [result,r,q,p,m,l,k,j,i,h,g,f,e,c,b,a,put,write,headerMemory,Nat.add_comm]
  · simp [result,r,q,put,Nat.cast_add]; ring
  · simp [result,r,put,Nat.cast_add]; ring
  · simp [result,put]
  · intro reg ne0 ne1 ne2 ne5
    simp [result,r,q,p,m,l,k,j,i,h,g,f,e,c,b,a,put,write,Function.update_of_ne,ne0,ne1,ne2,ne5]

def headerCode (d : Nat) : Structured.Code 128 := .seq (metadataCode d) footerCode

theorem header_exec {n d edges w : Nat} (data : Data 128)
    (nValue : data.1 66=n) (edgesValue : data.1 83=edges)
    (capFits : Fits w (coldCapacity (vertexCount n d) edges)) (phaseFits : Fits w (2^d : Nat)) :
    ∃ result, Structured.Exec w (headerCode d) data result 47 ∧
      result.2=headerMemory data.2 (vertexCount n d) edges ∧
      result.1 1=(4+2*edges : Nat) ∧ result.1 2=(4+2*edges : Nat) ∧
      result.1 5=coldCapacity (vertexCount n d) edges ∧
      result.1 84=vertexCount n d ∧ result.1 85=coldCapacity (vertexCount n d) edges ∧
      (∀ reg : Fin 128, 64≤reg.val → reg.val<84 → result.1 reg=data.1 reg) := by
  obtain ⟨middle,first,memory,N,cap,fixed⟩ := metadata_exec data nValue edgesValue capFits phaseFits
  have edgeEq : middle.1 83=edges := (fixed _ (by decide) (by decide) (by decide)).trans edgesValue
  obtain ⟨result,later,stored,start,start2,capacity,lastFixed⟩ := footer_exec middle N edgeEq cap capFits
  refine ⟨result,first.seq later,by simpa only [memory] using stored,start,start2,capacity,?_,?_,?_⟩
  · rw [lastFixed _ (by decide) (by decide) (by decide) (by decide)]; exact N
  · rw [lastFixed _ (by decide) (by decide) (by decide) (by decide)]; exact cap
  · intro reg lower upper
    have ne (value : Fin 128) (bound : value.val<64) : reg≠value := by intro same; have := congrArg Fin.val same; omega
    rw [lastFixed reg (ne _ (by decide)) (ne _ (by decide)) (ne _ (by decide)) (ne _ (by decide))]
    apply fixed reg (by omega)
    all_goals intro same; have := congrArg Fin.val same; change reg.val=_ at this; omega

end LeanTrominoes.BipartiteMatching.PackWordRAM
