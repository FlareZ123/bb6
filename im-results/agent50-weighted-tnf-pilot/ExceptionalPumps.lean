import BlockPump
import RootFrontier

set_option maxRecDepth 24000
set_option maxHeartbeats 0

namespace BB6Coverage.Agent50Exceptional
open BB6Coverage Agent50Zipper Agent50Pump BB6.Agent50RootFrontier

theorem never_of_arbitrary (p : PartialMachine)
    (h : ∀ n : Nat, ∃ k z, n≤k ∧ hrun p k ⟨0,[],[]⟩ = some z)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  intro n
  obtain ⟨k,z,hk,Hk⟩ := h n
  obtain ⟨h',H'⟩ := hrun_sound p k _ _ 0 Hk
  have H := zrun_sound p m hm k _ _ H'
  rw [blank_embed] at H
  rw [show k=n+(k-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some z => rfl

namespace Nested
abbrev P := bits "01"
abbrev K := bits "11"
abbrev Z0 := bits "00"
abbrev V := bits "1110"
abbrev W := bits "0101"
abbrev X := bits "10"
def table (w : Bool) : PackedTable := [some (some ⟨true,true,1⟩),some (some ⟨false,false,2⟩),some (some ⟨true,true,2⟩),some (some ⟨true,false,5⟩),some (some ⟨false,true,3⟩),some (some ⟨true,true,1⟩),some (some ⟨true,false,3⟩),some (some ⟨true,true,4⟩),some (some (if w then ⟨true,true,0⟩ else ⟨false,true,5⟩)),some (some ⟨false,false,1⟩),none,some (some ⟨false,false,0⟩)]
abbrev M (w : Bool) := unpackTable (table w)
def A (m : Nat) : HZ := ⟨0,[],rep P m⟩
def D (k j : Nat) : HZ := ⟨3,Z0++rep V k++rep K (j+1),[]⟩

theorem base (w : Bool) : hrun (M w) 9 ⟨0,[],[]⟩ = some (A 2) := by cases w <;> rfl

theorem initial (w : Bool) (m : Nat) : hrun (M w) (1+2*m+4) (A (m+1)) = some (D 0 (m+1)) := by
  have h1 := openRun_sound (M w) true false 1 ⟨0,[],P⟩ ⟨1,P,bits "1"⟩ [] (rep P m) (by simp) (by simp) (by cases w <;> rfl)
  have h2 := sweepR (M w) 1 (bits "1") P P K 2 (by cases w <;> rfl) m [] []
  have h3 := openRun_sound (M w) false true 4 ⟨1,P,bits "1"⟩ ⟨3,Z0++K++K,[]⟩ (rep K m) [] (by simp) (by simp) (by cases w <;> rfl)
  simp only [tail,List.nil_append,List.append_nil,List.append_assoc] at h1 h2 h3
  have H := hjoin (hjoin h1 h2) h3
  simpa only [A,D,rep,List.nil_append,List.append_assoc] using H

theorem inner (w : Bool) (k j : Nat) : hrun (M w) (8*k+10+6*k+6) (D k (j+1)) = some (D (k+1) j) := by
  have h1 := sweepL (M w) 3 Z0 V [] W 8 (by cases w <;> rfl) k (rep K (j+2)) []
  have h2 := openRun_sound (M w) false false 10 ⟨3,Z0++K++K,[]⟩ ⟨3,X++K,P⟩ (rep K j) (rep W k) (by simp) (by simp) (by cases w <;> rfl)
  have h3 := sweepR (M w) 3 P W X V 6 (by cases w <;> rfl) k (rep K (j+1)) []
  have h4 := openRun_sound (M w) false true 6 ⟨3,X,P⟩ ⟨3,Z0++V,[]⟩ (rep V k++rep K (j+1)) [] (by simp) (by simp) (by cases w <;> rfl)
  simp only [tail,List.nil_append,List.append_nil,List.append_assoc] at h1 h2 h3 h4
  have h12 : hrun (M w) (8*k+10) (D k (j+1)) = some ⟨3,X++rep K (j+1),P++rep W k⟩ := by
    apply hjoin h1
    simpa only [rep,List.append_assoc] using h2
  have H := hjoin (hjoin h12 h3) h4
  simpa only [D,rep,List.append_assoc] using H

theorem innerAll (w : Bool) (k j : Nat) : ∃ t, hrun (M w) t (D k j) = some (D (k+j) 0) := by
  induction j generalizing k with
  | zero => exact ⟨0,by simp [hrun]⟩
  | succ j ih =>
    obtain ⟨t,H⟩ := ih (k+1)
    exact ⟨8*k+10+6*k+6+t,by simpa only [show k+1+j=k+(j+1) by omega] using hjoin (inner w k j) H⟩

theorem double_rep (k : Nat) : rep W k = rep P (2*k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [show 2*(k+1)=2*k+1+1 by omega]; simp only [rep,ih,List.append_assoc]; rfl

theorem finish (w : Bool) (k : Nat) : hrun (M w) (8*k+6) (D k 0) = some (A (2*k+2)) := by
  have h1 := sweepL (M w) 3 Z0 V [] W 8 (by cases w <;> rfl) k K []
  have h2 := openRun_sound (M w) true false 6 ⟨3,Z0++K,[]⟩ ⟨0,[],W⟩ [] (rep W k) (by simp) (by simp) (by cases w <;> rfl)
  simp only [tail,List.nil_append,List.append_nil,List.append_assoc] at h1 h2
  have H := hjoin h1 h2
  have he : W = P++P := rfl
  rw [double_rep] at H
  simpa only [A,D,rep,List.nil_append,List.append_nil,double_rep,he,show 2*k+2=2*k+1+1 by omega,List.append_assoc] using H

theorem grow (w : Bool) (m : Nat) : ∃ t, 0<t ∧ hrun (M w) t (A (m+1)) = some (A (2*(m+1)+2)) := by
  obtain ⟨t,H⟩ := innerAll w 0 (m+1)
  simp only [Nat.zero_add] at H
  exact ⟨1+2*m+4+t+(8*(m+1)+6),by omega,hjoin (hjoin (initial w m) H) (finish w (m+1))⟩

theorem arbitrary (w : Bool) (n : Nat) : ∃ t m, n≤t ∧ hrun (M w) t ⟨0,[],[]⟩ = some (A (m+1)) := by
  induction n with
  | zero => exact ⟨9,1,by omega,base w⟩
  | succ n ih =>
    obtain ⟨t,m,ht,H⟩ := ih
    obtain ⟨u,hu,G⟩ := grow w m
    exact ⟨t+u,2*(m+1)+1,by omega,hjoin H G⟩

theorem never (w : Bool) (m : Machine) (hm : compatible (M w) m) : NeverHalts m := by
  apply never_of_arbitrary (M w) _ m hm
  intro n
  obtain ⟨t,k,ht,H⟩ := arbitrary w n
  exact ⟨t,A (k+1),ht,H⟩
#print axioms grow
#print axioms never
end Nested

namespace DoubleGrow
abbrev O := bits "1"
abbrev V := bits "010"
def table : PackedTable := [some (some ⟨true,true,1⟩),some (some ⟨true,false,0⟩),some (some ⟨true,true,2⟩),some (some ⟨true,false,5⟩),some (some ⟨false,true,3⟩),some (some ⟨true,true,2⟩),some (some ⟨true,false,3⟩),some (some ⟨true,true,4⟩),some (some ⟨false,false,4⟩),some (some ⟨false,false,1⟩),none,some (some ⟨false,false,0⟩)]
abbrev M := unpackTable table
def A (n : Nat) : HZ := ⟨0,[],rep O (n+2)++V++rep O (n+1)⟩
theorem base : hrun M 26 ⟨0,[],[]⟩ = some (A 0) := by rfl

theorem grow (n : Nat) : hrun M (5+(n+1)+13+(n+3)) (A n) = some (A (n+1)) := by
  have h1 := openRun_sound M true false 5 ⟨0,[],O⟩ ⟨2,bits "111",[]⟩ [] (rep O (n+1)++V++rep O (n+1)) (by simp) (by simp) (by rfl)
  have h2 := sweepR M 2 [] O (bits "111") O 1 (by rfl) (n+1) [] (V++rep O (n+1))
  have h3 := openRun_sound M false false 13 ⟨2,bits "111",V⟩ ⟨0,bits "11",V++O⟩ (rep O (n+1)) (rep O (n+1)) (by simp) (by simp) (by rfl)
  have h4 := sweepL M 0 [] O [] O 1 (by rfl) (n+3) [] (V++rep O (n+2))
  simp only [tail,List.nil_append,List.append_nil,List.append_assoc,Nat.one_mul] at h1 h2 h3 h4
  have H := hjoin (hjoin h1 h2) h3
  have he : bits "11" = O++O := rfl
  have h3' : hrun M (5+(n+1)+13) (A n) = some ⟨0,rep O (n+3),V++rep O (n+2)⟩ := by
    simpa only [A,rep,List.append_assoc,he] using H
  simpa only [A,List.append_assoc] using hjoin h3' h4

theorem arbitrary (n : Nat) : ∃ t k, n≤t ∧ hrun M t ⟨0,[],[]⟩ = some (A k) := by
  induction n with
  | zero => exact ⟨26,0,by omega,base⟩
  | succ n ih =>
    obtain ⟨t,k,ht,H⟩ := ih
    exact ⟨t+(5+(k+1)+13+(k+3)),k+1,by omega,hjoin H (grow k)⟩

theorem never (m : Machine) (hm : compatible M m) : NeverHalts m := by
  apply never_of_arbitrary M _ m hm
  intro n
  obtain ⟨t,k,ht,H⟩ := arbitrary n
  exact ⟨t,A k,ht,H⟩
#print axioms grow
#print axioms never
end DoubleGrow
end BB6Coverage.Agent50Exceptional
