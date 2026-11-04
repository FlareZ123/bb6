import Parents

namespace CascadeResetInverse

private def cap (u:Nat) := Nat.log2 (2*u+6)+1
private def evenHeight (u k:Nat) := 2*u-8*2^k-k
private def oddHeight (u k t:Nat) :=
  2*(2^t*((2*u+5)/(3^(t+1))))-8*2^k-k-5

private def evenOK (u k:Nat) : Bool :=
  let h := evenHeight u k
  decide (6*2^k-1≤u ∧ u≤8*2^k-3 ∧ 2*u=8*2^k+h+k)
private def oddFactorOK (u t:Nat) : Bool :=
  let d := (2*u+5)/(3^(t+1))
  decide (d%2=1 ∧ 2*u+5=3^(t+1)*d)
private def oddBandOK (u k t:Nat) : Bool :=
  let d := (2*u+5)/(3^(t+1))
  let h := oddHeight u k t
  decide (6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1 ∧
    2*(2^t*d)=8*2^k+h+k+5)

private def evens (u:Nat) : List Nat :=
  (List.range (cap u)).flatMap fun k =>
     if evenOK u k then [evenHeight u k] else []
private def odds (u:Nat) : List Nat :=
  (List.range (cap u)).flatMap fun t =>
     if oddFactorOK u t then
       (List.range (cap u)).flatMap fun k =>
         if oddBandOK u k t then [oddHeight u k t] else []
     else []

/-- Direct one-pass evaluation of algebraically valid first-reset parents:
    each dyadic/valuation witness is checked once, avoiding the exhaustive
    rechecking of each candidate in the older parents implementation. -/
def fastParents (u:Nat) : List Nat := evens u ++ odds u

private theorem pow_small (u k:Nat) (hk:2^k≤2*u+6):k<cap u := by
  have hn:2*u+6≠0 := by omega
  have hh := (Nat.le_log2 hn).mpr hk
  dsimp [cap]
  omega

private theorem three_base (t:Nat):2^t≤3^(t+1):=by
  induction t with
  | zero => decide
  | succ t ih => rw [Nat.pow_succ,Nat.pow_succ];omega

private theorem factor_div (u t d:Nat) (he:2*u+5=3^(t+1)*d) :
  (2*u+5)/3^(t+1)=d := by
  rw [he]
  exact Nat.mul_div_cancel_left d (Nat.pow_pos (by decide))

private theorem mem_choice (flag:Bool) (x y:Nat):
    x ∈ (if flag then [y] else []) ↔ flag=true ∧ x=y := by
  cases flag <;> simp

/-- Source-equivalent complete reset-parent enumeration at every natural
    height, with no fixed bit limit or unverified first-return assumptions. -/
theorem fastParents_iff (h u:Nat) : h ∈ fastParents u ↔ ResetParent h u := by
  constructor
  · intro hh
    rcases List.mem_append.mp hh with he|ho
    · obtain ⟨k,hk,hval⟩ := List.mem_flatMap.mp he
      have hyes : evenOK u k=true ∧ h=evenHeight u k :=
        (mem_choice (evenOK u k) h (evenHeight u k)).mp hval
      have hev : 6*2^k-1≤u ∧ u≤8*2^k-3 ∧ 2*u=8*2^k+evenHeight u k+k :=
        of_decide_eq_true hyes.1
      left
      exact ⟨k,⟨hev.1,hev.2.1⟩,by rw [hyes.2]; exact hev.2.2⟩
    · obtain ⟨t,ht,hval⟩ := List.mem_flatMap.mp ho
      have hfac : oddFactorOK u t=true := by
        cases hf : oddFactorOK u t with
        | false => simp [hf] at hval
        | true => rfl
      simp only [if_pos hfac] at hval
      obtain ⟨k,hk,hval⟩ := List.mem_flatMap.mp hval
      have hband : oddBandOK u k t=true ∧ h=oddHeight u k t :=
        (mem_choice (oddBandOK u k t) h (oddHeight u k t)).mp hval
      let d := (2*u+5)/(3^(t+1))
      have hv : d%2=1 ∧ 2*u+5=3^(t+1)*d := of_decide_eq_true hfac
      have hb : 6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1 ∧
          2*(2^t*d)=8*2^k+oddHeight u k t+k+5 := of_decide_eq_true hband.1
      right
      exact ⟨k,t,d,hv.1,⟨hb.1,hb.2.1⟩,hv.2,by rw [hband.2]; exact hb.2.2⟩
  · intro hh
    rcases hh with ⟨k,⟨hl,hu⟩,heq⟩ | ⟨k,t,d,hd,⟨hl,hu⟩,heq,hq⟩
    · have hpow:1≤2^k := Nat.one_le_pow k 2 (by decide)
      have hkbound:2^k≤2*u+6 := by omega
      have heven:h=evenHeight u k := by dsimp [evenHeight];omega
      apply List.mem_append.mpr
      left
      apply List.mem_flatMap.mpr
      refine ⟨k,List.mem_range.mpr (pow_small u k hkbound),?_⟩
      apply (mem_choice (evenOK u k) h (evenHeight u k)).mpr
      constructor
      · apply decide_eq_true
        rw [←heven]
        exact ⟨hl,hu,heq⟩
      · exact heven
    · have hd1:1≤d := by omega
      have hb1:=Nat.mul_le_mul_right d (three_base t)
      have hqbounded:2^t*d≤2*u+5 := by omega
      have hkbound:2^k≤2*u+6 := by omega
      have htp:=Nat.mul_le_mul_left (2^t) hd1
      have htbound:2^t≤2*u+6 := by omega
      have hdiv:=factor_div u t d heq
      have hodd:h=oddHeight u k t := by
        dsimp [oddHeight]
        rw [hdiv]
        omega
      apply List.mem_append.mpr
      right
      apply List.mem_flatMap.mpr
      refine ⟨t,List.mem_range.mpr (pow_small u t htbound),?_⟩
      have hfactor : oddFactorOK u t=true := by
        apply decide_eq_true
        rw [hdiv]
        exact ⟨hd,heq⟩
      simp only [if_pos hfactor]
      apply List.mem_flatMap.mpr
      refine ⟨k,List.mem_range.mpr (pow_small u k hkbound),?_⟩
      apply (mem_choice (oddBandOK u k t) h (oddHeight u k t)).mpr
      constructor
      · apply decide_eq_true
        rw [hdiv,←hodd]
        exact ⟨hl,hu,hq⟩
      · exact hodd

#print axioms fastParents_iff
end CascadeResetInverse
