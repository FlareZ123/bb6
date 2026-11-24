import Q0LocalFilters

namespace BB429Q0Macro
set_option maxHeartbeats 4000000

def rowState (s : Int × Int) : BB429.State :=
  (s.1.toNat,(s.2-2*s.1).toNat)

private theorem rowState_ar (a H : Int) (A S : Nat)
    (ha : a=A) (hh : H=S) : rowState (a,H)=stateAR A S := by
  unfold rowState stateAR
  congr 1 <;> omega

/-- Every row in the integer formula table corresponds to the actual
    accelerator run, with no omitted branch guard. -/
theorem macro_trace (d : Digit) (x r X R k : Nat)
    (hx : 400≤x) (hc : 3*x≤r) (hr : r=R+cost d)
    (he : 16*X+offset d=x+digit d*r) (hk : k≤4) :
    BB429.run k (original X R)=some (rowState ((rows d X R).getD k (0,0))) := by
  have hcases : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by omega
  cases d <;> simp [digit,cost,offset] at hr he
  · let s0 := original X R
    let s1 := stateAR (8*X-3) (4*R+2)
    let s2 := stateAR (16*X-3) (4*R+5)
    let s3 := stateAR (32*X-3) (4*R+8)
    let s4 := original x r
    have h1 : BB429.next s0=some s1 := by dsimp [s0,s1,original]; apply invF_rank <;> omega
    have h2 : BB429.next s1=some s2 := by dsimp [s1,s2]; apply invF_rank <;> omega
    have h3 : BB429.next s2=some s3 := by dsimp [s2,s3]; apply invF_rank <;> omega
    have h4 : BB429.next s3=some s4 := by dsimp [s3,s4,original]; apply invF_rank <;> omega
    change BB429.run k s0=some _
    rcases hcases with h|h|h|h|h <;> subst k <;>
      simp only [BB429.run,h1,h2,h3,h4,Option.bind_some] <;>
      simp [rows,List.getD,s0,s1,s2,s3,s4,original] <;>
      symm <;> apply rowState_ar <;> omega
  · let s0 := original X R
    let s1 := stateAR (8*X-3) (4*R+2)
    let s2 := stateAR (16*X-3) (4*R+5)
    let s3 := stateAR (32*X-2*R-1) (4*R+16)
    let s4 := original x r
    have h1 : BB429.next s0=some s1 := by dsimp [s0,s1,original]; apply invF_rank <;> omega
    have h2 : BB429.next s1=some s2 := by dsimp [s1,s2]; apply invF_rank <;> omega
    have h3 : BB429.next s2=some s3 := by dsimp [s2,s3]; apply invS_rank <;> omega
    have h4 : BB429.next s3=some s4 := by dsimp [s3,s4,original]; apply invF_rank <;> omega
    change BB429.run k s0=some _
    rcases hcases with h|h|h|h|h <;> subst k <;>
      simp only [BB429.run,h1,h2,h3,h4,Option.bind_some] <;>
      simp [rows,List.getD,s0,s1,s2,s3,s4,original] <;>
      symm <;> apply rowState_ar <;> omega
  · let s0 := original X R
    let s1 := stateAR (8*X-2*R-2) (4*R+6)
    let s2 := stateAR (16*X-4*R-1) (4*R+9)
    let s3 := stateAR (32*X-8*R+1) (4*R+12)
    let s4 := original x r
    have h1 : BB429.next s0=some s1 := by dsimp [s0,s1,original]; apply invE_rank <;> omega
    have h2 : BB429.next s1=some s2 := by dsimp [s1,s2]; apply invF_rank <;> omega
    have h3 : BB429.next s2=some s3 := by dsimp [s2,s3]; apply invF_rank <;> omega
    have h4 : BB429.next s3=some s4 := by dsimp [s3,s4,original]; apply invF_rank <;> omega
    change BB429.run k s0=some _
    rcases hcases with h|h|h|h|h <;> subst k <;>
      simp only [BB429.run,h1,h2,h3,h4,Option.bind_some] <;>
      simp [rows,List.getD,s0,s1,s2,s3,s4,original] <;>
      symm <;> apply rowState_ar <;> omega
  · let s0 := original X R
    let s1 := stateAR (8*X-2*R-2) (4*R+6)
    let s2 := stateAR (16*X-4*R-1) (4*R+9)
    let s3 := stateAR (32*X-10*R+1) (4*R+20)
    let s4 := original x r
    have h1 : BB429.next s0=some s1 := by dsimp [s0,s1,original]; apply invE_rank <;> omega
    have h2 : BB429.next s1=some s2 := by dsimp [s1,s2]; apply invF_rank <;> omega
    have h3 : BB429.next s2=some s3 := by dsimp [s2,s3]; apply invS_rank <;> omega
    have h4 : BB429.next s3=some s4 := by dsimp [s3,s4,original]; apply invF_rank <;> omega
    change BB429.run k s0=some _
    rcases hcases with h|h|h|h|h <;> subst k <;>
      simp only [BB429.run,h1,h2,h3,h4,Option.bind_some] <;>
      simp [rows,List.getD,s0,s1,s2,s3,s4,original] <;>
      symm <;> apply rowState_ar <;> omega

#print axioms macro_trace
end BB429Q0Macro

namespace BB429Q0Macro

private theorem rows_length (d : Digit) (X R : Int) : (rows d X R).length=5 := by
  cases d <;> rfl

private theorem rows_nonneg (d : Digit) (x r X R : Nat)
    (hx : 400≤x) (hc : 3*x≤r) (hr : r=R+cost d)
    (he : 16*X+offset d=x+digit d*r) :
    ∀ s ∈ rows d X R, 0≤s.1 ∧ 2*s.1≤s.2 := by
  intro s hs
  cases d <;> simp [rows,digit,cost,offset] at * <;>
    rcases hs with h|h|h|h|h <;> subst s <;> simp <;> omega

private theorem rows_getD_mem (d : Digit) (X R : Int) (k : Nat) (hk : k≤4) :
    (rows d X R).getD k (0,0) ∈ rows d X R := by
  have hcases : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by omega
  cases d <;> rcases hcases with h|h|h|h|h <;> subst k <;> simp [rows,List.getD]

private theorem rowOK_state (s : Int × Int) (hs : rowOK s)
    (ha : 0≤s.1) (hb : 2*s.1≤s.2) :
    localFilters (rowState s).1 (rowState s).2 := by
  unfold rowOK at hs
  unfold rowState
  simp only
  rw [Int.toNat_of_nonneg ha,Int.toNat_of_nonneg (by omega : 0≤s.2-2*s.1)]
  exact hs

/-- The residue tests are redundant in all five actual rows of the
    second macro of a genuine cone chain; no root assumption is needed. -/
theorem two_macro_source_filters (e d : Digit) (x r X R Z T k : Nat)
    (hx : 400≤x) (hc : 3*x≤r) (hr : r=R+cost d)
    (he : 16*X+offset d=x+digit d*r)
    (hr' : R=T+cost e) (he' : 16*Z+offset e=X+digit e*R)
    (hk : k≤4) {s : BB429.State}
    (hRun : BB429.run (4+k) (original Z T)=some s)
    (hX : 400≤X) (hC : 3*X≤R) :
    localFilters s.1 s.2 := by
  have hX' : (X:Int)=shiftedX e Z T := by
    cases e <;> simp [shiftedX,digit,cost,offset] at * <;> omega
  have hR' : (R:Int)=shiftedR e T := by
    cases e <;> simp [shiftedR,cost] at * <;> omega
  have first := macro_converse e X R Z T hX hC hr' he'
  have second := macro_trace d x r X R k hx hc hr he hk
  rw [BB429.run_add,first] at hRun
  simp only [Option.bind_some] at hRun
  rw [second] at hRun
  have hs : s=rowState ((rows d X R).getD k (0,0)) := by simpa using hRun.symm
  subst s
  have hm := rows_getD_mem d X R k hk
  have hp := rows_nonneg d x r X R hx hc hr he _ hm
  apply rowOK_state _ _ hp.1 hp.2
  rw [hX',hR'] at hm ⊢
  exact two_macro_filters e d Z T _ hm

#print axioms two_macro_source_filters
end BB429Q0Macro
