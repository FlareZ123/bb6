import Lean.Elab.Tactic.Omega

/-! A local exact copy of BB6.Agent46.sectionPreimageAll. This file is
self-contained and kernel-compiles independently of the source import graph.
The original source's section_preimage_all_iff transfers its theorem to secNext. -/
namespace BB6.Agent34Cone

def sectionPreimageAll (a k x y : Nat) : Prop :=
  if a=0 then
    if k=0 then False
    else if k=1 then x=0 ∧ y=4
    else 4≤y ∧ ∃ n:Nat,
      x+y=2^n*8 ∧ (2*k+1)+8+3*n=x+2*y
  else if a=1 then
    if k=0 then x=5 ∧ y=1
    else if k=1 then x=2 ∧ y=3
    else if k=2 then x=2 ∧ y=5
    else if k=3 then x=0 ∧ y=7
    else
      (y=3 ∧ ∃ n:Nat, x+6=2^n*16 ∧
        (2*k-3)+16+3*n=x+10) ∨
      (5≤y ∧ ∃ n:Nat, x+y+1=2^n*16 ∧
        (2*k-3)+16+3*n=x+2*y+2)
  else if k=0 then x=a-2 ∧ y=2
  else if 2*k≤a then x=a-2*k ∧ y=2*k+2
  else if a%2=0 then
    4≤y ∧ ∃ n:Nat,
      x+y=2^n*(2*(a-1)+6) ∧
      (2*k-a+3)+(2*(a-1)+6)+3*n=x+2*y
  else
    (y=3 ∧ ∃ n:Nat, x+6=2^n*(2*(a-1)+8) ∧
      (2*k-a+3)+(2*(a-1)+8)+3*n=x+10) ∨
    (5≤y ∧ ∃ n:Nat,
      x+y+1=2^n*(2*(a-1)+8) ∧
      (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2)

private theorem depth_small (a x y n : Nat)
    (ha : 2 ≤ a) (he : a%2=0)
    (hx : x%64=5) (hy : y%64=43)
    (hs : x+y=2^n*(2*(a-1)+6)) : n<3 := by
  by_cases h : n<3
  · exact h
  have hn : 3 ≤ n := by omega
  have hpow : 8 ∣ (2:Nat)^n := by
    change (2:Nat)^3 ∣ 2^n
    exact Nat.pow_dvd_pow 2 hn
  obtain ⟨u,hu⟩ := hpow
  have hfour : 4 ∣ 2*(a-1)+6 := by
    refine ⟨a/2+1,?_⟩
    omega
  obtain ⟨v,hv⟩ := hfour
  have hdiv : 32 ∣ x+y := by
    refine ⟨u*v,?_⟩
    calc
      x+y = 2^n*(2*(a-1)+6) := hs
      _ = (8*u)*(4*v) := by rw [hu,hv]
      _ = 32*(u*v) := by
        calc
          (8*u)*(4*v) = (8*4)*(u*v) := by ac_rfl
          _ = 32*(u*v) := by simp
  have h0 : (x+y)%32=0 := Nat.mod_eq_zero_of_dvd hdiv
  omega

private theorem cone_arith (a k x y n : Nat)
    (ha : 2 ≤ a) (he : a%2=0)
    (hx : x%64=5) (hy : y%64=43)
    (hs : x+y=2^n*(2*(a-1)+6))
    (hc : (2*k-a+3)+(2*(a-1)+6)+3*n=x+2*y) :
    k%2=1 ∧ (a+k)%4=1 ∧ 5 ≤ k := by
  have hn := depth_small a x y n ha he hx hy hs
  have hncase : n=0 ∨ n=1 ∨ n=2 := by omega
  rcases hncase with h|h|h <;> subst n <;>
    simp at hs hc <;> omega

private theorem no_pow_eight (x y n : Nat)
    (hx : x%64=5) (hy : y%64=43)
    (hs : x+y=2^n*8) : False := by
  by_cases h : n<3
  · have hn : n=0 ∨ n=1 ∨ n=2 := by omega
    rcases hn with hn|hn|hn <;> subst n <;> simp at hs <;> omega
  · have hn : 3≤n := by omega
    have hpow : 8 ∣ (2:Nat)^n := by
      change (2:Nat)^3 ∣ 2^n
      exact Nat.pow_dvd_pow 2 hn
    obtain ⟨u,hu⟩ := hpow
    have hdiv : 64 ∣ x+y := by
      refine ⟨u,?_⟩
      calc
        x+y = 2^n*8 := hs
        _ = (8*u)*8 := by rw [hu]
        _ = 64*u := by omega
    have h0 : (x+y)%64=0 := Nat.mod_eq_zero_of_dvd hdiv
    omega

private theorem no_pow_odd_sum (x y n c : Nat)
    (hx : x%64=5) (hy : y%64=43)
    (hs : x+y+1=2^n*(2*c)) : False := by
  have hd : 2∣x+y+1 := by
    refine ⟨2^n*c,?_⟩
    calc
      x+y+1=2^n*(2*c) := hs
      _=2*(2^n*c) := by ac_rfl
  have h0 : (x+y+1)%2=0 := Nat.mod_eq_zero_of_dvd hd
  omega

/-- In the exact original SectionAllInverse source grammar,
every parent of the new cone is an odd-right missing-image state. -/
theorem all_parent_residue (a k x y : Nat)
    (hx : x%64=5) (hy : y%64=43)
    (h : sectionPreimageAll a k x y) :
    k%2=1 ∧ (a+k)%4=1 ∧ 5≤k := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at h
        omega
      · simp only [sectionPreimageAll,if_pos ha0,if_neg hk0,if_neg hk1] at h
        obtain ⟨_,n,hs,_⟩ := h
        exact False.elim (no_pow_eight x y n hx hy hs)
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at h
        omega
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at h
          omega
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at h
            omega
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at h
              omega
            · simp only [sectionPreimageAll,if_neg ha0,if_pos ha1,
                if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at h
              rcases h with ⟨h3,_⟩ | ⟨_,n,hs,_⟩
              · omega
              · have hh : x+y+1=2^n*(2*8) := by simpa using hs
                exact False.elim (no_pow_odd_sum x y n 8 hx hy hh)
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at h
        omega
      · by_cases hlow : 2*k≤a
        · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,if_neg hk0,if_pos hlow] at h
          obtain ⟨_,hy2⟩ := h
          omega
        · by_cases heven : a%2=0
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hlow,if_pos heven] at h
            obtain ⟨_,n,hs,hc⟩ := h
            exact cone_arith a k x y n ha2 heven hx hy hs hc
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hlow,if_neg heven] at h
            rcases h with ⟨h3,_⟩ | ⟨_,n,hs,_⟩
            · omega
            · have hh : x+y+1=2^n*(2*((a-1)+4)) := by
                simpa only [show 2*(a-1)+8=2*((a-1)+4) by omega] using hs
              exact False.elim (no_pow_odd_sum x y n ((a-1)+4) hx hy hh)

#print axioms all_parent_residue
end BB6.Agent34Cone
