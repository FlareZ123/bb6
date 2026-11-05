import Core192High
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace Agent41M192

def lowCore (x w : Nat) : Prop :=
  (x=9 ∧ w=67) ∨
  (x=10 ∧ w%96=59) ∨
  (x=106 ∧ w%96=11) ∨
  (x=34 ∧ w%96=47) ∨
  (x=130 ∧ w%96=95) ∨
  (x=36 ∧ (w%96=48 ∨ w%96=50)) ∨
  (x=132 ∧ (w%96=0 ∨ w%96=2)) ∨
  (x=58 ∧ w%96=35) ∨
  (x=154 ∧ w%96=83) ∨
  (x=82 ∧ w%96=23) ∨
  (x=178 ∧ w%96=71) ∨
  (x=84 ∧ w%96=24) ∨
  (x=180 ∧ w%96=72)

def low (a k c : Nat) : Prop :=
  c≠2 ∧
  let shift := if c<4 then 0 else c-3
  let x := (a+192-shift)%192
  let w := (k+c)%192
  lowCore x w ∧ (8≤k ∨ (x=106 ∧ w=11 ∧ 4≤c))

def bad (a k c : Nat) : Prop :=
  if c<8 then low a k c else high a k c

theorem bad_root_absent : ¬bad 5 0 1 := by
  simp [bad, low, lowCore]

theorem bad_target (a k : Nat) (ha:a%192=9) (hk:k%192=67) : bad a k 0 := by
  have hk8 : 8≤k := by omega
  simp only [bad, show (0:Nat)<8 by omega, ↓reduceIte,low]
  refine ⟨by omega, ?_⟩
  dsimp
  have hx : (a+192)%192=9 := by omega
  have hw : k%192=67 := by omega
  rw [hx,hw]
  exact ⟨Or.inl ⟨rfl,rfl⟩, Or.inl hk8⟩

private theorem lowCore_ne_8 (x:Nat) : ¬ lowCore x 8 := by
  simp [lowCore]

private theorem lowCore_ne_9 (x:Nat) : ¬ lowCore x 9 := by
  simp [lowCore]

theorem low_step1 (a k:Nat) (h:low a (k+1) 0) : low a k 1 := by
  dsimp [low] at h ⊢
  rcases h with ⟨_,hc,hb⟩
  have hk : 8≤k := by
    rcases hb with hb | hb
    · by_cases hk : 8≤k
      · exact hk
      · have he : k=7 := by omega
        subst k
        exact False.elim ((lowCore_ne_8 _) (by simpa using hc))
    · omega
  exact ⟨by decide, hc, Or.inl hk⟩

private theorem lowCore_ne_10 (x:Nat) : ¬ lowCore x 10 := by
  simp [lowCore]

theorem low_step3 (a k:Nat) (h:low a (k+2) 1) : low a k 3 := by
  dsimp [low] at h ⊢
  rcases h with ⟨_,hc,hb⟩
  have hk : 8≤k := by
    rcases hb with hb | hb
    · by_cases hk : 8≤k
      · exact hk
      · have he : k=6 ∨ k=7 := by omega
        rcases he with he|he
        · subst k
          exact False.elim ((lowCore_ne_9 _) (by simpa using hc))
        · subst k
          exact False.elim ((lowCore_ne_10 _) (by simpa using hc))
    · omega
  exact ⟨by decide, hc, Or.inl hk⟩

private theorem lowCore_11_to_14 (x w:Nat)
    (hlo:11≤w) (hhi:w≤14) (h:lowCore x w) : x=106 ∧ w=11 := by
  unfold lowCore at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h <;> omega

theorem low_step_mid (a k c:Nat) (ha:0<a) (hc:4≤c) (hce:c≤7)
    (h:low (a-1) (k+1) (c-1)) : low a k c := by
  dsimp [low] at h ⊢
  have hs : (if c-1<4 then 0 else c-1-3)=c-4 := by
    by_cases hh : c-1<4
    · simp only [if_pos hh]; omega
    · simp only [if_neg hh]; omega
  have ht : (if c<4 then 0 else c-3)=c-3 := by
    simp [show ¬c<4 by omega]
  rw [hs] at h
  rw [ht]
  have hx : ((a-1)+192-(c-4))%192=(a+192-(c-3))%192 := by omega
  have hw : ((k+1)+(c-1))%192=(k+c)%192 := by omega
  rw [hx,hw] at h
  rcases h with ⟨_,hcore,hb⟩
  constructor
  · omega
  constructor
  · exact hcore
  rcases hb with hb|hb
  · by_cases hk:8≤k
    · exact Or.inl hk
    · have hk7:k=7 := by omega
      subst k
      have hwsmall : 11 ≤ (7+c)%192 ∧ (7+c)%192 ≤ 14 := by omega
      have hh := lowCore_11_to_14 _ _ hwsmall.1 hwsmall.2 hcore
      exact Or.inr ⟨hh.1,hh.2,hc⟩
  · exact Or.inr ⟨hb.1,hb.2.1,by omega⟩

theorem low7_to_high8 (a k:Nat) (ha:0<a) (h:low (a-1) (k+1) 7) : high a k 8 := by
  dsimp [low] at h
  have hcore := h.2.1
  unfold lowCore at hcore
  dsimp [high]
  rcases hcore with h|h|h|h|h|h|h|h|h|h|h|h|h
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))))))))
  · exact (Or.inr (Or.inl (by omega)))
  · exact (Or.inr (Or.inl (by omega)))
  · exact (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))))))))

#print axioms low7_to_high8
#print axioms low_step_mid
#print axioms lowCore_11_to_14
#print axioms low_step3
#print axioms low_step1
#print axioms bad_root_absent
#print axioms bad_target
end Agent41M192
