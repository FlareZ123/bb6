import Std
namespace BB6.Agent1

def G (k c : Nat) : Nat × Nat :=
  if h : c < 2*k then G (k-(c/2+1)) (2*c+3)
  else if c ≤ 2*k+1 then (0,2*c+3)
  else (4*k+4,c-(2*k+2))
termination_by k
decreasing_by omega

def T (a c : Nat) : Option (Nat × Nat) :=
  if c=0 then some (2,a+1)
  else if c=1 then some (a+2,0)
  else if a%2=0 then some (a+3,c-2)
  else if c=2 then none
  else if c=3 then some (G (a/2) 1)
  else some (G (a/2+1) (c-2))

inductive Reach : Nat → Nat → Prop where
  | init : Reach 2 1
  | next (a c b d : Nat) : Reach a c → T a c = some (b,d) → Reach b d

theorem G_second_odd (k c : Nat) (hc:c%2=1) : (G k c).2%2=1 := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
    by_cases h1 : c < 2*k
    · rw [G]
      simp only [h1,dite_true]
      apply ih _ (by omega) _
      omega
    · by_cases h2 : c ≤ 2*k+1
      · rw [G]
        simp [h1,h2]
      · rw [G]
        simp [h1,h2]
        omega

theorem G_first_even (k c : Nat) : (G k c).1%2=0 := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
    by_cases h1 : c < 2*k
    · rw [G]
      simp only [h1,dite_true]
      exact ih _ (by omega) _
    · by_cases h2 : c ≤ 2*k+1
      · rw [G]
        simp [h1,h2]
      · rw [G]
        simp [h1,h2]
        omega

theorem G_even_output (k v b d : Nat)
    (h:G k v=(b,d)) (hd:d%2=0) :
    b=4*k+4 ∧ 2*k+2 ≤ v ∧ d=v-(2*k+2) := by
  by_cases hlow:v<2*k
  · have ho:=G_second_odd (k-(v/2+1)) (2*v+3) (by omega)
    rw [G] at h
    simp only [hlow,dite_true] at h
    have hh : (G (k-(v/2+1)) (2*v+3)).2=d := congrArg Prod.snd h
    rw [hh] at ho
    omega
  · by_cases hmid:v≤2*k+1
    · rw [G] at h
      simp only [hlow,dite_false,hmid,ite_true] at h
      have hh : d=2*v+3 := (Prod.mk.inj h).2.symm
      omega
    · rw [G] at h
      simp only [hlow,dite_false,hmid,ite_false] at h
      obtain ⟨hb,hd'⟩:=Prod.mk.inj h
      constructor
      · exact hb.symm
      constructor
      · omega
      · exact hd'.symm

/-- A nonreset even-left/positive-even-right hub came through a high G exit. -/
theorem even_target_parent (a c b d : Nat)
    (h:T a c=some (b,d)) (hb:b%2=0) (hdpos:0<d) (hdeven:d%2=0)
    (hnot:b≠2) :
    a%2=1 ∧ 4≤c ∧ b=2*a+6 ∧ d+a+5=c := by
  unfold T at h
  by_cases hz:c=0
  · simp [hz] at h
    omega
  · by_cases ho:c=1
    · simp [hz,ho] at h
      omega
    · by_cases he:a%2=0
      · simp [hz,ho,he] at h
        omega
      · by_cases ht:c=2
        · simp [hz,ho,he,ht] at h
        · by_cases hthree:c=3
          · simp [hz,ho,he,ht,hthree] at h
            have hh : (G (a/2) 1).2=d := congrArg Prod.snd h
            have hodd:=G_second_odd (a/2) 1 (by decide)
            rw [hh] at hodd
            omega
          · simp [hz,ho,he,ht,hthree] at h
            have ⟨hb',hbound,hd'⟩:=G_even_output (a/2+1) (c-2) b d h hdeven
            constructor
            · exact (by omega)
            constructor
            · omega
            constructor
            · omega
            · omega

/-- A positive-even-right hub with odd left has an even-left parent. -/
theorem odd_target_parent (b d : Nat)
    (hr:Reach b d) (hb:b%2=1) (hdpos:0<d) (hdeven:d%2=0) :
    ∃ a c, Reach a c ∧ a%2=0 ∧ b=a+3 ∧ c=d+2 := by
  cases hr with
  | init => omega
  | next a c _ _ hr h =>
      unfold T at h
      by_cases hz:c=0
      · simp [hz] at h
        omega
      · by_cases ho:c=1
        · simp [hz,ho] at h
          omega
        · by_cases he:a%2=0
          · simp [hz,ho,he] at h
            refine ⟨a,c,hr,he,?_,?_⟩
            · omega
            · omega
          · by_cases ht:c=2
            · simp [hz,ho,he,ht] at h
            · by_cases hthree:c=3
              · simp [hz,ho,he,ht,hthree] at h
                have hh : (G (a/2) 1).1=b := congrArg Prod.fst h
                have heven:=G_first_even (a/2) 1
                rw [hh] at heven
                omega
              · simp [hz,ho,he,ht,hthree] at h
                have hh : (G (a/2+1) (c-2)).1=b := congrArg Prod.fst h
                have heven:=G_first_even (a/2+1) (c-2)
                rw [hh] at heven
                omega

/-- A nonreset positive-even hub has an earlier smaller even hub. -/
theorem even_two_back (b d : Nat) (hr:Reach b d)
    (hb:b%2=0) (hdpos:0<d) (hdeven:d%2=0) (hnot:b≠2) :
    ∃ x y, Reach x y ∧ x%2=0 ∧ 0<y ∧ y%2=0 ∧ b=2*x+12 := by
  cases hr with
  | init => omega
  | next a c _ _ hr h =>
      obtain ⟨ha,hc,hb',hd'⟩:=even_target_parent a c b d h hb hdpos hdeven hnot
      obtain ⟨x,y,hrx,hxe,hax,hy⟩:=odd_target_parent a c hr ha (by omega) (by omega)
      refine ⟨x,y,hrx,hxe,by omega,by omega,?_⟩
      omega

/-- Exact global left-coordinate normal form at all reachable positive even-right hubs. -/
theorem even_left_power_shape (b d : Nat) (hr:Reach b d)
    (hb:b%2=0) (hdpos:0<d) (hdeven:d%2=0) :
    ∃ j : Nat, b+12=14*2^j := by
  induction b using Nat.strongRecOn generalizing d with
  | ind b ih =>
    by_cases h2:b=2
    · exact ⟨0,by omega⟩
    · obtain ⟨x,y,hrx,hxe,hypos,hyeven,hb'⟩:=even_two_back b d hr hb hdpos hdeven h2
      obtain ⟨j,hj⟩:=ih x (by omega) y hrx hxe hypos hyeven
      refine ⟨j+1,?_⟩
      rw [Nat.pow_succ]
      omega

#print axioms BB6.Agent1.even_left_power_shape
end BB6.Agent1
