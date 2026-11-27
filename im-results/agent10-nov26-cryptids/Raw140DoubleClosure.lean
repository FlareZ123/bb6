import Raw140DoubleCore
namespace Raw140Double
open BB6BlockFAR Raw140Orbit Raw140Extra
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def orbitCfg (m n : Nat) (s : Tail) : Prim :=
  boundary 1 true (U 5 m) (word (trips n) ++ tailWord s)

theorem dIterTriple (k n : Nat) (V : List Bool) (s : Tail) :
    Reach base (boundary 3 false (U 6 k ++ [S 4]) (word V ++ word (trips n) ++ tailWord s))
      (boundary 3 false [S 4] (U 4 k ++ word V ++ word (trips (n+(turn k s).1)) ++ tailWord (turn k s).2)) := by
  have h := dIter k [S 4] (V ++ trips n) s
  simpa only [word_append,word_four,trips_add,List.append_assoc] using h

theorem reachRun {M : Table} {a b : Prim} {k : Nat} (h : run M k a = some b) : Reach M a b := ⟨k,h⟩

theorem core4 (p n : Nat) (s : Tail) (hp : 9 ≤ p) :
    ∃ r t, 2 ≤ r ∧ Reach base
      (boundary 3 false (U 5 (2*p)) (S 2::S 4::S 4::(word (trips (n+1)) ++ tailWord s)))
      (orbitCfg (4*p+14) r t) := by
  let c := (turn (2*p+2) s).1
  let t := (turn (2*p+2) s).2
  let r := n+1+c
  have hc : 3 ≤ c := turn_ge_three (2*p+2) s (by omega)
  have h₁ := convert1 (2*p) (S 4::S 4::(word (trips (n+1)) ++ tailWord s))
  have h₂ := cr4turn (U 6 (2*p+2) ++ [S 4]) (S 4::(word (trips (n+1)) ++ tailWord s))
  have h₃ := dIterTriple (2*p+2) (n+1) [true,false] s
  have h₄ := dEndE (2*p+1) (S 6::S 4::(word (trips r) ++ tailWord t))
  have h₅ := eIter p 1 1 (S 6::S 4::(word (trips r) ++ tailWord t))
  have h₆ := eOddLast (1+4*p) (trips r) t
  have h₇ : Reach base (E (1+4*p) 1 (S 6::S 4::(word (trips r) ++ tailWord t)))
      (boundary 3 false [] (U 4 (1+4*p+6) ++ word (trips (r+carry t)) ++ tailWord (rho t))) := by
    simpa only [trips_add,word_append,List.append_assoc] using h₆
  let z := r+carry t-1
  have hr : r+carry t = z+1 := by dsimp [z,r]; omega
  have hz : 2 ≤ z := by dsimp [z,r]; omega
  rw [hr] at h₇
  have h₈ : Reach base (E (1+4*p) 1 (S 6::S 4::(word (trips r) ++ tailWord t)))
      (E (1+4*p+6) 2 (word (trips z) ++ tailWord (rho t))) := h₇
  have h₉ := eEven 1 (1+4*p+6) (word (trips z) ++ tailWord (rho t))
  have h₁₀ : Reach base
      (boundary 3 false (U 5 (2*p)) (S 2::S 4::S 4::(word (trips (n+1)) ++ tailWord s)))
      (orbitCfg (4*p+14) z (rho t)) := by
    have hₐ := Reach.trans (reachRun h₁) (reachRun h₂)
    have h_b := Reach.trans hₐ h₃
    have h_c := Reach.trans h_b h₄
    have h_d := Reach.trans h_c h₅
    have h_e := Reach.trans (Reach.trans h_d h₈) h₉
    simpa only [orbitCfg, show 1+4*p+6+4*1+3 = 4*p+14 by omega] using h_e
  exact ⟨z,rho t,hz,h₁₀⟩

theorem core13 (p n : Nat) (s : Tail) (hp : 9 ≤ p) :
    ∃ r t, 2 ≤ r ∧ Reach base
      (boundary 3 false (U 5 (2*p+2)) (S 2::(word (trips (n+1)) ++ tailWord s)))
      (orbitCfg (4*p+16) r t) := by
  let c := (turn (2*p+4) (rho s)).1
  let t := (turn (2*p+4) (rho s)).2
  let r := n+carry s+c
  have hc : 3 ≤ c := turn_ge_three (2*p+4) (rho s) (by omega)
  have hr : 2 ≤ r := by dsimp [r]; omega
  let X := U 6 (2*p+4) ++ [S 4]
  have h₁ := convert1 (2*p+2) (word (trips (n+1)) ++ tailWord s)
  have h₂ := f13start X (S 4::(word (trips n) ++ tailWord s))
  have h₃ := bounce (false::false::trips n) s X
  have h₄ := stepL base 3 3 false (S 5) (S 4) 3 X
    (word (false::false::trips n) ++ word (trips (carry s)) ++ tailWord (rho s)) (by rfl)
  have h₅ : Reach base
      (boundary 3 false (U 5 (2*p+2)) (S 2::(word (trips (n+1)) ++ tailWord s)))
      (boundary 3 false X (word [false,false,false] ++ word (trips (n+carry s)) ++ tailWord (rho s))) := by
    have hₐ := Reach.trans (reachRun h₁) (reachRun h₂)
    have h_b := Reach.trans (Reach.trans hₐ h₃) (reachRun h₄)
    simpa only [trips_add,word_append,List.append_assoc,word,List.cons_append,List.nil_append,Bool.false_eq_true,ite_false] using h_b
  have h₆ := dIterTriple (2*p+4) (n+carry s) [false,false,false] (rho s)
  have h₇ : Reach base (boundary 3 false X (word [false,false,false] ++ word (trips (n+carry s)) ++ tailWord (rho s)))
      (boundary 3 false [S 4] (U 4 (2*p+7) ++ word (trips r) ++ tailWord t)) := by
    simpa only [X,r,c,t,U,word,List.replicate_succ,List.cons_append,List.nil_append,List.append_assoc,rep_cons,Bool.false_eq_true,ite_false] using h₆
  have h₈ := dEndE (2*p+6) (word (trips r) ++ tailWord t)
  have h₉ := eEven (p+3) 1 (word (trips r) ++ tailWord t)
  have h₁₀ : Reach base (E 1 (2*p+6) (word (trips r) ++ tailWord t)) (orbitCfg (4*p+16) r t) := by
    simpa only [orbitCfg,show 2*(p+3)=2*p+6 by omega,show 1+4*(p+3)+3=4*p+16 by omega] using h₉
  exact ⟨r,t,hr,Reach.trans (Reach.trans (Reach.trans h₅ h₇) h₈) h₁₀⟩

def Good (a : Prim) : Prop :=
  ∃ p n s, 9 ≤ p ∧ a = orbitCfg (2*p) (n+2) s

theorem progress4 (a : Prim) (ha : Good a) :
    ∃ k b, 0 < k ∧ Good b ∧ run M4 k a = some b := by
  obtain ⟨p,n,s,hp,rfl⟩ := ha
  have h₁ := reset4 (U 5 (2*p-1)) (word (trips (n+1)) ++ tailWord s)
  have hm : 2*p = (2*p-1)+1 := by omega
  have h₂ : run M4 7 (orbitCfg (2*p) (n+2) s) =
      some (boundary 3 false (U 5 (2*p)) (S 2::S 4::S 4::(word (trips (n+1)) ++ tailWord s))) := by
    rw [hm]
    exact h₁
  obtain ⟨r,t,hr,h₃⟩ := core4 p n s hp
  obtain ⟨k,hk⟩ := Reach.ext (M := M4) (fill_extends _ _) h₃
  refine ⟨7+k,orbitCfg (4*p+14) r t,by omega,?_,join h₂ hk⟩
  refine ⟨2*p+7,r-2,t,by omega,?_⟩
  rw [show 2*(2*p+7) = 4*p+14 by omega,show r-2+2=r by omega]

theorem progress13 (a : Prim) (ha : Good a) :
    ∃ k b, 0 < k ∧ Good b ∧ run M13 k a = some b := by
  obtain ⟨p,n,s,hp,rfl⟩ := ha
  have h₁ := reset13 (U 5 (2*p-1)) (S 4::S 4::(word (trips n) ++ tailWord s))
  have hm : 2*p = (2*p-1)+1 := by omega
  have h₂ : run M13 19 (orbitCfg (2*p) (n+2) s) =
      some (boundary 3 false (U 5 (2*p+2)) (S 2::(word (trips (n+1)) ++ tailWord s))) := by
    rw [hm]
    exact h₁
  obtain ⟨r,t,hr,h₃⟩ := core13 p n s hp
  obtain ⟨k,hk⟩ := Reach.ext (M := M13) (fill_extends _ _) h₃
  refine ⟨19+k,orbitCfg (4*p+16) r t,by omega,?_,join h₂ hk⟩
  refine ⟨2*p+8,r-2,t,by omega,?_⟩
  rw [show 2*(2*p+8) = 4*p+16 by omega,show r-2+2=r by omega]

theorem foreverGood (M : Table) (next : ∀ a, Good a → ∃ k b, 0 < k ∧ Good b ∧ run M k a = some b)
    (n : Nat) (a : Prim) (ha : Good a) : ∃ c, run M n a = some c := by
  induction n using Nat.strongRecOn generalizing a with
  | ind n ih =>
    obtain ⟨k,b,hk,hb,h⟩ := next a ha
    by_cases hle : k ≤ n
    · obtain ⟨c,hc⟩ := ih (n-k) (by omega) b hb
      exact ⟨c,by rw [show n=k+(n-k) by omega,run_add,h]; exact hc⟩
    · rw [show k=n+(k-n) by omega,run_add] at h
      cases he : run M n a with
      | none => simp [he] at h
      | some c => exact ⟨c,rfl⟩

theorem foreverEntry (M : Table) (next : ∀ a, Good a → ∃ k b, 0 < k ∧ Good b ∧ run M k a = some b)
    (t : Nat) (a : Prim) (ha : Good a) (h : run M t primBlank = some a) (n : Nat) :
    ∃ c, run M n primBlank = some c := by
  by_cases hle : t ≤ n
  · obtain ⟨c,hc⟩ := foreverGood M next (n-t) a ha
    exact ⟨c,by rw [show n=t+(n-t) by omega,run_add,h]; exact hc⟩
  · rw [show t=n+(t-n) by omega,run_add] at h
    cases he : run M n primBlank with
    | none => simp [he] at h
    | some c => exact ⟨c,rfl⟩

#print axioms progress4
#print axioms progress13
#print axioms foreverEntry
end Raw140Double
