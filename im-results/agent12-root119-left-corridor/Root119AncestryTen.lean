import Root119Ancestry
namespace BB6Root119
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Original-source ten-step inverse exclusion, with arbitrary signed exterior tape. -/
theorem no_ten_step_right1110
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 d : Conf)
    (h01: next a0 = some a1)
    (h12: next a1 = some a2)
    (h23: next a2 = some a3)
    (h34: next a3 = some a4)
    (h45: next a4 = some a5)
    (h56: next a5 = some a6)
    (h67: next a6 = some a7)
    (h78: next a7 = some a8)
    (h89: next a8 = some a9)
    (h9d : next a9 = some d)
    (hq : d.q = .B) (h0 : d.tape d.h = false)
    (hl2 : d.tape (d.h-2) = false)
    (hr1 : d.tape (d.h+1) = true)
    (hr2 : d.tape (d.h+2) = true)
    (hr3 : d.tape (d.h+3) = true)
    (hr4 : d.tape (d.h+4) = false) : False := by
  all_goals rcases a9 with ⟨q9,x9,t9⟩
  all_goals cases q9 <;> cases hb9 : t9 x9 <;> simp [next, hb9] at h9d
  all_goals cases h9d
  all_goals try simp (disch := omega) [setBit] at *
  all_goals try omega
  all_goals rcases a8 with ⟨q8,x8,t8⟩
  all_goals cases q8 <;> cases hb8 : t8 x8 <;> simp [next, hb8] at h89
  all_goals cases h89
  all_goals subst t9
  all_goals try simp (disch := omega) [setBit] at *
  all_goals try omega
  all_goals rcases a7 with ⟨q7,x7,t7⟩
  all_goals cases q7 <;> cases hb7 : t7 x7 <;> simp [next, hb7] at h78
  all_goals cases h78
  all_goals subst t8
  all_goals try simp (disch := omega) [setBit] at *
  all_goals try omega
  all_goals rcases a6 with ⟨q6,x6,t6⟩
  all_goals cases q6 <;> cases hb6 : t6 x6 <;> simp [next, hb6] at h67
  all_goals cases h67
  all_goals subst t7
  all_goals try simp (disch := omega) [setBit] at *
  all_goals try omega
  all_goals rcases a5 with ⟨q5,x5,t5⟩
  all_goals cases q5 <;> cases hb5 : t5 x5 <;> simp [next, hb5] at h56
  all_goals cases h56
  all_goals subst t6
  all_goals try simp (disch := omega) [setBit] at *
  all_goals try omega
  all_goals rcases a4 with ⟨q4,x4,t4⟩
  all_goals cases q4 <;> cases hb4 : t4 x4 <;> simp [next, hb4] at h45
  all_goals cases h45
  all_goals subst t5
  all_goals try simp (disch := omega) [setBit] at *
  all_goals try omega
  all_goals rcases a3 with ⟨q3,x3,t3⟩
  all_goals cases q3 <;> cases hb3 : t3 x3 <;> simp [next, hb3] at h34
  all_goals cases h34
  all_goals subst t4
  all_goals try simp (disch := omega) [setBit] at *
  all_goals try omega
  all_goals rcases a2 with ⟨q2,x2,t2⟩
  all_goals cases q2 <;> cases hb2 : t2 x2 <;> simp [next, hb2] at h23
  all_goals cases h23
  all_goals subst t3
  all_goals try simp (disch := omega) [setBit] at *
  all_goals try omega
  all_goals rcases a1 with ⟨q1,x1,t1⟩
  all_goals cases q1 <;> cases hb1 : t1 x1 <;> simp [next, hb1] at h12
  all_goals cases h12
  all_goals subst t2
  all_goals try simp (disch := omega) [setBit] at *
  all_goals try omega
  all_goals rcases a0 with ⟨q0,x0,t0⟩
  all_goals cases q0 <;> cases hb0 : t0 x0 <;> simp [next, hb0] at h01
  all_goals cases h01
  all_goals subst t1
  all_goals try simp (disch := omega) [setBit] at *
  all_goals try omega

/-- Restate the inverse exclusion for ten primitive instructions. -/
theorem no_ten_run_right1110 (u d : Conf)
    (hr : run 10 u = some d)
    (hq : d.q = .B) (h0 : d.tape d.h = false)
    (hl2 : d.tape (d.h-2) = false)
    (hr1 : d.tape (d.h+1) = true)
    (hr2 : d.tape (d.h+2) = true)
    (hr3 : d.tape (d.h+3) = true)
    (hr4 : d.tape (d.h+4) = false) : False := by
  cases h1 : next u with
  | none =>
    simp [run, h1] at hr
  | some a1 =>
    have he1 : run 9 a1 = some d := by simpa [run, h1] using hr
    cases h2 : next a1 with
    | none =>
      simp [run, h2] at he1
    | some a2 =>
      have he2 : run 8 a2 = some d := by simpa [run, h2] using he1
      cases h3 : next a2 with
      | none =>
        simp [run, h3] at he2
      | some a3 =>
        have he3 : run 7 a3 = some d := by simpa [run, h3] using he2
        cases h4 : next a3 with
        | none =>
          simp [run, h4] at he3
        | some a4 =>
          have he4 : run 6 a4 = some d := by simpa [run, h4] using he3
          cases h5 : next a4 with
          | none =>
            simp [run, h5] at he4
          | some a5 =>
            have he5 : run 5 a5 = some d := by simpa [run, h5] using he4
            cases h6 : next a5 with
            | none =>
              simp [run, h6] at he5
            | some a6 =>
              have he6 : run 4 a6 = some d := by simpa [run, h6] using he5
              cases h7 : next a6 with
              | none =>
                simp [run, h7] at he6
              | some a7 =>
                have he7 : run 3 a7 = some d := by simpa [run, h7] using he6
                cases h8 : next a7 with
                | none =>
                  simp [run, h8] at he7
                | some a8 =>
                  have he8 : run 2 a8 = some d := by simpa [run, h8] using he7
                  cases h9 : next a8 with
                  | none =>
                    simp [run, h9] at he8
                  | some a9 =>
                    have he9 : run 1 a9 = some d := by simpa [run, h9] using he8
                    cases h10 : next a9 with
                    | none =>
                      simp [run, h10] at he9
                    | some a10 =>
                      have he10 : a10 = d := by simpa [run, h10] using he9
                      subst a10
                      exact no_ten_step_right1110 u a1 a2 a3 a4 a5 a6 a7 a8 a9 d h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hq h0 hl2 hr1 hr2 hr3 hr4

/-- Reachability from the original blank tape has a finite primitive run witness. -/
theorem reach_has_run (d : Conf) (hd : Reach d) :
    ∃ n : Nat, run n blank = some d := by
  induction hd with
  | initial => exact ⟨0, rfl⟩
  | @follow u v hu huv ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n+1, ?_⟩
    rw [run_add, hn]
    simp [run, huv]

/-- Every authentic B/0 with a zero two cells left excludes right prefix 1110. -/
theorem reached_B0_exposed_no_right1110 (d : Conf) (hd : Reach d)
    (hq : d.q = .B) (h0 : d.tape d.h = false)
    (hl2 : d.tape (d.h-2) = false)
    (hr1 : d.tape (d.h+1) = true)
    (hr2 : d.tape (d.h+2) = true)
    (hr3 : d.tape (d.h+3) = true)
    (hr4 : d.tape (d.h+4) = false) : False := by
  obtain ⟨n, hn⟩ := reach_has_run d hd
  by_cases hnlt : n < 10
  · have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega
    rcases hcases with h | h | h | h | h | h | h | h | h | h
    all_goals subst n
    all_goals simp (disch := omega) [run, next, blank, setBit] at hn
    all_goals cases hn
    all_goals simp (disch := omega) [setBit] at hq h0 hl2 hr1 hr2 hr3 hr4
  · have heq : n = n-10+10 := by omega
    rw [heq, run_add] at hn
    cases hm : run (n-10) blank with
    | none => simp [hm] at hn
    | some a =>
      have h10 : run 10 a = some d := by simpa [hm] using hn
      exact no_ten_run_right1110 a d h10 hq h0 hl2 hr1 hr2 hr3 hr4

#print axioms BB6Root119.reached_B0_exposed_no_right1110

/-- Four consecutive right-hand ones in every reached left-10x B/0 section. -/
theorem reached_B0_left10x_right1111 (d : Conf) (hd : Reach d)
    (hq : d.q = .B) (h0 : d.tape d.h = false)
    (hl2 : d.tape (d.h-2) = false)
    (hl3 : d.tape (d.h-3) = true) :
    d.tape (d.h+1) = true ∧ d.tape (d.h+2) = true ∧
    d.tape (d.h+3) = true ∧ d.tape (d.h+4) = true := by
  obtain ⟨h1,h2,h3⟩ := reached_B0_left101_right11 d hd hq h0 hl2 hl3
  have h4 : d.tape (d.h+4) = true := by
    cases ht : d.tape (d.h+4) with
    | true => rfl
    | false =>
      exact False.elim (reached_B0_exposed_no_right1110 d hd hq h0 hl2 h1 h2 h3 ht)
  exact ⟨h1,h2,h3,h4⟩

#print axioms BB6Root119.reached_B0_left10x_right1111
end BB6Root119
