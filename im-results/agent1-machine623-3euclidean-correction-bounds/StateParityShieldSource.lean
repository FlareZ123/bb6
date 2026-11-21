import BusyBeaver.BB6.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

/-!
# Raw-state parity shield for BB(6) machine #623

This imports the unmodified DeepMind Cryptids machine file. All statements below
refer directly to its State, start, and next definitions; no transition rules are
copied. The source acceleration itself is Lean-certified upstream.
-/ 

namespace BB6.Agent1StateParitySource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

def Inv : State → Prop
  | .D0 a b d => a % 2 = 0 ∧ b % 2 = 0 ∧ 0 < d
  | .D1 a b d => (a + b) % 2 = 1
  | .H a b m => a % 2 = 1 ∧ b % 2 = 1
  | .B a k b d => (a + k + b) % 2 = 0
  | .A_pos a k q m => (a + k + q) % 2 = 1
  | .A_zero a q m => (a + q) % 2 = 1

theorem start_inv : Inv start := by
  simp [start, Inv]

theorem next_preserves_inv :
    ∀ {s s' : State}, Inv s → next s = some s' → Inv s' := by
  intro s s' hs hstep
  cases s with
  | D0 a b d =>
      rcases hs with ⟨ha, hb, hd⟩
      cases d with
      | zero => omega
      | succ d =>
          cases d with
          | zero =>
              cases b with
              | zero =>
                  cases a with
                  | zero =>
                      simp [next, Inv] at hstep ⊢
                      omega
                  | succ a =>
                      simp [next, Inv] at hstep ⊢
                      omega
              | succ b =>
                  simp [next, Inv] at hstep ⊢
                  omega
          | succ d =>
              cases d with
              | zero =>
                  cases a with
                  | zero =>
                      simp [next, Inv] at hstep ⊢
                      omega
                  | succ a =>
                      simp [next, Inv] at hstep ⊢
                      omega
              | succ d =>
                  simp [next, Inv] at hstep ⊢
                  omega
  | D1 a b d =>
      rcases hs with hpar
      cases a with
      | zero =>
          cases b with
          | zero => omega
          | succ b =>
              simp [next, Inv] at hstep ⊢
              omega
      | succ a =>
          simp [next, Inv] at hstep ⊢
          omega
  | H a b m =>
      rcases hs with ⟨ha, hb⟩
      cases a with
      | zero => omega
      | succ a =>
          cases a with
          | zero =>
              cases m with
              | zero =>
                  simp [next, Inv] at hstep ⊢
                  omega
              | succ m =>
                  cases m with
                  | zero =>
                      simp [next, Inv] at hstep ⊢
                      omega
                  | succ m =>
                      cases m with
                      | zero =>
                          simp [next, Inv] at hstep ⊢
                          omega
                      | succ m =>
                          simp [next, Inv] at hstep ⊢
                          omega
          | succ a =>
              cases m with
              | zero =>
                  simp [next, Inv] at hstep ⊢
                  omega
              | succ m =>
                  cases m with
                  | zero =>
                      simp [next, Inv] at hstep ⊢
                      omega
                  | succ m =>
                      simp [next, Inv] at hstep ⊢
                      omega
  | B a k b d =>
      rcases hs with hpar
      cases b with
      | zero =>
          cases k with
          | zero =>
              cases a with
              | zero =>
                  simp [next, Inv] at hstep ⊢
                  omega
              | succ a =>
                  cases a with
                  | zero => omega
                  | succ a =>
                      cases a with
                      | zero =>
                          cases d with
                          | zero =>
                              simp [next, Inv] at hstep ⊢
                              omega
                          | succ d =>
                              simp [next, Inv] at hstep ⊢
                              omega
                      | succ a =>
                          simp [next, Inv] at hstep ⊢
                          omega
          | succ k =>
              simp [next, Inv] at hstep ⊢
              omega
      | succ b =>
          simp [next, Inv] at hstep ⊢
          omega
  | A_pos a k q m =>
      rcases hs with hpar
      cases k with
      | zero =>
          cases a with
          | zero =>
              simp [next] at hstep
          | succ a =>
              simp [next, Inv] at hstep ⊢
              omega
      | succ k =>
          cases k with
          | zero =>
              cases a with
              | zero =>
                  simp [next, Inv] at hstep ⊢
                  omega
              | succ a =>
                  simp [next, Inv] at hstep ⊢
                  omega
          | succ k =>
              cases k with
              | zero =>
                  simp [next, Inv] at hstep ⊢
                  omega
              | succ k =>
                  simp [next, Inv] at hstep ⊢
                  omega
  | A_zero a q m =>
      simp [next, Inv] at hstep ⊢
      omega

theorem run_inv : ∀ n s, (Nat.rec (some start) (fun _ prev => prev.bind next) n = some s) → Inv s := by
  intro n
  induction n with
  | zero =>
      intro s h
      simp at h
      cases h
      exact start_inv
  | succ n ih =>
      intro s h
      simp only [Nat.rec] at h
      cases hr : Nat.rec (some start) (fun _ prev => prev.bind next) n with
      | none => simp [hr] at h
      | some t =>
          simp [hr] at h
          exact next_preserves_inv (ih t hr) h

theorem every_reachable_H_has_odd_a (n a b m : Nat)
    (h : Nat.rec (some start) (fun _ prev => prev.bind next) n = some (.H a b m)) :
    a % 2 = 1 := by
  have hp := run_inv n (.H a b m) h
  exact hp.1

theorem every_reachable_B_avoids_a1 (n d : Nat)
    (h : Nat.rec (some start) (fun _ prev => prev.bind next) n = some (.B 1 0 0 d)) : False := by
  have hp := run_inv n (.B 1 0 0 d) h
  norm_num [Inv] at hp

#print axioms start_inv
#print axioms next_preserves_inv
#print axioms every_reachable_H_has_odd_a
#print axioms every_reachable_B_avoids_a1

end BB6.Agent1StateParitySource
