import SourceGate

namespace Agent4Synthetic
open Agent9SourceSRun Agent9SProjection
open BusyBeaver.M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB

def adversarialIndex : Nat → Nat
  | 0 => 0
  | n+1 => 9*adversarialIndex n+2

def syntheticInput (c : Nat) : Nat := 3*adversarialIndex (c+5)+4

theorem adversarial_power (n : Nat) :
    4*adversarialIndex n+1 = 9^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change 4*(9*adversarialIndex n+2)+1 = 9^(n+1)
      rw [Nat.pow_succ]
      omega

theorem input_ge16 (c : Nat) : 16 ≤ syntheticInput c := by
  unfold syntheticInput
  have h : 20 ≤ adversarialIndex (c+5) := by
    have he : c+5 = (c+3)+2 := by omega
    rw [he]
    change 20 ≤ 9*(9*adversarialIndex (c+3)+2)+2
    omega
  omega

theorem input_residue (c : Nat) : syntheticInput c % 3 = 1 := by
  unfold syntheticInput; omega

theorem synthetic_one (c : Nat) :
    Sstep (syntheticInput c) c = some (9^(c+5),c+4) := by
  have h := adversarial_power (c+5)
  have hr := input_residue c
  have hd : syntheticInput c / 3 = adversarialIndex (c+5)+1 := by
    unfold syntheticInput; omega
  simp [Sstep, hr, hd]
  omega

theorem scalarRun_add (n m : Nat) (s : Option (Nat × Nat)) :
    scalarRun (n+m) s = scalarRun m (scalarRun n s) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change (scalarRun (n+m) s).bind (fun z => Sstep z.1 z.2)
        = (scalarRun m (scalarRun n s)).bind (fun z => Sstep z.1 z.2)
      rw [ih]

theorem zero_step (x c : Nat) :
    Sstep (3*x) (c+1) = some (4*x,c) := by
  simp [Sstep]

theorem zero_prefix (k n h u : Nat) (hk : k ≤ n) :
    scalarRun k (some (3^n*u,h+k)) =
       some (4^k*3^(n-k)*u,h) := by
  induction k generalizing n u h with
  | zero =>
      simp [scalarRun]
  | succ k ih =>
      have hl : k ≤ n-1 := by omega
      have hn : n = n-1+1 := by omega
      have hfact : 3^n*u = 3*(3^(n-1)*u) := by
        calc
          3^n*u = 3^(n-1+1)*u :=
            congrArg (fun v : Nat => 3^v*u) hn
          _ = 3*(3^(n-1)*u) := by
             rw [Nat.pow_succ]
             ac_rfl
      have hout : Sstep (3^n*u) (h+(k+1)) =
          some (4*(3^(n-1)*u),h+k) := by
        rw [hfact]
        simpa [Nat.add_assoc] using zero_step (3^(n-1)*u) (h+k)
      have hrun := ih (n-1) h (4*u) hl
      have hres : 4^k*3^((n-1)-k)*(4*u) =
          4^(k+1)*3^(n-(k+1))*u := by
        rw [Nat.pow_succ]
        have he : (n-1)-k = n-(k+1) := by omega
        rw [he]
        ac_rfl
      have harg : h+(k+1) = h+k+1 := by omega
      have hnum : 4*(3^(n-1)*u) = 3^(n-1)*(4*u) := by ac_rfl
      calc
        scalarRun (k+1) (some (3^n*u,h+(k+1))) =
           scalarRun k (scalarRun 1 (some (3^n*u,h+(k+1)))) := by
             rw [show k+1=1+k by omega, scalarRun_add]
        _ = scalarRun k (some (3^(n-1)*(4*u),h+k)) := by
             simp [scalarRun, hout, hnum]
        _ = some (4^(k+1)*3^(n-(k+1))*u,h) := by
             rw [hrun, hres]

theorem power9 (n : Nat) : 9^n = 3^(2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.pow_succ, ih]
      have h : 2*(n+1) = 2*n+2 := by omega
      rw [h, Nat.pow_add]

theorem synthetic_live_before_transfer (c : Nat) :
    scalarRun (c+5) (some (syntheticInput c,c)) =
        some (4^(c+4)*3^(c+6),0) := by
  have h := zero_prefix (c+4) (2*(c+5)) 0 1 (by omega)
  have hn : (2*(c+5)-(c+4))=c+6 := by omega
  have hpow := power9 (c+5)
  have hp : (c+5)=1+(c+4) := by omega
  rw [hp,scalarRun_add]
  change scalarRun (c+4) (Sstep (syntheticInput c) c) = _
  rw [synthetic_one,hpow] at *
  simpa [hn] using h

theorem synthetic_transfer (c : Nat) :
    scalarRun (c+6) (some (syntheticInput c,c)) = none := by
  have hlive := synthetic_live_before_transfer c
  have hmod : (4^(c+4)*3^(c+6))%3=0 := by
    have hd : 3^(c+6)=3*(3^(c+5)) := by
      rw [show c+6=c+5+1 by omega, Nat.pow_succ]
      ac_rfl
    rw [hd]
    simp [Nat.mul_mod]
  have htime : c+6 = (c+5)+1 := by omega
  rw [htime]
  change (scalarRun (c+5) (some (syntheticInput c,c))).bind
     (fun z => Sstep z.1 z.2) = none
  rw [hlive]
  simp [Sstep, hmod]

theorem synthetic_source_halt (c : Nat) :
    sourceRun (c+7) (some (.S (syntheticInput c-16) c)) = none := by
  have hge := input_ge16 c
  have hb : syntheticInput c-16+16=syntheticInput c := by omega
  have hfactor : 3^(c+6) = 729*3^c := by
    have he : c+6=6+c := by omega
    rw [he, Nat.pow_add]
  have hdiv : (4^(c+4)*3^(c+6))%729=0 := by
    rw [hfactor]
    simp [Nat.mul_mod, Nat.mul_comm, Nat.mul_left_comm]
  have hmain := source_immediate_halt_after_transfer
    (c+5) (syntheticInput c-16) c (4^(c+4)*3^(c+6)) 0
  have hh := hmain (by simpa [hb] using synthetic_live_before_transfer c)
      (by simpa [hb] using synthetic_transfer c) hdiv
  simpa [show c+7=c+5+2 by omega] using hh

#print axioms synthetic_source_halt

theorem scalarRun_none (n : Nat) : scalarRun n none = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (scalarRun n none).bind (fun z => Sstep z.1 z.2) = none
      rw [ih]
      rfl

theorem scalar_prefix_live (n k : Nat) (x : Option (Nat × Nat))
    (hk : k ≤ n) (v : Nat × Nat)
    (hn : scalarRun n x = some v) :
    ∃ v', scalarRun k x = some v' := by
  have he : n=k+(n-k) := by omega
  rw [he, scalarRun_add] at hn
  cases hs : scalarRun k x with
  | none =>
      simp [hs,scalarRun_none] at hn
  | some state => exact ⟨state,rfl⟩

theorem synthetic_first_halt (c : Nat) :
    sourceRun (c+7) (some (.S (syntheticInput c-16) c)) = none ∧
    ∀ j, j<c+7 →
      ∃ st, sourceRun j (some (.S (syntheticInput c-16) c)) =
         some st := by
  constructor
  · exact synthetic_source_halt c
  · intro j hj
    have hb : syntheticInput c-16+16=syntheticInput c := by
      have hg := input_ge16 c
      omega
    by_cases heq : j ≤ c+5
    · have ⟨v,hv⟩ := scalar_prefix_live
          (c+5) j (some (syntheticInput c,c)) heq
          (4^(c+4)*3^(c+6),0) (synthetic_live_before_transfer c)
      rcases v with ⟨q,d⟩
      have htrans : scalarRun j
          (some (syntheticInput c-16+16,c)) = some (q,d) := by
        simpa [hb] using hv
      obtain ⟨b',_,hs⟩ := live_source_steps
        j (syntheticInput c-16) c q d htrans
      exact ⟨.S b' d, hs⟩
    · have hj : j=c+6 := by omega
      subst j
      have hl : scalarRun (c+5)
          (some (syntheticInput c-16+16,c)) =
          some (4^(c+4)*3^(c+6),0) := by
        simpa [hb] using synthetic_live_before_transfer c
      have ht : scalarRun (c+6)
          (some (syntheticInput c-16+16,c)) = none := by
        simpa [hb] using synthetic_transfer c
      obtain ⟨b',m,_,_,hs⟩ := first_transfer_source
        (c+5) (syntheticInput c-16) c
        (4^(c+4)*3^(c+6)) 0 hl (by
           simpa [show c+6=(c+5)+1 by omega] using ht)
      exact ⟨.T m, hs⟩

#print axioms synthetic_first_halt

end Agent4Synthetic
