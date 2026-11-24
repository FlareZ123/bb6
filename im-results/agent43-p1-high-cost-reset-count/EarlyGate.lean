import PosEvenForm
namespace BB6.Agent43Early
open BB6.Agent1

/-- Structural recursion for kernel evaluation of the unchanged source map. -/
def gFuel : Nat → Nat → Nat → Nat × Nat
  | 0, _, _ => (0,0)
  | f+1,k,c =>
    if c < 2*k then gFuel f (k-(c/2+1)) (2*c+3)
    else if c ≤ 2*k+1 then (0,2*c+3)
    else (4*k+4,c-(2*k+2))

theorem gFuel_eq (f k c : Nat) (h : k<f) : gFuel f k c = G k c := by
  induction f generalizing k c with
  | zero => omega
  | succ f ih =>
    rw [gFuel,G]
    by_cases hl : c<2*k
    · simp only [hl,ite_true,dite_true]
      exact ih _ _ (by omega)
    · simp [hl]

def fastG (k c : Nat) := gFuel (k+1) k c
theorem fastG_eq (k c : Nat) : fastG k c = G k c := gFuel_eq _ _ _ (by omega)

def fastT (a c : Nat) : Option (Nat × Nat) :=
  if c=0 then some (2,a+1)
  else if c=1 then some (a+2,0)
  else if a%2=0 then some (a+3,c-2)
  else if c=2 then none
  else if c=3 then some (fastG (a/2) 1)
  else some (fastG (a/2+1) (c-2))

theorem fastT_eq (a c : Nat) : fastT a c = T a c := by simp [fastT,T,fastG_eq]

/-- Rank lemma of Agent1's Packet, in the exact PosEvenForm source namespace. -/
private theorem g_mass (k c : Nat) : 2*k+c+2 ≤ (G k c).1+(G k c).2 := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
    by_cases h1 : c < 2*k
    · have hr : k - (c/2+1) < k := by omega
      have hrec := ih _ hr (2*c+3)
      rw [G]
      simp only [h1, dite_true]
      omega
    · by_cases h2 : c ≤ 2*k+1
      · rw [G]; simp [h1,h2]; omega
      · rw [G]; simp [h1,h2]; omega

private theorem g_mass_one (k : Nat) : 2*k+5 ≤ (G k 1).1+(G k 1).2 := by
  by_cases hk:k=0
  · subst k; simp [G]
  · have hlow : 1 < 2*k := by omega
    have hr := g_mass (k-1) 5
    rw [G]
    simp only [hlow, dite_true, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd]
    omega

theorem fast_mass (a c b d : Nat) (h : fastT a c = some (b,d)) : a+c<b+d := by
  rw [fastT_eq] at h
  unfold T at h
  by_cases hc0 : c=0
  · simp [hc0] at h; omega
  · by_cases hc1 : c=1
    · simp [hc0,hc1] at h; omega
    · by_cases ha : a%2=0
      · simp [hc0,hc1,ha] at h; omega
      · by_cases hc2 : c=2
        · simp [hc0,hc1,ha,hc2] at h
        · by_cases hc3 : c=3
          · simp [hc0,hc1,ha,hc2,hc3] at h
            have hm := g_mass_one (a/2)
            have he := Prod.mk.inj h
            omega
          · simp [hc0,hc1,ha,hc2,hc3] at h
            have hm := g_mass (a/2+1) (c-2)
            have he := Prod.mk.inj h
            omega

def run : Nat → Nat × Nat → Option (Nat × Nat)
  | 0,p => some p
  | n+1,p => (fastT p.1 p.2).bind (run n)

theorem run_add (m n : Nat) (p : Nat × Nat) : run (m+n) p = (run m p).bind (run n) := by
  induction m generalizing p with
  | zero => simp [run]
  | succ m ih =>
    rw [Nat.succ_add]
    simp only [run]
    cases h : fastT p.1 p.2 with
    | none => simp [h]
    | some q => simp [h,ih]

theorem reach_run {a c : Nat} (h : Reach a c) : ∃ n, run n (2,1)=some (a,c) := by
  induction h with
  | init => exact ⟨0,rfl⟩
  | next a c b d hr ht ih =>
    obtain ⟨n,hn⟩ := ih
    refine ⟨n+1,?_⟩
    rw [run_add,hn]
    simp [run,fastT_eq,ht]

theorem run_mass (n : Nat) (p q : Nat × Nat) (h : run n p=some q) : p.1+p.2≤q.1+q.2 := by
  induction n generalizing p with
  | zero => simp [run] at h; subst q; omega
  | succ n ih =>
    cases he : fastT p.1 p.2 with
    | none => simp [run,he] at h
    | some r =>
      have hr : run n r=some q := by simpa [run,he] using h
      have h1 := ih r hr
      obtain ⟨a,c⟩ := r
      have h2 := fast_mass p.1 p.2 a c he
      simp at h1
      omega

def forbidden (p : Nat × Nat) : Bool := (p.1==2) && ([4,16,42,96,206,428,874,1768,3558,7140,14306,28640,57310].contains p.2)

/-- Check all states up to mass B, terminating at B or a source halt. -/
def scan (B : Nat) : Nat → Nat × Nat → Bool
  | 0,p => decide (B<p.1+p.2)
  | fuel+1,p =>
    if B<p.1+p.2 then true
    else if forbidden p then false
    else match fastT p.1 p.2 with
      | none => true
      | some r => scan B fuel r

theorem scan_sound (B fuel : Nat) (p : Nat × Nat) (hs : scan B fuel p=true)
    (n : Nat) (q : Nat × Nat) (hr : run n p=some q) (hb : q.1+q.2≤B) : forbidden q=false := by
  have hm := run_mass n p q hr
  have hp : ¬ B<p.1+p.2 := by omega
  induction fuel generalizing p n with
  | zero => simp [scan,hp] at hs
  | succ fuel ih =>
    simp only [scan,hp,ite_false] at hs
    split at hs
    · contradiction
    · rename_i hf
      cases n with
      | zero =>
        simp [run] at hr
        subst q
        simpa using hf
      | succ n =>
        cases he : fastT p.1 p.2 with
        | none => simp [run,he] at hr
        | some r =>
          have hr' : run n r=some q := by simpa [run,he] using hr
          exact ih r (by simpa [he] using hs) n hr' (run_mass n r q hr') (by have := run_mass n r q hr'; omega)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem small_scan : scan 57312 57313 (2,1)=true := by decide +kernel

theorem small_numeric (n : Nat) (hn : n≤12) :
    2+(14*2^n-2*n-10)≤57312 ∧ forbidden (2,14*2^n-2*n-10)=true := by
  have h : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 ∨ n=7 ∨ n=8 ∨ n=9 ∨ n=10 ∨ n=11 ∨ n=12 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem no_small_gate (n : Nat) (hn : n≤12) : ¬ Reach 2 (14*2^n-2*n-10) := by
  intro h
  obtain ⟨k,hk⟩ := reach_run h
  obtain ⟨hb,hf⟩ := small_numeric n hn
  have hs := scan_sound 57312 57313 (2,1) small_scan k _ hk hb
  rw [hf] at hs
  contradiction

private theorem pow_linear (k : Nat) : 2*k+12≤14*2^k := by
  induction k with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ]; omega

theorem odd_gate_arithmetic (n : Nat) (hn : 3≤n) (ho : n%2=1) :
    let d:=14*2^n-2*n-10
    12≤d ∧ d%4=0 ∧ ∀ j : Nat, d+8≠14*2^j := by
  dsimp only
  have h0 : 2*n+10≤14*2^n := by have := pow_linear n; omega
  have hn1 : n=n-1+1 := by omega
  have hn2 : n=n-2+2 := by omega
  have hpow1 : 2^n=2*2^(n-1) := by
    calc
      2^n = 2^(n-1+1) := congrArg (fun k : Nat => 2^k) hn1
      _ = 2*2^(n-1) := by rw [Nat.pow_succ]; omega
  have hpow2 : 2^n=4*2^(n-2) := by
    calc
      2^n = 2^(n-2+2) := congrArg (fun k : Nat => 2^k) hn2
      _ = 4*2^(n-2) := by rw [Nat.pow_add]; simp; omega
  have hlin := pow_linear (n-1)
  have hlo : 14*2^(n-1)<(14*2^n-2*n-10)+8 := by rw [hpow1]; omega
  have hhi : (14*2^n-2*n-10)+8<14*2^n := by omega
  refine ⟨by rw [hpow1]; omega,by rw [hpow2]; omega,?_⟩
  intro j hj
  by_cases h : j<n
  · have hle := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (show j≤n-1 by omega)
    omega
  · have hle := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (show n≤j by omega)
    omega

#print axioms no_small_gate
#print axioms odd_gate_arithmetic
end BB6.Agent43Early
