import DyadicPopulation

namespace BB6.Agent21Dyadic
namespace FiniteTree

variable {α : Type}

def count (f : α→Bool→α) (v : α→Nat) : Nat→α→Nat
  | 0,s => v s
  | n+1,s => count f v n (f s false)+count f v n (f s true)

theorem count_const (f : α→Bool→α) (c n : Nat) (s : α) :
    count f (fun _=>c) n s=2^n*c := by
  induction n generalizing s with
  | zero => simp [count]
  | succ n ih => rw [count,ih,ih,Nat.pow_succ]; rw [Nat.mul_right_comm, Nat.mul_two]

theorem count_le (f : α→Bool→α) (v w : α→Nat) (h : ∀ s, v s≤w s) (n : Nat) (s : α) :
    count f v n s≤count f w n s := by
  induction n generalizing s with
  | zero => exact h s
  | succ n ih => simp only [count]; exact Nat.add_le_add (ih _) (ih _)

theorem count_mul (f : α→Bool→α) (v : α→Nat) (c n : Nat) (s : α) :
    count f (fun s=>c*v s) n s=c*count f v n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [count,ih,Nat.mul_add]

theorem count_add (f : α→Bool→α) (v w : α→Nat) (n : Nat) (s : α) :
    count f (fun s=>v s+w s) n s=count f v n s+count f w n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [count,ih]; omega

theorem count_comp (f : α→Bool→α) (v : α→Nat) (n m : Nat) (s : α) :
    count f v (n+m) s=count f (fun s=>count f v m s) n s := by
  induction n generalizing s with
  | zero => simp [count]
  | succ n ih => rw [show n+1+m=n+m+1 by omega]; simp only [count,ih]

theorem supercount (f : α→Bool→α) (v : α→Nat)
    (h : ∀ s, v (f s false)+v (f s true)≤2*v s) (n : Nat) (s : α) :
    count f v n s≤2^n*v s := by
  induction n generalizing s with
  | zero => simp [count]
  | succ n ih =>
    rw [count,Nat.pow_succ,Nat.mul_assoc]
    have h1 := ih (f s false)
    have h2 := ih (f s true)
    have hm := Nat.mul_le_mul_left (2^n) (h s)
    rw [Nat.mul_add] at hm
    omega

def stop (f : α→Bool→α) (v : α→Nat) (B : Nat) (s : α) (e : Bool) : α :=
  if v s=0 ∨ B≤v s then s else f s e

def live (v : α→Nat) (s : α) : Nat := if 0<v s then 1 else 0

def high (v : α→Nat) (B : Nat) (s : α) : Nat := if B≤v s then 1 else 0

def mid (v : α→Nat) (B : Nat) (s : α) : Nat := if 0<v s ∧ v s<B then 1 else 0

theorem stop_super (f : α→Bool→α) (v : α→Nat) (B : Nat)
    (h : ∀ s, v (f s false)+v (f s true)≤2*v s) (s : α) :
    v (stop f v B s false)+v (stop f v B s true)≤2*v s := by
  by_cases hs : v s=0 ∨ B≤v s
  · simp [stop,hs]; omega
  · simpa [stop,hs] using h s

theorem high_count_bound (f : α→Bool→α) (v : α→Nat) (B n : Nat)
    (h : ∀ s, v (f s false)+v (f s true)≤2*v s) (s : α) :
    B*count (stop f v B) (high v B) n s≤2^n*v s := by
  have hp (s : α) : B*high v B s≤v s := by
    unfold high
    split <;> simp_all
  have h1 := count_le (stop f v B) (fun s=>B*high v B s) v hp n s
  rw [count_mul] at h1
  exact Nat.le_trans h1 (supercount _ _ (stop_super f v B h) n s)

theorem zero_step (f : α→Bool→α) (v : α→Nat)
    (h : ∀ s, v (f s false)+v (f s true)≤2*v s) (s : α) (e : Bool) (hs : v s=0) :
    v (f s e)=0 := by
  have hh := h s
  cases e <;> omega

theorem zero_run (f : α→Bool→α) (v : α→Nat)
    (h : ∀ s, v (f s false)+v (f s true)≤2*v s) (s : α) (bits : List Bool) (hs : v s=0) :
    v (runBits f s bits)=0 := by
  induction bits generalizing s with
  | nil => exact hs
  | cons e bits ih => exact ih (f s e) (zero_step f v h s e hs)

theorem stopped_fixed (f : α→Bool→α) (v : α→Nat) (B : Nat) (s : α)
    (hs : v s=0 ∨ B≤v s) (bits : List Bool) : runBits (stop f v B) s bits=s := by
  induction bits with
  | nil => rfl
  | cons e bits ih => simpa [runBits,stop,hs] using ih

theorem stopped_hit (f : α→Bool→α) (v : α→Nat) (B : Nat) (hB : 0<B)
    (h : ∀ s, v (f s false)+v (f s true)≤2*v s) (s : α) (bits : List Bool)
    (hh : B≤v (runBits f s bits)) : B≤v (runBits (stop f v B) s bits) := by
  induction bits generalizing s with
  | nil => exact hh
  | cons e bits ih =>
    by_cases hz : v s=0
    · have he := zero_run f v h s (e::bits) hz; omega
    by_cases hhi : B≤v s
    · rw [stopped_fixed f v B s (Or.inr hhi)]; exact hhi
    · change B≤v (runBits (stop f v B) (stop f v B s e) bits)
      rw [stop,if_neg (by simp [hz,hhi])]
      exact ih (f s e) hh

theorem count_one_missing (f : α→Bool→α) (v : α→Nat) (hv : ∀ s, v s≤1)
    (s : α) (bits : List Bool) (hz : v (runBits f s bits)=0) :
    count f v bits.length s+1≤2^bits.length := by
  induction bits generalizing s with
  | nil => simpa [count,runBits] using hz
  | cons e bits ih =>
    have h1 := ih (f s e) hz
    have h2 := count_le f v (fun _=>1) hv bits.length (f s (!e))
    rw [count_const] at h2
    simp only [List.length_cons,count,Nat.pow_succ]
    cases e <;> simp at * <;> omega

theorem stopped_count_fixed (f : α→Bool→α) (v w : α→Nat) (B n : Nat) (s : α)
    (hs : v s=0 ∨ B≤v s) : count (stop f v B) w n s=2^n*w s := by
  induction n with
  | zero => simp [count]
  | succ n ih => simp only [count,stop,if_pos hs,ih,Nat.pow_succ]; rw [Nat.mul_right_comm,Nat.mul_two]

theorem block_mid (f : α→Bool→α) (v : α→Nat) (B H : Nat) (hB : 0<B)
    (h : ∀ s, v (f s false)+v (f s true)≤2*v s)
    (amp : ∀ s, 0<v s→∃ bits : List Bool, bits.length≤H ∧ B≤v (runBits f s bits))
    (s : α) : count (stop f v B) (mid v B) H s≤(2^H-1)*mid v B s := by
  by_cases hs : v s=0 ∨ B≤v s
  · rw [stopped_count_fixed f v _ B H s hs]
    have he : mid v B s=0 := by unfold mid; rcases hs with hh|hh <;> simp_all <;> omega
    simp [he]
  · have hp : 0<v s ∧ v s<B := by omega
    obtain ⟨bits,hlen,hh⟩ := amp s hp.1
    let t := runBits (stop f v B) s bits
    have ht : B≤v t := stopped_hit f v B hB h s bits hh
    let pad := List.replicate (H-bits.length) false
    have hl : (bits++pad).length=H := by simp [pad]; omega
    have hf : mid v B (runBits (stop f v B) s (bits++pad))=0 := by
      rw [runBits_append]
      change mid v B (runBits (stop f v B) t pad)=0
      rw [stopped_fixed f v B t (Or.inr ht)]
      unfold mid
      split <;> simp_all <;> omega
    have hmiss := count_one_missing (stop f v B) (mid v B) (fun s=>by unfold mid; split <;> decide) s (bits++pad) hf
    rw [hl] at hmiss
    have he : mid v B s=1 := by simp [mid,hp]
    rw [he,Nat.mul_one]
    omega

theorem repeated_mid (f : α→Bool→α) (v : α→Nat) (B H k : Nat)
    (hb : ∀ s, count (stop f v B) (mid v B) H s≤(2^H-1)*mid v B s) (s : α) :
    count (stop f v B) (mid v B) (k*H) s≤(2^H-1)^k*mid v B s := by
  induction k generalizing s with
  | zero => simp [count]
  | succ k ih =>
    rw [Nat.succ_mul,count_comp]
    have he := count_le (stop f v B) (fun s=>count (stop f v B) (mid v B) H s) (fun s=>(2^H-1)*mid v B s) hb (k*H) s
    rw [count_mul] at he
    have hh := Nat.mul_le_mul_left (2^H-1) (ih s)
    exact Nat.le_trans he (by simpa [Nat.pow_succ,Nat.mul_left_comm,Nat.mul_assoc,Nat.mul_comm] using hh)

theorem count_zero (f : α→Bool→α) (v : α→Nat)
    (h : ∀ s, v (f s false)+v (f s true)≤2*v s) (n : Nat) (s : α) (hs : v s=0) :
    count f (live v) n s=0 := by
  induction n generalizing s with
  | zero => simp [count,live,hs]
  | succ n ih => simp only [count,ih _ (zero_step f v h s false hs),ih _ (zero_step f v h s true hs),Nat.add_zero]

theorem live_stopped_le (f : α→Bool→α) (v : α→Nat) (B n : Nat) (hB : 0<B)
    (h : ∀ s, v (f s false)+v (f s true)≤2*v s) (s : α) :
    count f (live v) n s≤count (stop f v B) (live v) n s := by
  induction n generalizing s with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    by_cases hz : v s=0
    · rw [count_zero f v h _ _ hz]; omega
    by_cases hb : B≤v s
    · rw [stopped_count_fixed f v _ B _ _ (Or.inr hb)]
      have he : live v s=1 := by simp [live]; omega
      rw [he,Nat.mul_one]
      have h1 := count_le f (live v) (fun _=>1) (fun s=>by unfold live; split <;> decide) (n+1) s
      simpa [count_const] using h1
    · simp only [count,stop,if_neg (show ¬(v s=0 ∨ B≤v s) by simp [hz,hb])]
      exact Nat.add_le_add (ih _) (ih _)

theorem live_split (v : α→Nat) (B : Nat) (hB : 0<B) (s : α) :
    live v s=high v B s+mid v B s := by
  unfold live high mid
  split <;> split <;> split <;> simp_all <;> omega

-- An elementary Bernoulli inequality, avoiding real analysis.
theorem bernoulli (M k : Nat) (hM : 0<M) :
    (M-1)^k*(M+k)≤M^(k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : (M-1)*(M+(k+1))≤M*(M+k) := by
      have h1 : (M-1)*(M+k)+(M-1)=(M-1)*(M+(k+1)) := by rw [show M+(k+1)=M+k+1 by omega]; simp only [Nat.mul_add,Nat.mul_one]
      have h2 : M*(M+k)=(M-1)*(M+k)+(M+k) := by
        calc
          M*(M+k)=((M-1)+1)*(M+k) := by congr 1; omega
          _=(M-1)*(M+k)+(M+k) := by rw [Nat.add_mul,Nat.one_mul]
      omega
    calc
      (M-1)^(k+1)*(M+(k+1))=(M-1)^k*((M-1)*(M+(k+1))) := by rw [Nat.pow_succ,Nat.mul_assoc]
      _≤(M-1)^k*(M*(M+k)) := Nat.mul_le_mul_left _ he
      _=M*((M-1)^k*(M+k)) := by ac_rfl
      _≤M*M^(k+1) := Nat.mul_le_mul_left _ ih
      _=M^(k+1+1) := by rw [Nat.pow_succ M (k+1),Nat.mul_comm]

theorem geometric_small (M d : Nat) (hM : 0<M) :
    d*(M-1)^(d*M)≤M^(d*M) := by
  have hh := bernoulli M (d*M) hM
  have he : d*M≤M+d*M := by omega
  have h1 := Nat.mul_le_mul_left ((M-1)^(d*M)) he
  have h2 := Nat.le_trans h1 hh
  rw [Nat.pow_succ] at h2
  have h3 : (d*(M-1)^(d*M))*M≤M^(d*M)*M := by simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h2
  exact Nat.le_of_mul_le_mul_right h3 hM

/-- Uniform finite-cylinder extinction bound.  For any precision denominator d,
    at some depth at most 1/d of binary continuations still have positive weight.
    The depth depends only on d, initial weight and the uniform amplification
    bound, not on the transition system's starting state. -/
theorem extinction (f : α→Bool→α) (v : α→Nat)
    (h : ∀ s, v (f s false)+v (f s true)≤2*v s)
    (H : Nat→Nat)
    (amp : ∀ B s, 0<v s→∃ bits : List Bool, bits.length≤H B ∧ B≤v (runBits f s bits))
    (s : α) (d : Nat) (hd : 0<d) :
    ∃ n, d*count f (live v) n s≤2^n := by
  let B := 2*d*(v s+1)
  have hB : 0<B := Nat.mul_pos (by omega) (by omega)
  let M := 2^(H B)
  let k := 2*d*M
  let n := k*H B
  refine ⟨n,?_⟩
  have hhi := high_count_bound f v B n h s
  have hhi' : 2*d*count (stop f v B) (high v B) n s≤2^n := by
    let c := count (stop f v B) (high v B) n s
    change B*c≤2^n*v s at hhi
    change 2*d*c≤2^n
    have he : (2*d*c)*(v s+1)=B*c := by unfold B; ac_rfl
    have hbound : (2*d*c)*(v s+1)≤2^n*(v s+1) := by
      rw [he]
      exact Nat.le_trans hhi (Nat.mul_le_mul_left _ (by omega))
    exact Nat.le_of_mul_le_mul_right hbound (by omega)
  have hmid := repeated_mid f v B (H B) k (block_mid f v B (H B) hB h (amp B)) s
  have hm1 : mid v B s≤1 := by unfold mid; split <;> decide
  have hmid' : count (stop f v B) (mid v B) n s≤(M-1)^k := by
    exact Nat.le_trans hmid (by simpa [M] using Nat.mul_le_mul_left ((M-1)^k) hm1)
  have hg := geometric_small M (2*d) (Nat.two_pow_pos _)
  change (2*d)*(M-1)^k≤M^k at hg
  have hpow : M^k=2^n := by
    unfold M n
    rw [←Nat.pow_mul,Nat.mul_comm]
  rw [hpow] at hg
  have hmid'' := Nat.le_trans (Nat.mul_le_mul_left (2*d) hmid') hg
  have halive := live_stopped_le f v B n hB h s
  have hsplit : count (stop f v B) (live v) n s=count (stop f v B) (high v B) n s+count (stop f v B) (mid v B) n s := by
    have he : live v=(fun s=>high v B s+mid v B s) := funext (live_split v B hB)
    rw [he,count_add]
  rw [hsplit] at halive
  have hh := Nat.mul_le_mul_left (2*d) halive
  rw [Nat.mul_add, Nat.mul_assoc] at hh
  omega

end FiniteTree

/-- For every good affine inverse family, surviving binary cylinders have
    arbitrarily small density. -/
theorem affine_extinction (a : Affine) (h : Good a) (d : Nat) (hd : 0<d) :
    ∃ n, d*FiniteTree.count (next a h) (FiniteTree.live (fun s=>weight s.pop)) n (root a)≤2^n :=
  FiniteTree.extinction (next a h) (fun s=>weight s.pop)
    (fun s=>step_supermean a s.n s.b s.pop h) (fun B=>F B+1)
    (fun B s hs=>amplify_population a h s B hs) (root a) d hd

#print axioms FiniteTree.extinction
#print axioms affine_extinction
end BB6.Agent21Dyadic
