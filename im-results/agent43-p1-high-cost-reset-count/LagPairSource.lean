import LagPair
import TraceComplementCover
import LongConeSource

namespace BB6.Agent43LagPair
open BB6.Agent45.DelayedCarry
open BB6.Agent43PackedRecover
open BB6.Agent43P1Complement

/-- Expand a certified half-carry cover using the forced parity of the next edge. -/
def midpoints (n P r : Nat) (xs : List Nat) : List Nat :=
  xs.map fun a => 2*a+digit n P (2*r)
theorem midpoints_sound (n s h B a C c D d r : Nat) (xs : List Nat)
    (hclock : n+s+h+3=2*r) (hhn : h<n)
    (hl : Live n (7*B) (2*n+s+3) r (·∈xs))
    (ht : Trace n s B a) (hpre : Extend n s B a h C c)
    (hsuf : Extend n (s+h) C c (n-h) D d) :
    c∈midpoints n (7*B) r xs := by
  have hw := fixed_suffix n s B a h C c (n-h) D d ht hpre hsuf (by omega)
  have hlen : 2*n+s+3-2*r=n-h := by omega
  have hw' : FixedWalk n (7*B) (2*r) c (2*n+s+3-2*r) d := by
    rw [hlen]
    simpa only [hclock] using hw
  have hm := hl c d hw'
  rw [show 2*n+s+3-2*r=(n-h-1)+1 by omega] at hw'
  obtain ⟨e,he⟩ := fixed_first hw'
  have heven := (even_half n (7*B) r c e he).1
  exact List.mem_map.mpr ⟨c/2,hm,heven.symm⟩

def recoverList (n s h B a : Nat) (xs : List Nat) : List Prefix :=
  xs.filterMap fun c =>
    let R := recoverFast n B s h c
    if R.2=a ∧ R.1%4=1 then some (R.1,c) else none

theorem recover_sound (n s h B a C c : Nat) (xs : List Nat)
    (ht : Trace n s B a) (he : Extend n s B a h C c)
    (hh : h≤n) (hm : c∈xs) (hcanon : C%4=1) :
    (C,c)∈recoverList n s h B a xs := by
  apply List.mem_filterMap.mpr
  exact ⟨c,hm,by simp [recoverFast_exact n s B a h C c ht he hh,hcanon,recoverList]⟩

theorem half_start (n : Nat) : HalfCovered n 1 [(1,(n+2)/2)] := by
  intro B a C c ht _ he
  exact covered_first n B a C c ht he

/-- It suffices to certify survival of each candidate extension through the
same fixed target window, even though no word at the final horizon is recovered. -/
theorem half_advance (n s h : Nat) (ps qs : List Prefix) (hs : 1≤s) (hh : h≤n)
    (hc : HalfCovered n s ps)
    (hmid : ∀ B a C c, (B,a)∈ps → Trace n s B a → C%4=1 →
      Extend n s B a h C c → (∃ D d, Extend n (s+h) C c (n-h) D d) → (C,c)∈qs) :
    HalfCovered n (s+h) qs := by
  intro C c B a ht hp he
  obtain ⟨D,d,hpre,hExt⟩ := trace_split n (s+h) C c s ht hs (by omega)
  have hExt' : Extend n s D d h C c := by simpa using hExt
  have hmod : D%4=1 := by
    by_cases hs1 : s=1
    · subst s
      obtain ⟨_,hb,ho,_⟩ := trace_bounds n 1 D d hpre
      simp at hb
      omega
    · have hd : 4∣2^s := by simpa using Nat.pow_dvd_pow 2 (show 2≤s by omega)
      obtain ⟨R,hR⟩ := extend_mod n s D d h C c hExt'
      rw [hR,Nat.add_mod,Nat.mul_mod,Nat.mod_eq_zero_of_dvd hd] at hp
      simpa using hp
  have hfull := extend_append n s D d h C c n B a hExt' he
  obtain ⟨F,f,hshort⟩ := extend_prefix n s D d (h+n) B a n hfull (by omega)
  obtain ⟨G,g,htail⟩ := extend_prefix n (s+h) C c n B a (n-h) he (by omega)
  exact hmid D d C c (hc D d F f hpre hmod hshort) hpre hp hExt' ⟨G,g,htail⟩

/-- A per-parent reverse cover plus exact recovery inclusion gives the
chronological extension property needed by half_advance. -/
theorem parent_advance (n s h B a C c r : Nat) (xs : List Nat) (qs : List Prefix)
    (hclock : n+s+h+3=2*r) (hh : h<n)
    (hl : Live n (7*B) (2*n+s+3) r (·∈xs))
    (hout : ∀ p∈recoverList n s h B a (midpoints n (7*B) r xs), p∈qs)
    (ht : Trace n s B a) (hc : C%4=1) (he : Extend n s B a h C c)
    (hsuf : ∃ D d, Extend n (s+h) C c (n-h) D d) :
    (C,c)∈qs := by
  obtain ⟨D,d,hsuf⟩ := hsuf
  exact hout _ (recover_sound n s h B a C c _ ht he (by omega)
    (midpoints_sound n s h B a C c D d r xs hclock hh hl ht he hsuf) hc)

theorem critical_empty_half (n s : Nat) (hn : 8000≤n) (he : n%2=0) (hs : 2≤s)
    (hcut : n+s≤BB6.Agent9FirstReturn.practicalCut n+1)
    (hc : HalfCovered n s []) : ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  apply BB6.Agent43LongCone.critical_reset_no_reach_of_short_lag n s hn he (by omega) hcut
  simpa using complete_half n s [] (by omega) he hs hc

#print axioms midpoints_sound
#print axioms half_advance
#print axioms parent_advance
#print axioms critical_empty_half
end BB6.Agent43LagPair
