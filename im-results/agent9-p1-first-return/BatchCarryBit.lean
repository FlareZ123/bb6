import BatchCarrySource
import BitSpread
namespace BB6.Agent9BatchCarry
open BB6.Agent28BitSpread

/-- Bits at exactly the strict interior positions 1,...,q-3. -/
def mask (q : Nat) : Nat := (2^(q-3)-1) <<< 1

theorem mask_sound (q c : Nat) (hi : Interior q c) : (mask q).testBit c=true := by
  unfold Interior at hi
  unfold mask
  rw [Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one]
  simp [show 1≤c by omega,show c-1<q-3 by omega]

/-- Broadword implementation of the same reverse edge, restricted to the
    strict interior. Soundness alone suffices for exclusion certificates. -/
def bitBack (L q bits : Nat) : Nat :=
  let u := spreadEven L bits
  (u ||| (u >>> q)) &&& mask q

theorem bitBack_sound (L q c z bits : Nat) (he : Edge q c z)
    (hbound : z<2^L) (hb : bits.testBit z=true) : (bitBack L q bits).testBit c=true := by
  have hs := spreadEven_sound L bits z hbound hb
  have hm := mask_sound q c he.1
  obtain ⟨hc,hp⟩ := (edge_iff_parent q c z he.2.1).mp he
  have hz := he.2.1
  unfold Interior at hz
  unfold bitBack
  rw [Nat.testBit_and,Nat.testBit_or,hm,Bool.and_true,hp]
  by_cases h : 2*z<q
  · rw [Nat.mod_eq_of_lt h]; simp [hs]
  · rw [Nat.mod_eq_sub_mod (by omega : q≤2*z),Nat.mod_eq_of_lt (by omega : 2*z-q<q)]
    rw [Nat.testBit_shiftRight]
    simp [show q+(2*z-q)=2*z by omega,hs]

theorem live_interior (q c k : Nat) (h : c∈live q k) : Interior q c := by
  obtain ⟨z,hz⟩ := (mem_live q c k).mp h
  cases hz with
  | nil _ _ hi => exact hi
  | cons _ _ _ _ _ he _ => exact he.1

def checkAt (q R bits : Nat) : Bool :=
  !(decide (q%2=0 ∧ q-4≤R) && bits.testBit ((q-2)/2))

def scan (L R q bits : Nat) : Nat → Bool
  | 0 => checkAt q R bits
  | d+1 => checkAt q R bits && scan L R (q-1) (bitBack L (q-1) bits) d

theorem checkAt_sound (q R n bits : Nat) (hq : n+4=q) (he : n%2=0) (hr : n≤R)
    (h : checkAt q R bits=true) : bits.testBit ((n+2)/2)=false := by
  subst q
  simpa [checkAt,show (n+4)%2=0 by omega,show n+4-4=n by omega,show n+4-2=n+2 by omega,hr] using h

/-- A checked sweep can use an arbitrary sound overapproximation of the live
    set at its initial clock. No exactness assumption on bit spreading. -/
theorem scan_sound (L R q d k n bits : Nat) (hq : d+4≤q) (hcap : q+k<2^L)
    (hs : ∀ c∈live q k, bits.testBit c=true)
    (hcheck : scan L R q bits d=true)
    (hlo : q-d≤n+4) (hhi : n+4≤q) (he : n%2=0) (hr : n≤R) :
    (n+2)/2∉live (n+4) (q+k-(n+4)) := by
  induction d generalizing q k bits with
  | zero =>
    have heq : q=n+4 := by omega
    subst q
    intro hm
    have hb : bits.testBit ((n+2)/2)=true := hs ((n+2)/2) (by simpa using hm)
    have hfalse := checkAt_sound (n+4) R n bits rfl he hr hcheck
    rw [hb] at hfalse
    contradiction
  | succ d ih =>
    simp only [scan,Bool.and_eq_true] at hcheck
    by_cases h : q=n+4
    · subst q
      intro hm
      have hb : bits.testBit ((n+2)/2)=true := hs ((n+2)/2) (by simpa using hm)
      have hfalse := checkAt_sound (n+4) R n bits rfl he hr hcheck.1
      rw [hb] at hfalse
      contradiction
    · have hEq : live (q-1) (k+1)=back (q-1) (live q k) := by rw [live,show q-1+1=q by omega]
      have hnext : ∀ c∈live (q-1) (k+1), (bitBack L (q-1) bits).testBit c=true := by
        intro c hc
        rw [hEq,mem_back] at hc
        · obtain ⟨z,hz,he⟩ := hc
          have hi := live_interior q z k hz
          unfold Interior at hi
          exact bitBack_sound L (q-1) c z bits he (by omega) (hs z hz)
        · intro z hz
          rw [show q-1+1=q by omega]
          exact live_interior q z k hz
      have hh := ih (q-1) (k+1) (bitBack L (q-1) bits) (by omega) (by omega)
        hnext hcheck.2 (by omega) (by omega)
      simpa [show q-1+(k+1)=q+k by omega] using hh

/-- Complete certificate at common final clock F for the interval [lo,hi]. -/
def check (L F lo hi : Nat) : Bool := scan L hi F (mask F) (F-(lo+4))

theorem check_absent (L F lo hi n : Nat) (hcap : F<2^L) (hlo : lo≤n)
    (hhi : n≤hi) (hF : n+4≤F) (he : n%2=0) (hc : check L F lo hi=true) : n∉batch F lo := by
  intro hm
  obtain ⟨_,_,_,hcenter⟩ := (mem_batch F lo n (by omega)).mp hm
  have h := scan_sound L hi F (F-(lo+4)) 0 n (mask F) (by omega) (by omega)
    (fun c hc => mask_sound F c ((mem_terminal F c).mp hc)) hc (by omega) hF he hhi
  exact h (by simpa using hcenter)

theorem checked_interval (L F lo hi : Nat) (hcap : F<2^L) (hlo : 14≤lo)
    (hF : hi+4≤F) (hK : F≤2*lo+3) (hc : check L F lo hi=true) :
    ∀ n, lo≤n → n≤hi → n%2=0 → ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  intro n h₁ h₂ he
  exact critical_reset_no_reach_batch F lo n (by omega) h₁ (by omega) (by omega) he
    (check_absent L F lo hi n hcap h₁ h₂ (by omega) he hc)

#print axioms bitBack_sound
#print axioms scan_sound
#print axioms check_absent
#print axioms checked_interval
end BB6.Agent9BatchCarry
