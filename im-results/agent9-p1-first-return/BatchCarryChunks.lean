import BatchCarryBit
namespace BB6.Agent9BatchCarry

/-- A packed prelude advances the common clock without inspecting births. -/
def bitRewind (L q bits : Nat) : Nat → Nat
  | 0 => bits
  | d+1 => bitRewind L (q-1) (bitBack L (q-1) bits) d

theorem bitRewind_sound (L q d k bits : Nat) (hq : d+4≤q) (hcap : q+k<2^L)
    (hs : ∀ c∈live q k, bits.testBit c=true) :
    ∀ c∈live (q-d) (k+d), (bitRewind L q bits d).testBit c=true := by
  induction d generalizing q k bits with
  | zero => simpa [bitRewind] using hs
  | succ d ih =>
    have hEq : live (q-1) (k+1)=back (q-1) (live q k) := by rw [live,show q-1+1=q by omega]
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
    simpa [bitRewind,show q-1-d=q-(d+1) by omega,show k+1+d=k+(d+1) by omega] using
      ih (q-1) (k+1) (bitBack L (q-1) bits) (by omega) (by omega) hnext

def listCheck (q R : Nat) (zs : List Nat) : Bool :=
  !(decide (q%2=0 ∧ q-4≤R) && zs.contains ((q-2)/2))

def listScan (R q : Nat) (zs : List Nat) : Nat → Bool × List Nat
  | 0 => (listCheck q R zs,zs)
  | d+1 =>
    let out := listScan R (q-1) (back (q-1) zs) d
    (listCheck q R zs && out.1,out.2)

theorem localCheck (q R k : Nat) (zs : List Nat) (hs : ∀ c∈live q k, c∈zs) :
    ∀ n, n+4=q → n%2=0 → n≤R → listCheck q R zs=true → (n+2)/2∉live (n+4) (q+k-(n+4)) := by
  intro n hqn he hr hcheck hm
  subst q
  have hin := hs ((n+2)/2) (by simpa using hm)
  have hcheck' : ¬ (n+2)/2∈zs := by
    simpa only [listCheck,show (n+4)%2=0 by omega,show n+4-4=n by omega,show n+4-2=n+2 by omega,hr,true_and,decide_true,Bool.true_and,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] using hcheck
  exact hcheck' hin

theorem listScan_sound (R q d k : Nat) (zs : List Nat) (hq : d+4≤q)
    (hs : ∀ c∈live q k, c∈zs) (hc : (listScan R q zs d).1=true) :
    (∀ c∈live (q-d) (k+d), c∈(listScan R q zs d).2) ∧
    (∀ n, q-d≤n+4 → n+4≤q → n%2=0 → n≤R → (n+2)/2∉live (n+4) (q+k-(n+4))) := by
  induction d generalizing q k zs with
  | zero =>
    refine ⟨by simpa [listScan] using hs,?_⟩
    intro n hlo hhi he hr
    exact localCheck q R k zs hs n (by omega) he hr (by simpa [listScan] using hc)
  | succ d ih =>
    simp only [listScan,Bool.and_eq_true] at hc
    have hEq : live (q-1) (k+1)=back (q-1) (live q k) := by rw [live,show q-1+1=q by omega]
    have hnext : ∀ c∈live (q-1) (k+1), c∈back (q-1) zs := by
      intro c hmem
      rw [hEq,mem_back] at hmem
      · obtain ⟨z,hz,he⟩ := hmem
        have hi := he.1
        have hp := (edge_iff_parent (q-1) c z he.2.1).mp he
        unfold back
        rw [mem_join,mem_branch,mem_branch]
        cases hb : decide (2*z<q-1)
        · right; exact ⟨⟨z,hs z hz,hb,hp.2.symm⟩,hi⟩
        · left; exact ⟨⟨z,hs z hz,hb,hp.2.symm⟩,hi⟩
      · intro z hz
        rw [show q-1+1=q by omega]
        exact live_interior q z k hz
    obtain ⟨hprop,hexcl⟩ := ih (q-1) (k+1) (back (q-1) zs) (by omega) hnext hc.2
    refine ⟨?_,?_⟩
    · simpa [listScan,show q-1-d=q-(d+1) by omega,show k+1+d=k+(d+1) by omega] using hprop
    · intro n hlo hhi he hr
      by_cases h : n+4=q
      · exact localCheck q R k zs hs n h he hr hc.1
      · simpa [show q-1+(k+1)=q+k by omega] using hexcl n (by omega) (by omega) he hr

/-- Sparse checkpoint lists can be supplied by an untrusted generator. -/
def packList : List Nat → Nat
  | [] => 0
  | x::xs => (2^x) ||| packList xs

theorem packList_sound (xs : List Nat) (c : Nat) :
    (packList xs).testBit c=true ↔ c∈xs := by
  induction xs with
  | nil => simp [packList]
  | cons x xs ih =>
    simp [packList,Nat.testBit_or,Nat.testBit_two_pow,ih]
    exact or_congr (eq_comm) Iff.rfl

def LiveCover (F q : Nat) (xs : List Nat) : Prop :=
  ∀ c∈live q (F-q), c∈xs

def ExcludedBirths (F R lo hi : Nat) : Prop :=
  ∀ n, lo≤n+4 → n+4≤hi → n%2=0 → n≤R →
    (n+2)/2∉live (n+4) (F-(n+4))

def Verified (F R top q : Nat) (xs : List Nat) : Prop :=
  LiveCover F q xs ∧ ExcludedBirths F R q top

theorem packed_start (L F R q d : Nat) (xs : List Nat)
    (hF : F<2^L) (hq : q+d=F) (_hlo : 4≤q) (hR : R+4<q)
    (hpack : bitRewind L F (mask F) d=packList xs) :
    Verified F R q q xs := by
  constructor
  · intro c hc
    apply (packList_sound xs c).mp
    rw [←hpack]
    apply bitRewind_sound L F d 0 (mask F) (by omega) (by omega)
      (fun c h => mask_sound F c ((mem_terminal F c).mp h)) c
    simpa [show F-d=q by omega,show F-q=d by omega] using hc
  · intro n h₁ h₂ h₃ h₄
    omega

/-- Each local kernel equality extends an already verified sweep. -/
theorem extend_block (F R top q d : Nat) (xs ys : List Nat)
    (hq : q≤F) (hlo : d+4≤q) (_htop : q≤top)
    (prev : Verified F R top q xs)
    (hcheck : listScan R q xs d=(true,ys)) :
    Verified F R top (q-d) ys := by
  have hc : (listScan R q xs d).1=true := by rw [hcheck]
  obtain ⟨hl,he⟩ := listScan_sound R q d (F-q) xs hlo prev.1 hc
  rw [hcheck] at hl
  have hsum : F-q+d=F-(q-d) := by omega
  have hsum' : q+(F-q)=F := by omega
  refine ⟨?_,?_⟩
  · intro c hm
    exact hl c (by simpa [hsum] using hm)
  · intro n h₁ h₂ h₃ h₄
    by_cases h : n+4≤q
    · simpa [hsum'] using he n h₁ h h₃ h₄
    · exact prev.2 n (by omega) h₂ h₃ h₄

theorem verified_interval (F R top lo q : Nat) (xs : List Nat)
    (hq : q≤lo+4) (hR : R+4≤top) (ht : top≤F)
    (hK : F≤2*lo+3) (hl : 14≤lo)
    (cert : Verified F R top q xs) :
    ∀ n, lo≤n → n≤R → n%2=0 → ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  intro n hnlo hnhi he
  apply critical_reset_no_reach_batch F lo n (by omega) hnlo (by omega) (by omega) he
  intro hm
  have hc := ((mem_batch F lo n (by omega)).mp hm).2.2.2
  exact cert.2 n (by omega) (by omega) he hnhi hc

#print axioms bitRewind_sound
#print axioms listScan_sound
#print axioms packList_sound
#print axioms packed_start
#print axioms extend_block
#print axioms verified_interval
end BB6.Agent9BatchCarry
