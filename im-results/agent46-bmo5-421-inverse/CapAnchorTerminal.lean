import CapCanonicalReach

namespace CapSieve

def terminalAt (k n : Nat) : Option Nat :=
  let w := (2*(k+n)+3)/3^n
  if 0<w ∧ w%3=2^k%3 ∧ 3^n*w=2*(k+n)+3 then
    some (rayParent k ((w+3)/2))
  else none

theorem terminal_at_sound {k n q : Nat} (hk : 1≤k)
    (he : terminalAt k n=some q) :
    CanonQ k q ∧ 3^n*(2*positiveNext k q-3)=2*(k+n)+3 := by
  unfold terminalAt at he
  dsimp at he
  split at he
  next h =>
    have hv := terminal_weight_valid h.2.2
    obtain ⟨hp,_,hw⟩ := negative_entry_exit hv h.2.1
    obtain ⟨hc,hnext⟩ := ray_parent_spec hk hp
    obtain rfl := Option.some.inj he
    exact ⟨hc,by rw [hnext,hw]; exact h.2.2⟩
  next h => contradiction

theorem terminal_at_complete {k n q : Nat} (hk : 1≤k) (hc : CanonQ k q)
    (he : 3^n*(2*positiveNext k q-3)=2*(k+n)+3) :
    terminalAt k n=some q := by
  let w := 2*positiveNext k q-3
  have he' : 3^n*w=2*(k+n)+3 := he
  have hf : positiveNext k q<k+7 := by
    by_cases h : positiveNext k q<k+7
    · exact h
    · have hbig : 2*k+7<w := by dsimp [w]; omega
      have hh := CapNegative.above_grows hbig n
      omega
  have hw := entry_weight hc.1 hf
  have hpos : 0<3^n := Nat.pow_pos (by decide)
  have hquot : (2*(k+n)+3)/3^n=w := by
    rw [←he',Nat.mul_div_cancel_left _ hpos]
  unfold terminalAt
  dsimp
  rw [hquot,if_pos (show 0<w ∧ w%3=2^k%3 ∧ 3^n*w=2*(k+n)+3 from ⟨hw.1.1,hw.2,he'⟩)]
  have hlow := (positive_next_bounds (show 0<q by have := hc.1.1; omega) hc.1.2.1).1
  have hw' : (w+3)/2=positiveNext k q := by dsimp [w]; omega
  rw [hw',ray_parent_inverse hk hc]

theorem terminal_at_iff {k n q : Nat} (hk : 1≤k) :
    terminalAt k n=some q ↔
      CanonQ k q ∧ 3^n*(2*positiveNext k q-3)=2*(k+n)+3 :=
  ⟨terminal_at_sound hk,fun ⟨hc,he⟩ => terminal_at_complete hk hc he⟩

/-- Exact all-time target for a band-five anchor. -/
theorem anchor_terminal_iff {a : Nat} (ha : CanonQ 5 a) :
    (∃ limit, signedHaltBy limit 5 a=true) ↔
      ∃ k n q, 5≤k ∧ terminalAt k n=some q ∧ anchorOf k q=some (5,a) := by
  constructor
  · rintro ⟨limit,hl⟩
    obtain ⟨k,q,hr,_,he⟩ := (signed_halt_canonical ha).mp hl
    have hv := c_reach_valid hr
    have hk := hv.2.2
    obtain ⟨n,hn⟩ := (positive_event_terminal_iff (by omega) hv.2.1.1).mp he
    exact ⟨k,n,q,hk,terminal_at_complete (by omega) hv.2.1 hn,(anchor_of_iff hv.2.1 ha).mpr hr⟩
  · rintro ⟨k,n,q,hk,ht,ha'⟩
    obtain ⟨hc,he⟩ := terminal_at_sound (by omega : 1≤k) ht
    have hr := (anchor_of_iff hc ha).mp ha'
    have hterm := (positive_event_terminal_iff (by omega : 1≤k) hc.1).mpr ⟨n,he⟩
    exact ⟨(signedEvent k q).1,(signed_halt_canonical ha).mpr ⟨k,q,hr,by omega,hterm⟩⟩

#print axioms terminal_at_iff
#print axioms anchor_terminal_iff
end CapSieve
