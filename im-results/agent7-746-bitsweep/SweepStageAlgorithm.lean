import SweepFullLevelBatch
import SweepEvenOrbit

namespace CascadeFastReturn
open CascadeBitSweep

/-- Maximal admissible dyadic compression of a source-level deficit. -/
def terminalPair (k D : Nat) : Nat × Nat :=
  if hc : 2*k+6 ≤ D/2 ∧ D%2=0 then
    let md := terminalPair k (D/2)
    (md.1+1,md.2)
  else (0,D)
termination_by D
decreasing_by
  have hpositive : 0<D := by omega
  exact Nat.div_lt_self hpositive (by omega)

/-- Exact terminating factorization for the executable level compressor. -/
theorem terminalPair_spec (k D : Nat) (hmin : 2*k+6≤D) :
    let md := terminalPair k D
    D=2^md.1*md.2 ∧ 2*k+6≤md.2 ∧
      (md.2%2=1 ∨ md.2<4*k+12) := by
  induction D using Nat.strongRecOn with
  | ind D ih =>
    unfold terminalPair
    split
    · rename_i hc
      have hlt : D/2<D := Nat.div_lt_self (by omega) (by omega)
      have hi := ih (D/2) hlt hc.1
      have ht : D=2*(D/2) := by omega
      dsimp
      rcases hpair : terminalPair k (D/2) with ⟨m,d⟩
      rw [hpair] at hi
      dsimp at hi
      obtain ⟨hfact,hlo,hex⟩ := hi
      refine ⟨?_,hlo,hex⟩
      calc
        D = 2*(D/2) := ht
        _ = 2*(2^m*d) := by rw [hfact]
        _ = 2^(m+1)*d := by rw [Nat.pow_succ]; ac_rfl
    · rename_i hc
      have hoddOrSmall : D%2=1 ∨ D<4*k+12 := by
        by_cases hodd : D%2=1
        · exact Or.inl hodd
        · have heven : D%2=0 := by omega
          have hnot : ¬(2*k+6≤D/2 ∧ D%2=0) := hc
          have hd : D/2<2*k+6 := by omega
          right
          omega
      simpa using (show D=2^0*D ∧ 2*k+6≤D ∧ (D%2=1 ∨ D<4*k+12) from ⟨by simp,hmin,hoddOrSmall⟩)

/-- Every complete source same-level block has an exact arithmetic endpoint,
    without any synthetic low-band preparation condition. -/
theorem full_level_endpoint (k h m d : Nat)
    (hk : firstFailIndex h=k) (hnot : ¬fatalAt h)
    (hmin : 2*k+6≤d) (hfactor : deficitAt k h=2^m*d) :
    runBit h m=some (atHeight k 0 d) := by
  obtain ⟨u,hrun,hu,hdu,hnon⟩ :=
    runBit_full_level_block k h m d hk hnot hmin hfactor
  have hupper := (firstFailIndex_spec u).2
  rw [hu] at hupper
  have hbound : u≤8*2^k+k := by omega
  have heq : u=atHeight k 0 d := by
    dsimp [deficitAt] at hdu
    dsimp [atHeight]
    omega
  rw [←heq]
  exact hrun

/-- Execute one entire source dyadic level as a single compressed event.
    The returned count is the exact number of original source resets. -/
def levelMacro (h : Nat) : Nat × Option Nat :=
  if h+firstFailIndex h+4=4*2^(firstFailIndex h) then (1,none)
  else
    let k := firstFailIndex h
    let md := terminalPair k (deficitAt k h)
    let u := atHeight k 0 md.2
    (md.1+1, bitOutcome u)

/-- The executable macro performs exactly the reported original source
    first-return edges for every start h, including arbitrary synthetic h. -/
theorem levelMacro_sound (h : Nat) :
    runBit h (levelMacro h).1=(levelMacro h).2 := by
  by_cases hfat : fatalAt h
  · have he : bitOutcome h=none := by
      have hf : h+firstFailIndex h+4=4*2^(firstFailIndex h) := hfat
      simp [bitOutcome,hf]
    have hf : h+firstFailIndex h+4=4*2^(firstFailIndex h) := hfat
    simp [levelMacro,hf,runBit,he]
  · let k := firstFailIndex h
    let D := deficitAt k h
    let md := terminalPair k D
    have hmin : 2*k+6≤D := level_deficit_min h
    have hcertificate := terminalPair_spec k D hmin
    change D=2^md.1*md.2 ∧ 2*k+6≤md.2 ∧
      (md.2%2=1 ∨ md.2<4*k+12) at hcertificate
    obtain ⟨hfactor,hlo,_⟩ := hcertificate
    have hprefix := full_level_endpoint k h md.1 md.2 rfl hfat hlo hfactor
    have hn : h+firstFailIndex h+4 ≠ 4*2^(firstFailIndex h) := hfat
    simp only [levelMacro, if_neg hn]
    change runBit h (md.1+1)=bitOutcome (atHeight k 0 md.2)
    simp [runBit,hprefix]

/-- No source level recurs as an output of the compressed nonhalting macro. -/
theorem levelMacro_advances (h v : Nat)
    (hv : (levelMacro h).2=some v) :
    firstFailIndex h<firstFailIndex v := by
  by_cases hfat : fatalAt h
  · have hf : h+firstFailIndex h+4=4*2^(firstFailIndex h) := hfat
    simp [levelMacro,hf] at hv
  · let k := firstFailIndex h
    let D := deficitAt k h
    let md := terminalPair k D
    have hmin : 2*k+6≤D := level_deficit_min h
    have hcertificate := terminalPair_spec k D hmin
    change D=2^md.1*md.2 ∧ 2*k+6≤md.2 ∧
      (md.2%2=1 ∨ md.2<4*k+12) at hcertificate
    obtain ⟨hfactor,hlo,hexit⟩ := hcertificate
    have hprefix := runBit_full_level_block k h md.1 md.2 rfl hfat hlo hfactor
    obtain ⟨u,_,hu,hdu,_⟩ := hprefix
    have heq : u=atHeight k 0 md.2 := by
      have hbound := (firstFailIndex_spec u).2
      rw [hu] at hbound
      dsimp [deficitAt] at hdu
      dsimp [atHeight]
      omega
    have hterminal := full_level_terminal_next k u md.2 hu hdu hexit
    have hmacro : bitOutcome (atHeight k 0 md.2)=some v := by
      have hn : h+firstFailIndex h+4 ≠ 4*2^(firstFailIndex h) := hfat
      simpa only [levelMacro, if_neg hn] using hv
    rw [heq] at hterminal
    rcases hterminal with hn | ⟨w,hw,hjump⟩
    · rw [hn] at hmacro
      cases hmacro
    · rw [hw] at hmacro
      have he : w=v := Option.some.inj hmacro
      rw [←he]
      exact by simpa [k] using hjump

#print axioms terminalPair_spec
#print axioms full_level_endpoint
#print axioms levelMacro_sound
#print axioms levelMacro_advances
end CascadeFastReturn
