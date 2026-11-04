import FullForcedFilter
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Four successive genuine unique section predecessors exclude a first-family
    terminal counter cylinder, irrespective of the halting equation. -/
theorem first_counter_324_mod512_unreachable (q time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (1,512*q+324) := by
  intro ht
  have hA : ∃ n, BB6.Agent8Section.run secNext n (some (5,1)) =
      some (512*q+323,256*q+161) := by
    obtain ⟨n,hn⟩ := (BB6.Agent15.blank_reach_iff_affine
      1 (512*q+324) (by omega) (by omega) (by omega)).mp ⟨time,ht⟩
    have ha : 1+(512*q+324)-2=512*q+323 := by omega
    have hb : (512*q+324-2)/2=256*q+161 := by omega
    exact ⟨n,by simpa only [ha,hb] using hn⟩
  obtain ⟨nA,hA⟩ := hA
  have hB : ∃ n, BB6.Agent8Section.run secNext n (some (5,1)) =
      some (384*q+240,320*q+199) := by
    obtain ⟨n,hn⟩ := (oddodd_lowval_blank_reach_iff
      (512*q+323) (256*q+161)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).mp
      ⟨nA,hA⟩
    have ha : ((512*q+323)+(256*q+161)-4)/2=384*q+240 := by omega
    have hb : ((512*q+323)+3*(256*q+161)-10)/4=320*q+199 := by omega
    exact ⟨n,by simpa only [ha,hb] using hn⟩
  obtain ⟨nB,hB⟩ := hB
  have hC : ∃ n, BB6.Agent8Section.run secNext n (some (5,1)) =
      some (352*q+217,336*q+207) := by
    obtain ⟨n,hn⟩ := (odd_seven_blank_reach_iff
      (384*q+240) (320*q+199)
      (by omega) (by omega) (by omega) (by omega) (by omega)).mp
      ⟨nB,hB⟩
    have ha : ((384*q+240)+(320*q+199)-5)/2=352*q+217 := by omega
    have hb : ((384*q+240)+3*(320*q+199)-9)/4=336*q+207 := by omega
    exact ⟨n,by simpa only [ha,hb] using hn⟩
  obtain ⟨nC,hC⟩ := hC
  have hD : ∃ n, BB6.Agent8Section.run secNext n (some (5,1)) =
      some (344*q+210,340*q+207) := by
    obtain ⟨n,hn⟩ := (oddodd_lowval_blank_reach_iff
      (352*q+217) (336*q+207)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).mp
      ⟨nC,hC⟩
    have ha : ((352*q+217)+(336*q+207)-4)/2=344*q+210 := by omega
    have hb : ((352*q+217)+3*(336*q+207)-10)/4=340*q+207 := by omega
    exact ⟨n,by simpa only [ha,hb] using hn⟩
  obtain ⟨nD,hD⟩ := hD
  cases nD with
  | zero =>
      have h0 : (344*q+210,340*q+207)=(5,1) := by
        simpa [BB6.Agent8Section.run] using hD.symm
      have hh := congrArg Prod.snd h0
      omega
  | succ n =>
      have hi := blank_section_odd_image n (344*q+210) (340*q+207)
        hD (by omega) (by omega)
      omega

/-- First-family source stopping equation maps m modulo 512
    to the four-return forbidden counter cylinder. -/
theorem first_halt_m232_mod512_unreachable (m k time : Nat)
    (hm : m%512=232)
    (hgate : k+3*m+4=2^(2*m+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (1,k) := by
  have hm3 : 3≤m := by omega
  have hpow : 512∣2^(2*m+3) := by
    change 2^9∣2^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hmod : (k+3*m+4)%512=0 := by
    rw [hgate]
    exact Nat.mod_eq_zero_of_dvd hpow
  have hrem : k%512=324 := by omega
  have hk : k=512*(k/512)+324 := by omega
  rw [hk]
  exact first_counter_324_mod512_unreachable (k/512) time

#print axioms first_counter_324_mod512_unreachable
#print axioms first_halt_m232_mod512_unreachable
end BB6.Agent3
