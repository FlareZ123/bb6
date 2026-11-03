import FullForcedFilter
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- A uniform original Machine C high-stopping exclusion through three
    exact source-forced inverse edges, with no simulation-time bound. -/
theorem high_halt_affine_three_unreachable
    (j m k time : Nat)
    (hm : 6≤m) (hm4 : m%4=2)
    (hj : (j+127*m)%128=87)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (2*j+3,k) := by
  let P : Nat := 2^(2*m+2)
  have hpdiv : 128∣P := by
    dsimp [P]
    change 2^7∣2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨r,hr⟩ := hpdiv
  have hmod : (k+j+3*m+5)%128=0 := by
    have hd : 128∣k+j+3*m+5 := by
      refine ⟨r*(j+3),?_⟩
      calc
        k+j+3*m+5=P*(j+3) := hgate
        _=(128*r)*(j+3) := by rw [hr]
        _=128*(r*(j+3)) := by ac_rfl
    exact Nat.mod_eq_zero_of_dvd hd
  have hpow : 16*(m+1)≤P := by
    have hh := halting_power_linear (m-2)
    have he : 2*(m-2)+6=2*m+2 := by omega
    have hr2 : 16*((m-2)+3)=16*(m+1) := by omega
    dsimp [P]
    simpa only [he,hr2] using hh
  have hPone : 1≤P := by omega
  have hPj : j≤P*j := by simpa using Nat.mul_le_mul_right j hPone
  have hP3 : 3*m+105≤3*P := by omega
  have hprod : P*(j+3)=P*j+3*P := by rw [Nat.mul_add]; omega
  have hheight : 100≤k := by
    change k+j+3*m+5=P*(j+3) at hgate
    rw [hprod] at hgate
    omega
  let x := 2*j+3
  let y := k
  let a := x+y-2
  let b := (y-2)/2
  let c := (a+b-4)/2
  let d := (a+3*b-10)/4
  let e := (c+d-5)/2
  let f := (c+3*d-9)/4
  have hall :
    y%2=0 ∧ (x+y)%4=1 ∧
    a%2=1 ∧ b%2=1 ∧ (a+b)%4=0 ∧ (a+b)%16≠0 ∧
    c%2=0 ∧ d%2=1 ∧ (c+d+1)%16=8 ∧
    f%2=1 ∧ (e+f)%4=2 := by
    dsimp [x,y,a,b,c,d,e,f]
    omega
  rcases hall with ⟨hye,hs1,haodd,hbodd,hs2,hs16,hceven,hdodd,hs3,hfodd,hs4⟩
  have hy4 : 4≤y := by dsimp [y]; omega
  have hb5 : 5≤b := by dsimp [b,y]; omega
  have hab24 : 24≤a+b := by dsimp [a,b,x,y]; omega
  have hd5 : 5≤d := by dsimp [d,a,b,x,y]; omega
  have hcd23 : 23≤c+d := by dsimp [c,d,a,b,x,y]; omega
  have hf5 : 5≤f := by dsimp [f,c,d,a,b,x,y]; omega
  intro h
  have hreach1 : ∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (a,b) :=
    (BB6.Agent15.blank_reach_iff_affine x y hy4 hye hs1).mp ⟨time,by simpa [x,y] using h⟩
  obtain ⟨n1,hn1⟩ := hreach1
  have hreach2 : ∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (c,d) :=
    (oddodd_lowval_blank_reach_iff a b haodd hbodd hb5 hs2 hs16 hab24).mp
      ⟨n1,by simpa [c,d] using hn1⟩
  obtain ⟨n2,hn2⟩ := hreach2
  have hreach3 : ∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (e,f) :=
    (odd_seven_blank_reach_iff c d hceven hdodd hd5 hs3 hcd23).mp
      ⟨n2,by simpa [e,f] using hn2⟩
  obtain ⟨n3,hn3⟩ := hreach3
  cases n3 with
  | zero =>
      have hs : (e,f)=(5,1) := by
        simpa [BB6.Agent8Section.run] using hn3.symm
      have h : f=1 := congrArg Prod.snd hs
      omega
  | succ n =>
      have hi := blank_section_odd_image n e f hn3 hf5 hfodd
      omega

#print axioms high_halt_affine_three_unreachable
end BB6.Agent3
