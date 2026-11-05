import BB429Rank
import Lean.Elab.Tactic.Omega

namespace BB429Tower
set_option maxHeartbeats 6000000
set_option maxRecDepth 9000

private theorem four9_step1 (v s : Nat) :
    BB429.next (16*v+80*s+17,16*v+96*s+25) =
      some (8*v+32*s+8,32*v+192*s+50) := by
  simp only [BB429.next]
  repeat' (split <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

private theorem four9_step2 (v s : Nat) :
    BB429.next (8*v+32*s+8,32*v+192*s+50) =
      some (16*v+64*s+19,16*v+128*s+31) := by
  simp [BB429.next, show 32*v+192*s+50 ≥ 2*(8*v+32*s+8)+3 by omega]
  all_goals omega

private theorem four9_step3 (v s : Nat) :
    BB429.next (16*v+64*s+19,16*v+128*s+31) =
      some (8*v+11,32*v+256*s+58) := by
  simp only [BB429.next]
  repeat' (split <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

private theorem four9_step4 (v s : Nat) :
    BB429.next (8*v+11,32*v+256*s+58) =
      some (16*v+25,16*v+256*s+33) := by
  simp [BB429.next, show 32*v+256*s+58 ≥ 2*(8*v+11)+3 by omega]
  all_goals omega

private theorem four17_step1 (u s : Nat) (hs: 0<s) :
    BB429.next (16*u+80*s+9,16*u+96*s+17) =
      some (8*u+32*s+4,32*u+192*s+34) := by
  simp only [BB429.next]
  repeat' (split <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

private theorem four17_step2 (u s : Nat) :
    BB429.next (8*u+32*s+4,32*u+192*s+34) =
      some (16*u+64*s+11,16*u+128*s+23) := by
  simp [BB429.next, show 32*u+192*s+34 ≥ 2*(8*u+32*s+4)+3 by omega]
  all_goals omega

private theorem four17_step3 (u s : Nat) (hu: 0<u) :
    BB429.next (16*u+64*s+11,16*u+128*s+23) =
      some (8*u+7,32*u+256*s+42) := by
  simp only [BB429.next]
  repeat' (split <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

private theorem four17_step4 (u s : Nat) :
    BB429.next (8*u+7,32*u+256*s+42) =
      some (16*u+17,16*u+256*s+25) := by
  simp [BB429.next, show 32*u+256*s+42 ≥ 2*(8*u+7)+3 by omega]
  all_goals omega

private theorem four9 (v s : Nat) :
    BB429.run 4 (16*v+80*s+17,16*v+96*s+25) =
      some (16*v+25,16*v+256*s+33) := by
  simp [BB429.run, four9_step1, four9_step2, four9_step3, four9_step4]

private theorem four17 (u s : Nat) (hu: 0<u) (hs:0<s) :
    BB429.run 4 (16*u+80*s+9,16*u+96*s+17) =
      some (16*u+17,16*u+256*s+25) := by
  simp [BB429.run, four17_step1 u s hs, four17_step2, four17_step3 u s hu, four17_step4]

private theorem powstep (n t : Nat) :
    16^(n+1)*t = 16*(16^n*t) ∧
    16^(n+2)*t = 256*(16^n*t) := by
  constructor
  · rw [Nat.pow_add]
    have h1 : (16:Nat)^1=16 := by decide
    rw [h1]
    simp only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  · rw [Nat.pow_add]
    have he : (16:Nat)^2=256 := by decide
    rw [he]
    simp only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]

/-- Unbounded inverse quartets for two complementary families. -/
theorem inverse_tower (n : Nat) :
   (∀ u t : Nat, 0<u → 0<t →
     ∃ p, BB429.run (4*n) p =
       some (16*u+9,16*u+17+16^(n+1)*t)) ∧
   (∀ u t : Nat, 0<u → 0<t →
     ∃ p, BB429.run (4*n) p =
       some (16*u+17,16*u+25+16^(n+1)*t)) := by
  induction n with
  | zero =>
    constructor
    · intro u t _ _
      exact ⟨(16*u+9,16*u+17+16^(0+1)*t),rfl⟩
    · intro u t _ _
      exact ⟨(16*u+17,16*u+25+16^(0+1)*t),rfl⟩
  | succ n ih =>
    obtain ⟨ih9,ih17⟩ := ih
    constructor
    · intro u t hu ht
      obtain ⟨v,rfl⟩ : ∃ v, u=v+1 := ⟨u-1,by omega⟩
      let s := 16^n*t
      have hs : 0<s := Nat.mul_pos (Nat.pow_pos (by omega)) ht
      obtain ⟨p,hp⟩ := ih17 (v+5*s) t (by omega) ht
      have he1 : 16^(n+1)*t=16*s := (powstep n t).1
      have he2 : 16^(n+1+1)*t=256*s := by
        simpa only [show n+1+1=n+2 by omega] using (powstep n t).2
      have hp' : BB429.run (4*n) p =
          some (16*(v+5*s)+17,16*(v+5*s)+25+16*s) := by
        simpa only [he1] using hp
      refine ⟨p,?_⟩
      rw [show 4*(n+1)=4*n+4 by omega, BB429.run_add, hp']
      simp only [Option.bind_some]
      rw [he2]
      have hpre : (16*(v+5*s)+17,16*(v+5*s)+25+16*s) =
          (16*v+80*s+17,16*v+96*s+25) := by
        apply Prod.ext <;> omega
      rw [hpre, four9]
      apply congrArg some
      apply Prod.ext <;> omega
    · intro u t hu ht
      let s := 16^n*t
      have hs : 0<s := Nat.mul_pos (Nat.pow_pos (by omega)) ht
      obtain ⟨p,hp⟩ := ih9 (u+5*s) t (by omega) ht
      have he1 : 16^(n+1)*t=16*s := (powstep n t).1
      have he2 : 16^(n+1+1)*t=256*s := by
        simpa only [show n+1+1=n+2 by omega] using (powstep n t).2
      have hp' : BB429.run (4*n) p =
          some (16*(u+5*s)+9,16*(u+5*s)+17+16*s) := by
        simpa only [he1] using hp
      refine ⟨p,?_⟩
      rw [show 4*(n+1)=4*n+4 by omega, BB429.run_add, hp']
      simp only [Option.bind_some]
      rw [he2]
      have hpre : (16*(u+5*s)+9,16*(u+5*s)+17+16*s) =
          (16*u+80*s+9,16*u+96*s+17) := by
        apply Prod.ext <;> omega
      rw [hpre, four17 u s hu hs]
      apply congrArg some
      apply Prod.ext <;> omega

/-- Arbitrarily long source paths end at a synthetic 9 mod 8192 halt gate.
    The path start is not claimed reachable from the real blank seed. -/
theorem arbitrarily_deep_terminal_9 (m : Nat) :
    ∃ (p : BB429.State) (a b : Nat),
      a % 8192 = 9 ∧ b+1=2*a ∧
      BB429.run (4*(m+3)) p = some (a,b) := by
  let n := m+3
  let u := 16^n
  have hu : 0<u := Nat.pow_pos (by omega)
  obtain ⟨p,hp⟩ := (inverse_tower n).1 u 1 hu (by omega)
  have hs : 16*u = 16^(m+4) := by
    dsimp [u,n]
    calc
      16 * 16^(m+3) = 16^(m+3)*16 := Nat.mul_comm _ _
      _ = 16^((m+3).succ) := (Nat.pow_succ 16 (m+3)).symm
      _ = 16^(m+4) := by congr 1
  have hm : (16^(m+4)+9)%8192=9 := by
    rw [show m+4=4+m by omega, Nat.pow_add]
    have he : (16:Nat)^4=65536 := by decide
    rw [he]
    omega
  have hp' : BB429.run (4*(m+3)) p =
      some (16*u+9,16*u+17+16^(n+1)) := by
    simpa only [Nat.mul_one] using hp
  refine ⟨p,16*u+9,16*u+17+16^(n+1),?_,?_,hp'⟩
  · simpa only [hs] using hm
  · have he : 16^(n+1)=16*u := by
      dsimp [u]
      calc
        16^(n+1) = 16^n *16 := by
          simpa only [Nat.succ_eq_add_one] using Nat.pow_succ 16 n
        _ = 16*u := by dsimp [u]; omega
    omega

#print axioms arbitrarily_deep_terminal_9
#print axioms inverse_tower
end BB429Tower
