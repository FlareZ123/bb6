import BB429OddResetGate
import Lean.Elab.Tactic.Omega
namespace BB429Reset31
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000

def Reach (u w : Nat) : Prop := ∃ n, BB429.run n (0,0)=some (u,w)

theorem pred (a b : Nat) (ha : 0<a) (hr : Reach a b) :
    ∃ x y, Reach x y ∧ BB429.next (x,y)=some (a,b) := by
  rcases hr with ⟨n,hn⟩
  cases n with
  | zero => simp [BB429.run] at hn; omega
  | succ n =>
    simp only [BB429.run] at hn
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hn
    | some p =>
      simp only [hp,Option.bind_some] at hn
      exact ⟨p.1,p.2,⟨n,hp⟩,hn⟩

theorem unreachable_even_bad (a b : Nat)
    (ha : 6≤a) (he : a%2=0) (hb : b%4≠2) : ¬Reach a b := by
  intro hr
  obtain ⟨x,y,hp,hs⟩ := pred a b (by omega) hr
  have hi := BB429OddResetGate.incoming_even x y a b hs ha he
  omega

/-- Source inverse alternatives for sufficiently large odd outputs. -/
theorem odd_inverse (x y a b : Nat)
    (ha : 13≤a) (ho : a%2=1)
    (hs : BB429.next (x,y)=some (a,b)) :
    (a=2*x+3 ∧ y=b+a) ∨
    (4*x+26=4*a+b ∧ 2*y=b+4 ∧ b%4=2) := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

/-- Both possible ancestors have even first counter and forbidden odd second
    counter. Parameter q is arbitrary and no finite sampling is used. -/
theorem no_20q15 (q : Nat) : ¬Reach (20*q+15) (88*q+78) := by
  intro hr
  obtain ⟨x,y,hp,hs⟩ := pred (20*q+15) (88*q+78) (by omega) hr
  rcases odd_inverse x y (20*q+15) (88*q+78) (by omega) (by omega) hs with hf|hs
  · have hx : x=10*q+6 := by omega
    have hy : y=108*q+93 := by omega
    rw [hx,hy] at hp
    exact (unreachable_even_bad (10*q+6) (108*q+93) (by omega) (by omega) (by omega)) hp
  · obtain ⟨h1,h2,h3⟩ := hs
    have hx : x=42*q+28 := by omega
    have hy : y=44*q+41 := by omega
    rw [hx,hy] at hp
    exact (unreachable_even_bad (42*q+28) (44*q+41) (by omega) (by omega) (by omega)) hp

theorem no_40q33 (q : Nat) : ¬Reach (40*q+33) (48*q+45) := by
  intro hr
  obtain ⟨x,y,hp,hs⟩ := pred (40*q+33) (48*q+45) (by omega) hr
  obtain ⟨hx,hy⟩ := BB429OddResetGate.incoming_odd_second x y (40*q+33) (48*q+45) hs (by omega)
  have hx2 : x=20*q+15 := by omega
  have hy2 : y=88*q+78 := by omega
  rw [hx2,hy2] at hp
  exact (no_20q15 q) hp

theorem no_16q14 (q : Nat) : ¬Reach (16*q+14) (96*q+90) := by
  intro hr
  obtain ⟨x,y,hp,hs⟩ := pred (16*q+14) (96*q+90) (by omega) hr
  obtain ⟨h1,h2,h3⟩ := BB429OddResetGate.incoming_even x y (16*q+14) (96*q+90) hs (by omega) (by omega)
  have hx2 : x=40*q+33 := by omega
  have hy2 : y=48*q+45 := by omega
  rw [hx2,hy2] at hp
  exact (no_40q33 q) hp

/-- Entire mod32 residue 31 of the actual near-terminal odd reset line is
    excluded by a uniform bounded inverse chain independent of q. -/
theorem no_odd_reset_31 (n u w : Nat)
    (hr : BB429.run n (0,0)=some (u,w))
    (hg : w+3=2*u) (hu : u%32=31) : False := by
  let q := u/32
  have hu0 : u=32*q+31 := by dsimp [q]; omega
  have hw0 : w=64*q+59 := by omega
  have hrr : Reach (32*q+31) (64*q+59) := ⟨n,by simpa [←hu0,←hw0] using hr⟩
  obtain ⟨x,y,hp,hs⟩ := pred (32*q+31) (64*q+59) (by omega) hrr
  obtain ⟨hx,hy⟩ := BB429OddResetGate.incoming_odd_second x y (32*q+31) (64*q+59) hs (by omega)
  have hx2 : x=16*q+14 := by omega
  have hy2 : y=96*q+90 := by omega
  rw [hx2,hy2] at hp
  exact (no_16q14 q) hp

/-- Source-proved genuine blank odd-reset first-counter gate narrows
    from the original sixteen odd classes to just five modulo 32. -/
theorem odd_reset_necessary_five (n u w : Nat)
    (hr : BB429.run n (0,0)=some (u,w))
    (hg : w+3=2*u) :
    u%32=7 ∨ u%32=13 ∨ u%32=15 ∨ u%32=21 ∨ u%32=29 := by
  have h6 := BB429OddResetGate.rooted_odd_reset_necessary_six n u w hr hg
  have h31 : u%32≠31 := by
    intro hh; exact no_odd_reset_31 n u w hr hg hh
  omega

#print axioms no_20q15
#print axioms no_odd_reset_31
#print axioms odd_reset_necessary_five
end BB429Reset31
