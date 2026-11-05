import BB429SevenStrong
import Lean.Elab.Tactic.Omega
namespace BB429OddResetGate
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000

/-- The exact 12-branch source map has no incoming step to (0,6). -/
theorem no_preimage_zero_six (x y : Nat) :
    BB429.next (x,y) ≠ some (0,6) := by
  intro hs
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

theorem rooted_no_zero_six (n : Nat) :
    BB429.run n (0,0) ≠ some (0,6) := by
  intro h
  cases n with
  | zero => simp [BB429.run] at h
  | succ n =>
    simp only [BB429.run] at h
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at h
    | some p =>
      simp only [hp,Option.bind_some] at h
      exact no_preimage_zero_six p.1 p.2 h

/-- An odd second output must come from the first (doubling) branch. -/
theorem incoming_odd_second (x y a b : Nat)
    (hs : BB429.next (x,y)=some (a,b)) (hb : b%2=1) :
    a=2*x+3 ∧ y=b+a := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

/-- No actual blank orbit reaches the near-terminal odd reset-input line
    w=2u-3 in first-counter residue 3 mod8, including the small u=3 case. -/
theorem rooted_no_odd_reset_three (n u w : Nat)
    (hr : BB429.run n (0,0)=some (u,w))
    (hg : w+3=2*u) (hu : u%8=3) : False := by
  have hw : w%2=1 := by omega
  cases n with
  | zero => simp [BB429.run] at hr; omega
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      obtain ⟨ha,hy⟩ := incoming_odd_second p.1 p.2 u w hr hw
      by_cases h0 : p.1=0
      · have hz : BB429.run n (0,0)=some (0,6) := by
          have heq : p=(0,6) := Prod.ext h0 (by omega)
          simpa only [heq] using hp
        exact rooted_no_zero_six n hz
      · have hpos : 0<p.1 := by omega
        have hev : p.1%2=0 := by omega
        have hh := BB429RootEven8.rooted_positive_even_eight n p.1 p.2 hp hpos hev
        omega

/-- The exact source predecessor of any positive even first counter (>=6). -/
theorem incoming_even (x y a b : Nat)
    (hs : BB429.next (x,y)=some (a,b))
    (ha : 6≤a) (he : a%2=0) :
    4*x+14=4*a+b ∧ 2*y=b ∧ b%4=2 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

/-- Entire authentic near-halt reset feeder u=23(mod32) is excluded.
    Its forced second ancestor violates the strengthened 7(mod8) root cell. -/
theorem rooted_no_odd_reset_twenty_three (n u w : Nat)
    (hr : BB429.run n (0,0)=some (u,w))
    (hg : w+3=2*u) (hu : u%32=23) : False := by
  have hw : w%2=1 := by omega
  cases n with
  | zero => simp [BB429.run] at hr; omega
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      obtain ⟨ha,hy⟩ := incoming_odd_second p.1 p.2 u w hr hw
      have hpmod : p.1%16=10 := by omega
      have hpeven : p.1%2=0 := by omega
      have hppos : 6≤p.1 := by omega
      cases n with
      | zero =>
        simp [BB429.run] at hp
        cases hp
        omega
      | succ n =>
        simp only [BB429.run] at hp
        cases hpp : BB429.run n (0,0) with
        | none => simp [hpp] at hp
        | some v =>
          simp only [hpp,Option.bind_some] at hp
          obtain ⟨hx,hy,hmod⟩ := incoming_even v.1 v.2 p.1 p.2 hp hppos hpeven
          have hv := BB429SevenStrong.rooted_seven_strong n v.1 v.2 hpp (by omega)
          omega

/-- Source-root 5(mod32) cannot lie on the odd reset line w=2u-3. -/
theorem rooted_no_odd_reset_five (n u w : Nat)
    (hr : BB429.run n (0,0)=some (u,w))
    (hg : w+3=2*u) (hu : u%32=5) : False := by
  have hw : w%2=1 := by omega
  cases n with
  | zero => simp [BB429.run] at hr; omega
  | succ n =>
    simp only [BB429.run] at hr
    cases hp : BB429.run n (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp,Option.bind_some] at hr
      obtain ⟨ha,hy⟩ := incoming_odd_second p.1 p.2 u w hr hw
      have hn := BB429SevenStrong.rooted_one_strong n p.1 p.2 hp (by omega)
      omega

/-- Source-root 1(mod8) cannot lie on w=2u-3, already implicit
    in Agent6's original Allowed invariant. -/
theorem rooted_no_odd_reset_one (n u w : Nat)
    (hr : BB429.run n (0,0)=some (u,w))
    (hg : w+3=2*u) (hu : u%8=1) : False := by
  have h := BB429Mod8.all_blank_returns_allowed n u w hr
  unfold BB429Mod8.Allowed at h
  omega

/-- Every authentic near-terminal odd reset input lies in one of exactly
    six necessary residues modulo 32. No such input is asserted reachable. -/
theorem rooted_odd_reset_necessary_six (n u w : Nat)
    (hr : BB429.run n (0,0)=some (u,w))
    (hg : w+3=2*u) :
    u%32=7 ∨ u%32=13 ∨ u%32=15 ∨
    u%32=21 ∨ u%32=29 ∨ u%32=31 := by
  have hodd : u%2=1 := by
    by_cases he : u%2=0
    · have hu : 0<u := by omega
      have hh := BB429RootEven8.rooted_positive_even_eight n u w hr hu he
      omega
    · omega
  have h1 : u%8≠1 := by
    intro h; exact rooted_no_odd_reset_one n u w hr hg h
  have h3 : u%8≠3 := by
    intro h; exact rooted_no_odd_reset_three n u w hr hg h
  have h5 : u%32≠5 := by
    intro h; exact rooted_no_odd_reset_five n u w hr hg h
  have h23 : u%32≠23 := by
    intro h; exact rooted_no_odd_reset_twenty_three n u w hr hg h
  omega

/-- A source step resetting first counter to zero and outputting second counter
    2(mod4) is exactly one of two boundary branches. -/
theorem zero_two_source (u w z : Nat)
    (hs : BB429.next (u,w)=some (0,z)) (hz : z%4=2) :
    (w=2*u+2 ∧ z=4*u+18) ∨
    (w+3=2*u ∧ z=4*u+2) := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

/-- True-blank zero-return exception either takes the even upper boundary,
    or one of six allowed residues on the odd near-terminal reset line. -/
theorem rooted_zero_two_gateway (n u w z : Nat)
    (hr : BB429.run n (0,0)=some (u,w))
    (hs : BB429.next (u,w)=some (0,z)) (hz : z%4=2) :
    (w=2*u+2 ∧ z=4*u+18) ∨
    (w+3=2*u ∧ z=4*u+2 ∧
     (u%32=7 ∨ u%32=13 ∨ u%32=15 ∨
      u%32=21 ∨ u%32=29 ∨ u%32=31)) := by
  rcases zero_two_source u w z hs hz with htop | hodd
  · exact Or.inl htop
  · exact Or.inr ⟨hodd.1,hodd.2,
        rooted_odd_reset_necessary_six n u w hr hodd.1⟩

/-- A true-blank upper-boundary reset predecessor must have one of seven
    congruence classes modulo 16. -/
theorem rooted_top_two_predecessor (n u : Nat)
    (hr : BB429.run n (0,0)=some (u,2*u+2)) :
    u%16=0 ∨ u%16=4 ∨ u%16=5 ∨ u%16=8 ∨
    u%16=9 ∨ u%16=12 ∨ u%16=13 := by
  have hall := BB429Mod8.all_blank_returns_allowed n u (2*u+2) hr
  have heven : 0<u → u%2=0 → (2*u+2)%8=2 :=
    fun hx he => BB429RootEven8.rooted_positive_even_eight n u (2*u+2) hr hx he
  have hseven : u%8=7 → ((2*u+2)%8=2 ∨ (2*u+2)%8=3) :=
    fun hx => BB429SevenStrong.rooted_seven_strong n u (2*u+2) hr hx
  have hone : u%16=1 → ((2*u+2)%8=1 ∨ (2*u+2)%8=2) :=
    fun hx => BB429SevenStrong.rooted_one_strong n u (2*u+2) hr hx
  unfold BB429Mod8.Allowed at hall
  omega

/-- Both exceptional reset branches now have complete necessary source
    residue conditions, while authentic reachability of any survivor is open. -/
theorem rooted_zero_two_gateway_sharp (n u w z : Nat)
    (hr : BB429.run n (0,0)=some (u,w))
    (hs : BB429.next (u,w)=some (0,z)) (hz : z%4=2) :
    (w=2*u+2 ∧ z=4*u+18 ∧
     (u%16=0 ∨ u%16=4 ∨ u%16=5 ∨ u%16=8 ∨
      u%16=9 ∨ u%16=12 ∨ u%16=13)) ∨
    (w+3=2*u ∧ z=4*u+2 ∧
     (u%32=7 ∨ u%32=13 ∨ u%32=15 ∨
      u%32=21 ∨ u%32=29 ∨ u%32=31)) := by
  rcases rooted_zero_two_gateway n u w z hr hs hz with htop | hodd
  · rcases htop with ⟨hw,hz⟩
    have hh : BB429.run n (0,0)=some (u,2*u+2) := by simpa only [hw] using hr
    exact Or.inl ⟨hw,hz,rooted_top_two_predecessor n u hh⟩
  · exact Or.inr hodd

#print axioms no_preimage_zero_six
#print axioms rooted_no_zero_six
#print axioms incoming_odd_second
#print axioms rooted_no_odd_reset_three
#print axioms incoming_even
#print axioms rooted_no_odd_reset_twenty_three
#print axioms rooted_no_odd_reset_five
#print axioms rooted_no_odd_reset_one
#print axioms rooted_odd_reset_necessary_six
#print axioms zero_two_source
#print axioms rooted_zero_two_gateway
#print axioms rooted_top_two_predecessor
#print axioms rooted_zero_two_gateway_sharp
end BB429OddResetGate
