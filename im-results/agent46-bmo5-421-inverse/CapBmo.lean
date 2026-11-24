import CapBandInverse
namespace CapSieve.Bmo

open CapSieve

structure State where
  a : Nat
  b : Nat
  deriving DecidableEq, Repr

def F (a : Nat) : Nat := 2*P a-1

def S (a : Nat) : Nat := 2*P a-a-10

def encode (s : State) : Nat := S s.a+s.b+5

def Stable (s : State) : Prop := s.b<F s.a

def Halt (s : State) : Prop := s.b+1=F s.a

theorem f_pos (a : Nat) : 0<F a := by
  have := p_ge a
  unfold F; omega

theorem s_add (a : Nat) : S a+a+10=2*P a := by
  have := p_ge a
  unfold S; omega

theorem s_succ (a : Nat) : S (a+1)=S a+F a := by
  have h:=s_add a
  have h':=s_add (a+1)
  rw [p_succ] at h'
  unfold F; omega

theorem encode_ge (s : State) : 5≤encode s := by unfold encode; omega

theorem encode_positive (a b : Nat) (hb : 0<b) : encode ⟨a,b⟩=L (a+1)+(b-1) := by
  have h:=s_add a
  have h':=l_add (a+1)
  rw [p_succ] at h'
  unfold encode; dsimp; omega

theorem encode_zero (a : Nat) : encode ⟨a,0⟩=L a+(P a-2) := by
  have h:=s_add a
  have h':=l_add a
  have hp:=p_ge a
  unfold encode; dsimp; omega

theorem encode_band_positive {a b : Nat} (hb : 0<b) (hs : Stable ⟨a,b⟩) :
    Band (a+1) (encode ⟨a,b⟩) := by
  rw [encode_positive a b hb]
  unfold Band
  rw [l_succ (a+1)]
  unfold Stable F at hs
  dsimp at hs
  rw [p_succ]
  omega

theorem encode_halt {s : State} (hs : Stable s) : Halt s ↔ ∃ i, encode s=T i := by
  cases s with
  | mk a b =>
    have hf:=f_pos a
    have hp:=p_ge a
    have ht : ∀ j, T j=L j+(P j-3) := by
      intro j
      have h:=t_add j
      have hl:=l_add j
      have hp:=p_ge j
      unfold P at h hl hp ⊢; omega
    have htb : ∀ j, Band j (T j) := by
      intro j; rw [ht]; unfold Band; rw [l_succ]; have := p_ge j; omega
    constructor
    · intro h
      unfold Halt F at h
      dsimp at h
      have hb : 0<b := by omega
      refine ⟨a+1,?_⟩
      rw [encode_positive a b hb,ht,p_succ]
      omega
    · rintro ⟨i,he⟩
      by_cases hb : b=0
      · subst b
        rw [encode_zero] at he
        have hi:=band_unique (special_band a) (he.symm ▸ htb i)
        subst i
        rw [ht] at he
        omega
      · have hb' : 0<b := by omega
        have hi:=band_unique (encode_band_positive hb' hs) (he.symm ▸ htb i)
        subst i
        rw [encode_positive a b hb',ht,p_succ] at he
        unfold Halt F; dsimp; omega

/-- Published BMO5 recurrence with the distinguished target made terminal. -/
inductive Step : State → State → Prop where
  | shift (a b : Nat) (hb : F a≤b) : Step ⟨a,b⟩ ⟨a+1,b-F a⟩
  | grow (a b : Nat) (hb : b+1<F a) : Step ⟨a,b⟩ ⟨a,3*b+a+5⟩

theorem shift_encode {a b : Nat} (hb : F a≤b) :
    encode ⟨a+1,b-F a⟩=encode ⟨a,b⟩ := by
  unfold encode; dsimp
  rw [s_succ]; omega

theorem grow_arc {a b : Nat} (hb : b+1<F a) :
    Arc (encode ⟨a,b⟩) (encode ⟨a,3*b+a+5⟩) := by
  have he : encode ⟨a,3*b+a+5⟩=3*b+2*P a := by
    have h:=s_add a
    unfold encode; dsimp; omega
  rw [he]
  by_cases h0 : b=0
  · subst b
    rw [encode_zero]
    simpa using Arc.special a
  · rw [encode_positive a b (by omega)]
    have hr : b-1+4≤P (a+1) := by rw [p_succ]; unfold F at hb; omega
    have hy : 3*b+2*P a=3*(b-1)+P (a+1)+3 := by rw [p_succ]; omega
    rw [hy]
    exact .regular (a+1) (b-1) hr

theorem arc_cases {x y : Nat} (h : Arc x y) :
    (x=1 ∧ y=5) ∨ (∃ k r, r+4≤P k ∧ x=L k+r ∧ y=3*r+P k+3) ∨
    (∃ k, x=L k+(P k-2) ∧ y=2*P k) := by
  cases h with
  | one => exact Or.inl ⟨rfl,rfl⟩
  | regular k r hr => exact Or.inr (Or.inl ⟨k,r,hr,rfl,rfl⟩)
  | special k => exact Or.inr (Or.inr ⟨k,rfl,rfl⟩)

theorem arc_functional {x y z : Nat} (h : Arc x y) (h' : Arc x z) : y=z := by
  rcases arc_cases h with ⟨hx,hy⟩|⟨k,r,hr,hx,hy⟩|⟨k,hx,hy⟩ <;>
    rcases arc_cases h' with ⟨hx',hz⟩|⟨l,s,hs,hx',hz⟩|⟨l,hx',hz⟩
  · omega
  · have := l_add l; have := p_ge l; omega
  · have := l_add l; have := p_ge l; omega
  · have := l_add k; have := p_ge k; omega
  · have hk:=band_unique (hx.symm ▸ regular_band k r hr) (hx'.symm ▸ regular_band l s hs)
    subst l; omega
  · have hk:=band_unique (hx.symm ▸ regular_band k r hr) (hx'.symm ▸ special_band l)
    subst l; omega
  · have := l_add k; have := p_ge k; omega
  · have hk:=band_unique (hx.symm ▸ special_band k) (hx'.symm ▸ regular_band l s hs)
    subst l; omega
  · have hk:=band_unique (hx.symm ▸ special_band k) (hx'.symm ▸ special_band l)
    subst l; omega

theorem terminal_no_arc (i y : Nat) : ¬ Arc (T i) y := by
  have ht : T i=L i+(P i-3) := by
    have h:=t_add i
    have hl:=l_add i
    have hp:=p_ge i
    unfold P at h hl hp ⊢; omega
  have hb : Band i (T i) := by
    rw [ht]; unfold Band; rw [l_succ]; have := p_ge i; omega
  intro h
  rcases arc_cases h with ⟨hx,hy⟩|⟨k,r,hr,hx,hy⟩|⟨k,hx,hy⟩
  · have := l_add i; have := p_ge i; omega
  · have hk:=band_unique hb (hx.symm ▸ regular_band k r hr)
    subst k; omega
  · have hk:=band_unique hb (hx.symm ▸ special_band k)
    subst k; have := p_ge i; omega

inductive Reach (s : State) : State → Prop where
  | refl : Reach s s
  | tail {x y : State} : Reach s x → Step x y → Reach s y

inductive AReach (s : Nat) : Nat → Prop where
  | refl : AReach s s
  | tail {x y : Nat} : AReach s x → Arc x y → AReach s y

theorem reach_trans {s t u : State} (h : Reach s t) (h' : Reach t u) : Reach s u := by
  induction h' with
  | refl => exact h
  | tail _ e ih => exact .tail ih e

theorem normalize_exists (s : State) : ∃ t, Reach s t ∧ Stable t ∧ encode t=encode s := by
  cases s with
  | mk a b =>
    by_cases hb : F a≤b
    · obtain ⟨t,hr,hs,he⟩:=normalize_exists ⟨a+1,b-F a⟩
      exact ⟨t,reach_trans (.tail .refl (.shift a b hb)) hr,hs,he.trans (shift_encode hb)⟩
    · exact ⟨⟨a,b⟩,.refl,by unfold Stable; dsimp; omega,rfl⟩
termination_by s.b
decreasing_by have := f_pos a; omega

theorem reach_encode {s t : State} (h : Reach s t) : AReach (encode s) (encode t) := by
  induction h with
  | refl => exact .refl
  | tail _ e ih =>
    cases e with
    | shift a b hb => rwa [shift_encode hb]
    | grow a b hb => exact .tail ih (grow_arc hb)

theorem arc_lift {s : State} {y : Nat} (hs : Stable s) (h : Arc (encode s) y) :
    ∃ t, Reach s t ∧ Stable t ∧ encode t=y := by
  cases s with
  | mk a b =>
    have hn : b+1<F a := by
      by_cases he : b+1<F a
      · exact he
      · have ht : Halt ⟨a,b⟩ := by unfold Halt Stable at *; dsimp at *; omega
        obtain ⟨i,he'⟩ := (encode_halt hs).mp ht
        rw [he'] at h
        exact False.elim (terminal_no_arc i y h)
    let u : State := ⟨a,3*b+a+5⟩
    have he : encode u=y := arc_functional (grow_arc hn) h
    obtain ⟨t,hr,ht,he'⟩:=normalize_exists u
    exact ⟨t,reach_trans (.tail .refl (.grow a b hn)) hr,ht,he'.trans he⟩

theorem reach_lift {s : State} {y : Nat} (hs : Stable s) (h : AReach (encode s) y) :
    ∃ t, Reach s t ∧ Stable t ∧ encode t=y := by
  induction h with
  | refl => exact ⟨s,.refl,hs,rfl⟩
  | tail _ e ih =>
    obtain ⟨t,hr,ht,he⟩:=ih
    rw [←he] at e
    obtain ⟨u,hr',hu,he'⟩:=arc_lift ht e
    exact ⟨u,reach_trans hr hr',hu,he'⟩

/-- Exact target-existence equivalence with the original two-counter recurrence. -/
theorem halt_iff {s : State} (hs : Stable s) :
    (∃ t, Reach s t ∧ Halt t) ↔ ∃ i, AReach (encode s) (T i) := by
  constructor
  · rintro ⟨t,hr,hh⟩
    have ht : Stable t := by unfold Stable Halt at *; omega
    obtain ⟨i,he⟩:=(encode_halt ht).mp hh
    exact ⟨i,he ▸ reach_encode hr⟩
  · rintro ⟨i,hr⟩
    obtain ⟨t,ht,hs',he⟩:=reach_lift hs hr
    exact ⟨t,ht,(encode_halt hs').mpr ⟨i,he⟩⟩

/-- The original total recurrence, without stopping at the target. -/
def rawNext (s : State) : State :=
  if F s.a≤s.b then ⟨s.a+1,s.b-F s.a⟩ else ⟨s.a,3*s.b+s.a+5⟩

def orbit (s : State) : Nat → State
  | 0 => s
  | n+1 => rawNext (orbit s n)

theorem step_raw {s t : State} (h : Step s t) : rawNext s=t := by
  cases h with
  | shift a b hb => simp [rawNext,hb]
  | grow a b hb => simp [rawNext,show ¬F a≤b by omega]

theorem raw_step {s : State} (h : ¬ Halt s) : Step s (rawNext s) := by
  cases s with
  | mk a b =>
    unfold rawNext; dsimp
    by_cases hb : F a≤b
    · rw [ite_eq_left hb]; exact .shift a b hb
    · rw [ite_eq_right hb]
      unfold Halt at h; dsimp at h
      exact .grow a b (by omega)

theorem reach_orbit {s t : State} (h : Reach s t) : ∃ n, orbit s n=t := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | tail _ e ih =>
    obtain ⟨n,hn⟩:=ih
    exact ⟨n+1,by rw [orbit,hn,step_raw e]⟩

theorem first_target (s : State) (n : Nat) :
    Reach s (orbit s n) ∨ ∃ t, Reach s t ∧ Halt t := by
  induction n with
  | zero => exact Or.inl .refl
  | succ n ih =>
    rcases ih with hr|hh
    · by_cases h : Halt (orbit s n)
      · exact Or.inr ⟨_,hr,h⟩
      · exact Or.inl (.tail hr (raw_step h))
    · exact Or.inr hh

theorem raw_hit_iff (s : State) : (∃ n, Halt (orbit s n)) ↔ ∃ t, Reach s t ∧ Halt t := by
  constructor
  · rintro ⟨n,hn⟩
    rcases first_target s n with h|h
    · exact ⟨_,h,hn⟩
    · exact h
  · rintro ⟨t,hr,hh⟩
    obtain ⟨n,hn⟩:=reach_orbit hr
    exact ⟨n,hn.symm ▸ hh⟩

theorem raw_target_iff {s : State} (hs : Stable s) :
    (∃ n, Halt (orbit s n)) ↔ ∃ i, AReach (encode s) (T i) :=
  (raw_hit_iff s).trans (halt_iff hs)

/-- Direct statement for the recurrence's three distinct small seeds. -/
theorem seed_three : (∃ n, Halt (orbit ⟨0,3⟩ n)) ↔ ∃ i, AReach 8 (T i) :=
  raw_target_iff (s:=⟨0,3⟩) (by unfold Stable; decide)

theorem seed_five : (∃ n, Halt (orbit ⟨0,5⟩ n)) ↔ ∃ i, AReach 10 (T i) :=
  raw_target_iff (s:=⟨0,5⟩) (by unfold Stable; decide)

theorem seed_six : (∃ n, Halt (orbit ⟨0,6⟩ n)) ↔ ∃ i, AReach 11 (T i) :=
  raw_target_iff (s:=⟨0,6⟩) (by unfold Stable; decide)

theorem areach_prepend {s t u : Nat} (e : Arc s t) (h : AReach t u) : AReach s u := by
  induction h with
  | refl => exact .tail .refl e
  | tail _ e' ih => exact .tail ih e'

theorem strip_first {s t u : Nat} (e : Arc s t) (h : AReach s u) : u=s ∨ AReach t u := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ e' ih =>
    rcases ih with he|hr
    · subst_vars
      have he:=arc_functional e e'
      subst_vars
      exact Or.inr .refl
    · exact Or.inr (.tail hr e')

theorem t_ge4 (i : Nat) : 4≤T i := by
  have h:=t_add i
  have hp:=p_ge i
  unfold P at hp
  omega

theorem t_succ_ge13 (i : Nat) : 13≤T (i+1) := by
  have h:=t_add (i+1)
  have hp:=p_ge i
  rw [Nat.pow_succ] at h
  unfold P at hp
  omega

theorem t_ne5 (i : Nat) : T i≠5 := by
  cases i with
  | zero => decide
  | succ i => have := t_succ_ge13 i; omega

theorem root_two_arc : Arc 2 8 := by
  exact Arc.regular 0 0 (by decide)

theorem root_three_arc : Arc 3 11 := by
  exact Arc.regular 0 1 (by decide)

theorem root_five_arc : Arc 5 10 := Arc.special 0

theorem seed_three_root : (∃ n, Halt (orbit ⟨0,3⟩ n)) ↔ ∃ i, AReach 2 (T i) := by
  rw [seed_three]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨i,areach_prepend root_two_arc hi⟩
  · rintro ⟨i,hi⟩
    have hp:=t_ge4 i
    exact ⟨i,(strip_first root_two_arc hi).resolve_left (by omega)⟩

theorem seed_five_root : (∃ n, Halt (orbit ⟨0,5⟩ n)) ↔ ∃ i, AReach 1 (T i) := by
  rw [seed_five]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨i,areach_prepend .one (areach_prepend root_five_arc hi)⟩
  · rintro ⟨i,hi⟩
    have hp:=t_ge4 i
    have hr := (strip_first Arc.one hi).resolve_left (by omega)
    exact ⟨i,(strip_first root_five_arc hr).resolve_left (t_ne5 i)⟩

theorem seed_six_root : (∃ n, Halt (orbit ⟨0,6⟩ n)) ↔ ∃ i, AReach 3 (T i) := by
  rw [seed_six]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨i,areach_prepend root_three_arc hi⟩
  · rintro ⟨i,hi⟩
    have hp:=t_ge4 i
    exact ⟨i,(strip_first root_three_arc hi).resolve_left (by omega)⟩

#print axioms seed_three_root
#print axioms seed_five_root
#print axioms seed_six_root

#print axioms raw_target_iff
#print axioms seed_three
#print axioms seed_five
#print axioms seed_six

#print axioms halt_iff
end CapSieve.Bmo
