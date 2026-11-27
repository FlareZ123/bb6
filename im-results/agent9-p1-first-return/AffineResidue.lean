import P1CarryWideSource
namespace BB6.Agent9AffineResidue
open BB6.P1CarryExtinction

/-- One residue class for a weighted word: expr r xs = 1 + 2^k*a,
and B = 1 + bitMass 1 xs is the odd slope in the parameter n. -/
structure Node where
  r : Nat
  a : Nat
  B : Nat
  deriving DecidableEq, Repr

/-- The next selected bit fixes exactly one high bit of the parameter.
No modular inverse or search over parameter residues is needed. -/
def advance (k : Nat) (p : Node) (b : Bool) : Node :=
  let C := p.a + (if b then p.r+3+k else 0)
  let S := p.B + (if b then 2^k else 0)
  let t := C%2
  ⟨p.r+2^k*t,(C+t*S)/2,S⟩

def Rep (k : Nat) (xs : List Bool) (p : Node) : Prop :=
  xs.length+1=k ∧ p.r<2^k ∧ expr p.r xs=1+2^k*p.a ∧ p.B=1+bitMass 1 xs

theorem bitMass_snoc (j : Nat) (xs : List Bool) (b : Bool) :
    bitMass j (xs++[b])=bitMass j xs+(if b then 2^(j+xs.length) else 0) := by
  induction xs generalizing j with
  | nil => simp [bitMass]
  | cons a as ih =>
    simp only [List.cons_append,bitMass,ih,List.length_cons]
    rw [show j+1+as.length=j+(as.length+1) by omega]
    omega

theorem advance_rep (k : Nat) (xs : List Bool) (p : Node) (b : Bool)
    (h : Rep k xs p) : Rep (k+1) (xs++[b]) (advance k p b) := by
  rcases h with ⟨hlen,hr,hex,hB⟩
  let C := p.a+(if b then p.r+3+k else 0)
  let S := p.B+(if b then 2^k else 0)
  let t := C%2
  have hS : S=1+bitMass 1 (xs++[b]) := by
    rw [bitMass_snoc,show 1+xs.length=k by omega]
    simp [S,hB,Nat.add_comm,Nat.add_left_comm]
  have hodd : S%2=1 := by
    rw [hS]
    have he := bitMass_even 0 (xs++[b])
    change bitMass 1 (xs++[b])%2=0 at he
    omega
  have ht : t=0 ∨ t=1 := by dsimp [t]; omega
  have hpar : (C+t*S)%2=0 := by
    rw [Nat.add_mod,Nat.mul_mod,hodd]
    simp only [Nat.mul_one,Nat.mod_mod]
    change (t + t%2)%2=0
    omega
  have he : expr p.r (xs++[b])=1+2^k*C := by
    rw [expr_snoc,show 1+xs.length=k by omega,hex]
    cases b <;> simp [C,weight,Nat.mul_add,Nat.mul_comm,Nat.add_assoc]
  unfold Rep advance
  change (xs++[b]).length+1=k+1 ∧ p.r+2^k*t<2^(k+1) ∧
    expr (p.r+2^k*t) (xs++[b])=1+2^(k+1)*((C+t*S)/2) ∧ S=1+bitMass 1 (xs++[b])
  refine ⟨by simp; omega, ?_, ?_, hS⟩
  · rw [Nat.pow_succ]
    rcases ht with h0|h1
    · simp [h0]; omega
    · simp [h1]; omega
  · rw [expr_shift,he,←hS,Nat.pow_succ]
    have hhalf : C+t*S=2*((C+t*S)/2) := by omega
    calc
      _ = 1+2^k*(C+t*S) := by simp only [Nat.mul_add]; ac_rfl
      _ = _ := by
        calc
          _ = 1+2^k*(2*((C+t*S)/2)) := congrArg (fun x : Nat => 1+2^k*x) hhalf
          _ = _ := by ac_rfl

def nodes : Nat → List Node
  | 0 => [⟨0,1,1⟩]
  | d+1 => (nodes d).flatMap fun p => [advance (d+1) p false,advance (d+1) p true]

theorem nodes_sound (d : Nat) (p : Node) (hp : p∈nodes d) :
    ∃ xs : List Bool, Rep (d+1) xs p := by
  induction d generalizing p with
  | zero => simp [nodes] at hp; subst p; exact ⟨[],by simp [Rep,expr,absSum,bitMass]⟩
  | succ d ih =>
    simp only [nodes,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at hp
    obtain ⟨q,hq,hp⟩ := hp
    obtain ⟨xs,hxs⟩ := ih q hq
    rcases hp with rfl|rfl
    · exact ⟨xs++[false],advance_rep _ _ _ _ hxs⟩
    · exact ⟨xs++[true],advance_rep _ _ _ _ hxs⟩

theorem nodes_complete (d : Nat) (xs : List Bool) (h : xs.length=d) :
    ∃ p ∈ nodes d, Rep (d+1) xs p := by
  induction d generalizing xs with
  | zero =>
    have hx : xs=[] := List.length_eq_zero_iff.mp h
    subst xs
    exact ⟨⟨0,1,1⟩,by simp [nodes],by simp [Rep,expr,absSum,bitMass]⟩
  | succ d ih =>
    rcases List.eq_nil_or_concat xs with rfl|⟨ys,b,rfl⟩
    · simp at h
    · rw [List.concat_eq_append] at h ⊢
      have hy : ys.length=d := by simpa using h
      obtain ⟨p,hp,hr⟩ := ih ys hy
      refine ⟨advance (d+1) p b,?_,advance_rep _ _ _ _ hr⟩
      simp only [nodes,List.mem_flatMap]
      refine ⟨p,hp,?_⟩
      cases b <;> simp

theorem odd_mul_dvd (k x B : Nat) (hB : B%2=1) (h : 2^k ∣ x*B) : 2^k ∣ x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have he : 2 ∣ x*B := Nat.dvd_trans (Nat.pow_dvd_pow 2 (show 1≤k+1 by omega)) h
    have hx := Nat.dvd_iff_mod_eq_zero.mp he
    rw [Nat.mul_mod,hB,Nat.mul_one,Nat.mod_mod] at hx
    have hx' : x=2*(x/2) := by omega
    rw [hx',Nat.mul_assoc,Nat.pow_succ,Nat.mul_comm (2^k) 2] at h
    have hs := ih (x/2) (Nat.dvd_of_mul_dvd_mul_left (by decide : 0<2) h)
    obtain ⟨y,hy⟩ := hs
    rw [hx',hy,Nat.pow_succ]
    exact ⟨y,by ac_rfl⟩

theorem residue_diff (k n p : Nat) (xs : List Bool) (hk : 0<k)
    (ha : expr n xs % 2^k=1) (hb : expr (n+p) xs % 2^k=1) : 2^k ∣ p := by
  have hB : (1+bitMass 1 xs)%2=1 := by
    have h := bitMass_even 0 xs
    change bitMass 1 xs%2=0 at h
    omega
  apply odd_mul_dvd k p (1+bitMass 1 xs) hB
  rw [expr_shift,Nat.add_mod,ha] at hb
  have hM : 1<2^k := Nat.one_lt_two_pow (by omega)
  let r := p*(1+bitMass 1 xs)%2^k
  have hr : r<2^k := Nat.mod_lt _ (Nat.two_pow_pos _)
  change (1+r)%2^k=1 at hb
  apply Nat.dvd_iff_mod_eq_zero.mpr
  change r=0
  by_cases hlt : 1+r<2^k
  · rw [Nat.mod_eq_of_lt hlt] at hb; omega
  · have he : 1+r=2^k := by omega
    rw [he,Nat.mod_self] at hb; omega

theorem rep_unique (k n : Nat) (xs : List Bool) (p : Node)
    (h : Rep k xs p) (hn : expr n xs%2^k=1) : n%2^k=p.r := by
  rcases h with ⟨hlen,hr,hex,hB⟩
  have hk : 0<k := by omega
  have hM : 1<2^k := Nat.one_lt_two_pow (by omega)
  have hp : expr p.r xs%2^k=1 := by
    rw [hex,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hM]
  let r := n%2^k
  have hnr : n=r+2^k*(n/2^k) := (Nat.mod_add_div n _).symm
  have hn' : expr r xs%2^k=1 := by
    rw [hnr,expr_shift] at hn
    rw [show 2^k*(n/2^k)*(1+bitMass 1 xs)=2^k*((n/2^k)*(1+bitMass 1 xs)) by ac_rfl,Nat.add_mul_mod_self_left] at hn
    exact hn
  have hr' : r<2^k := Nat.mod_lt _ (Nat.two_pow_pos _)
  change r=p.r
  by_cases hle : p.r≤r
  · have he : r=p.r+(r-p.r) := by omega
    have hd := residue_diff k p.r (r-p.r) xs hk hp (by rwa [←he])
    have hz := Nat.eq_zero_of_dvd_of_lt hd (by omega : r-p.r<2^k)
    omega
  · have he : p.r=r+(p.r-r) := by omega
    have hd := residue_diff k r (p.r-r) xs hk hn' (by rwa [←he])
    have hz := Nat.eq_zero_of_dvd_of_lt hd (by omega : p.r-r<2^k)
    omega

/-- Exact support, not only a necessary condition. The list retains
word multiplicity. Each word is represented by its unique residue. -/
theorem width_pos_iff_nodes (d n : Nat) : 0<width (d+1) n ↔ ∃ p∈nodes d, p.r=n%2^(d+1) := by
  rw [width_pos_iff _ _ (by omega)]
  constructor
  · rintro ⟨xs,hx,he⟩
    obtain ⟨p,hp,hr⟩ := nodes_complete d xs (by omega)
    exact ⟨p,hp,(rep_unique _ _ _ _ hr he).symm⟩
  · rintro ⟨p,hp,he⟩
    obtain ⟨xs,hlen,hr,hex,hB⟩ := nodes_sound d p hp
    refine ⟨xs,hlen,?_⟩
    have hM : 1<2^(d+1) := Nat.one_lt_two_pow (by omega)
    have hp' : expr p.r xs%2^(d+1)=1 := by rw [hex,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hM]
    have hnr : n=p.r+2^(d+1)*(n/2^(d+1)) := by rw [he]; exact (Nat.mod_add_div n _).symm
    rw [hnr,expr_shift,show 2^(d+1)*(n/2^(d+1))*(1+bitMass 1 xs)=2^(d+1)*((n/2^(d+1))*(1+bitMass 1 xs)) by ac_rfl,Nat.add_mul_mod_self_left]
    exact hp'

#print axioms advance_rep
#print axioms rep_unique
#print axioms width_pos_iff_nodes
end BB6.Agent9AffineResidue
