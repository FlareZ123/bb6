import ZeroTwoEndpoint
import BB429Even16
import Lean.Elab.Tactic.Omega

namespace BB429.ZeroTwoRootCover
open ZeroTwoSpine ZeroTwoEndpoint
set_option maxHeartbeats 10000000

def Rooted (q : State) : Prop := ∃ n, run n (0,0)=some q

private theorem rooted_pred (q : State) (ha : 0<q.1) (hr : Rooted q) :
    ∃ p, Rooted p ∧ next p=some q := by
  obtain ⟨n,hn⟩ := hr
  cases n with
  | zero =>
    simp [run] at hn
    subst q
    omega
  | succ n =>
    simp only [run] at hn
    cases hp : run n (0,0) with
    | none => simp [hp] at hn
    | some p =>
      simp only [hp,Option.bind_some] at hn
      exact ⟨p,⟨n,hp⟩,hn⟩

private theorem odd_inverse (p q : State) (ha : 13≤q.1) (ho : q.1%2=1)
    (hs : next p=some q) :
    (q.1=2*p.1+3 ∧ p.2=q.1+q.2) ∨
    (4*p.1+26=4*q.1+q.2 ∧ 2*p.2=q.2+4 ∧ q.2%4=2) := by
  obtain ⟨u,w⟩ := p
  obtain ⟨a,b⟩ := q
  simp only [next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

def upper (k c : Nat) : State := (2^k*c-3,2*(2^k*c-3)+2)

private theorem a_large_odd (k c i : Nat) (hc : 9≤c) (hi : i<k) :
    13≤(back i (upper k c)).1 ∧ (back i (upper k c)).1%2=1 := by
  have h := (burst k c (upper k c).2 i (by omega) (by omega)).1
  change (back i (upper k c)).1=2^(k-i)*c-3 at h
  rw [h,show k-i=(k-i-1)+1 by omega,Nat.pow_succ,Nat.mul_right_comm]
  have hp : c≤2^(k-i-1)*c := Nat.le_mul_of_pos_left c (Nat.pow_pos (by decide))
  omega

private theorem b_phase (k c i : Nat) (hc : 9≤c) (hi : i<k) :
    (back i (upper k c)).2%4=i%4 := by
  let q := back i (upper k c)
  have h := (burst k c (upper k c).2 i (by omega) (by omega)).2
  change rank q+3*i=rank (upper k c) at h
  have ho := (a_large_odd k c i hc hi).2
  change q.1%2=1 at ho
  have hu : rank (upper k c)=4*(upper k c).1+2 := by simp [rank,upper]; omega
  rw [hu] at h
  simp only [rank] at h
  change q.2%4=i%4
  omega

/-- A side exit from the full F burst has a genuine rooted S parent,
    an index congruent to 2 modulo 4, and its exact gap identity. -/
def SideExit (k c : Nat) : Prop :=
  ∃ i<k, ∃ p : State,
    Rooted p ∧ next p=some (back i (upper k c)) ∧
    i%4=2 ∧ 4*p.1+26=4*(back i (upper k c)).1+(back i (upper k c)).2 ∧
    2*p.2=(back i (upper k c)).2+4 ∧
    2*p.1+21=p.2+2*(2^(k-i)*c)

/-- Exact backward grammar collapses an arbitrary F burst: either some
    genuine S side parent is rooted, or the full F endpoint is rooted. -/
theorem root_split (k c : Nat) (hc : 9≤c) (hr : Rooted (upper k c)) :
    Rooted (back k (upper k c)) ∨ SideExit k c := by
  classical
  by_cases hs : SideExit k c
  · exact Or.inr hs
  left
  have hall : ∀ i≤k, Rooted (back i (upper k c)) := by
    intro i hi
    induction i with
    | zero => simpa [back] using hr
    | succ i ih =>
      let q := back i (upper k c)
      have hrq : Rooted q := ih (by omega)
      obtain ⟨ha,ho⟩ := a_large_odd k c i hc (by omega)
      change 13≤q.1 at ha
      change q.1%2=1 at ho
      obtain ⟨p,hpr,hps⟩ := rooted_pred q (by omega) hrq
      rcases odd_inverse p q ha ho hps with hF|hS
      · obtain ⟨h1,h2⟩ := hF
        have heq : p=backStep q := by
          apply Prod.ext
          · change p.1=(q.1-3)/2
            omega
          · change p.2=q.1+q.2
            omega
        change Rooted (backStep q)
        rw [← heq]
        exact hpr
      · obtain ⟨h1,h2,h3⟩ := hS
        have hb := b_phase k c i hc (by omega)
        change q.2%4=i%4 at hb
        have hp := (burst k c (upper k c).2 i (by omega) (by omega)).1
        change q.1=2^(k-i)*c-3 at hp
        have hg : 2*p.1+21=p.2+2*(2^(k-i)*c) := by omega
        exfalso
        exact hs ⟨i,by omega,p,hpr,hps,by omega,h1,h2,hg⟩
  exact hall k (by omega)

/-- The all-F endpoint's even row is from the authentic blank-root
    invariant; no copied sieve soundness assumption is used. -/
theorem rooted_endpoint_classes (k c : Nat) (hk : 4≤k) (hc : 9≤c) (ho : c%2=1)
    (hr : Rooted (back k (upper k c))) :
    (k%16=0 ∧ c%8=1) ∨ (k%16=4 ∧ c%8=7) ∨
    (k%16=8 ∧ c%8=5) ∨ (k%16=12 ∧ c%8=3) := by
  let q := back k (upper k c)
  have h := (burst k c (upper k c).2 k (by omega) (by omega)).1
  change q.1=2^(k-k)*c-3 at h
  simp only [Nat.sub_self,Nat.pow_zero,Nat.one_mul] at h
  obtain ⟨n,hn⟩ := hr
  change run n (0,0)=some q at hn
  have hpair : q=(q.1,q.2) := Prod.ext rfl rfl
  rw [hpair] at hn
  have heven : q.1%2=0 := by omega
  have he := BB429Even16.rooted_even_sixteen n q.1 q.2 hn (by omega) heven
  have hfilter : necessary q.1 q.2 := by
    unfold necessary
    simp only [heven,ite_true]
    constructor
    · split <;> omega
    · omega
  exact endpoint_necessary k c hk (by omega) ho hfilter

/-- Complete all-parameter upper-boundary ancestry reduction.  The
    surviving side exits remain obligations, not reachability claims. -/
theorem upper_root_cover (k c : Nat) (hk : 4≤k) (hc : 9≤c) (ho : c%2=1)
    (hr : Rooted (upper k c)) :
    SideExit k c ∨ ((k%16=0 ∧ c%8=1) ∨ (k%16=4 ∧ c%8=7) ∨
    (k%16=8 ∧ c%8=5) ∨ (k%16=12 ∧ c%8=3)) := by
  rcases root_split k c hc hr with h|h
  · exact Or.inr (rooted_endpoint_classes k c hk hc ho h)
  · exact Or.inl h

#print axioms root_split
#print axioms rooted_endpoint_classes
#print axioms upper_root_cover
end BB429.ZeroTwoRootCover
