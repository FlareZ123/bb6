import EvenQuarter
namespace BB6.Agent1

private theorem large_step (a c:Nat) (ha:a%2=0) (hlarge:a+10≤c) :
    T a c=some (a+3,c-2) ∧ T (a+3) (c-2)=some (2*a+12,c-a-10) := by
  have h0:c≠0:=by omega
  have h1:c≠1:=by omega
  have h2:c-2≠0:=by omega
  have h3:c-2≠1:=by omega
  have h4:c-2≠2:=by omega
  have h5:c-2≠3:=by omega
  have hao:(a+3)%2≠0:=by omega
  have hbound:2*((a+3)/2+1)+2≤c-4:=by omega
  have hG:G ((a+3)/2+1) (c-4)=(2*a+12,c-a-10):=by
    rw [G]
    have hlow:¬c-4<2*((a+3)/2+1):=by omega
    have hmid:¬c-4≤2*((a+3)/2+1)+1:=by omega
    simp only [hlow,dite_false,hmid,ite_false]
    apply Prod.ext <;> omega
  constructor
  · simp [T,h0,h1,ha]
  · simp [T,h2,h3,hao,h4,h5,show c-2-2=c-4 by omega,hG]

private def near : Nat → Nat → Nat
 | _, 0 => 2
 | a, n+1 => a+10+near (2*a+12) n

private theorem near_closed (a n:Nat) :
    near a n + 2*n = (a+12)*(2^n-1)+2 := by
  induction n generalizing a with
  | zero => simp [near]
  | succ n ih =>
    have hpos : 1≤2^n := by
      have hp : 0<2^n:=Nat.pow_pos (by decide)
      omega
    have hpow : 2^(n+1)-1=2*(2^n-1)+1 := by
      rw [Nat.pow_succ]
      omega
    have hh:=ih (2*a+12)
    have hmul : (a+12)*(2*(2^n-1)+1)=(2*a+24)*(2^n-1)+(a+12):=by
      have hcoef:(a+12)*2=2*a+24:=by omega
      calc
        (a+12)*(2*(2^n-1)+1) = ((a+12)*2)*(2^n-1)+(a+12) := by
          rw [Nat.mul_add]
          simp only [Nat.mul_one]
          rw [Nat.mul_assoc]
        _ = (2*a+24)*(2^n-1)+(a+12) := by rw [hcoef]
    have hh' : near (2*a+12) n +2*n = (2*a+24)*(2^n-1)+2 := by
      simpa only [show 2*a+12+12=2*a+24 by omega] using hh
    change a+10+near (2*a+12) n+2*(n+1) = (a+12)*(2^(n+1)-1)+2
    rw [hpow,hmul]
    omega

private theorem near_two_form (n:Nat) : near 2 n=14*2^n-2*n-12 := by
  have h1:=near_closed 2 n
  have hp : 1≤2^n:= by
    have h:0<2^n:=Nat.pow_pos (by decide)
    omega
  omega

/-- Genuine high-branch two-step paths ending with the even c=2 boundary. -/
inductive EvenRoute : Nat → Nat → Nat → Nat → Prop where
 | zero (a:Nat) : EvenRoute 0 a 2 a
 | grow (n a c b:Nat) : T a c=some (a+3,c-2) →
     T (a+3) (c-2)=some (2*a+12,c-a-10) →
     EvenRoute n (2*a+12) (c-a-10) b → EvenRoute (n+1) a c b

theorem even_route_is_reachable (n a c b:Nat)
    (h:EvenRoute n a c b) (hr:Reach a c) : Reach b 2 := by
  induction h with
  | zero a => exact hr
  | grow n a c b hfirst hsecond hrec ih =>
      have hmid:Reach (a+3) (c-2):=Reach.next a c (a+3) (c-2) hr hfirst
      have hnext:Reach (2*a+12) (c-a-10):=
        Reach.next (a+3) (c-2) (2*a+12) (c-a-10) hmid hsecond
      exact ih hnext

theorem near_reaches_even_two (a n:Nat) (ha:a%2=0):
    ∃ b, b%2=0 ∧ EvenRoute n a (near a n) b := by
  induction n generalizing a with
  | zero => exact ⟨a,ha,EvenRoute.zero a⟩
  | succ n ih =>
      obtain ⟨b,hb,hroute⟩:=ih (2*a+12) (by omega)
      have hlarge:a+10≤near a (n+1):=by simp only [near];omega
      obtain ⟨h1,h2⟩:=large_step a (near a (n+1)) ha hlarge
      have hval:near a (n+1)-a-10=near (2*a+12) n:=by simp only [near];omega
      refine ⟨b,hb,?_⟩
      exact EvenRoute.grow n a (near a (n+1)) b h1 (by simpa only [hval] using h2)
        (by simpa only [hval] using hroute)

/-- An exact iff criterion for the existence of *any* reachable even-left
    c=2 hub, reducing the whole class to the single shifted-reset family. -/
theorem blank_even_two_iff_shifted_reset :
    (∃ b:Nat, b%2=0 ∧ Reach b 2) ↔
      (∃ n:Nat, Reach 2 (14*2^n-2*n-12)) := by
  constructor
  · rintro ⟨b,hb,hr⟩
    obtain ⟨j,s,hs,hpow,hmass⟩:=even_two_has_near_critical_reset b hr hb
    have hform:=near_two_form j
    have hsval:s=near 2 j:=by omega
    exact ⟨j,by simpa only [←hform,hsval] using hs⟩
  · rintro ⟨n,hr⟩
    have hform:=near_two_form n
    have hstart:Reach 2 (near 2 n):=by simpa only [hform] using hr
    obtain ⟨b,hb,hpath⟩:=near_reaches_even_two 2 n (by decide)
    exact ⟨b,hb,even_route_is_reachable n 2 (near 2 n) b hpath hstart⟩

#print axioms BB6.Agent1.blank_even_two_iff_shifted_reset
#print axioms BB6.Agent1.near_reaches_even_two
end BB6.Agent1
