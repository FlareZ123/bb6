import CLine
import DirectQuotientBarrier

namespace BB6.Agent19DirectBarrier
set_option maxRecDepth 4096

abbrev State := Nat × Nat × Nat

def Closed (J : State → Prop) : Prop :=
  ∀ s t, J s → BB6CLine.nextC s=some t → J t

def secPred (J : State → Prop) (a k : Nat) : Prop := J (a,k,0)

def run : Nat → Option State
  | 0 => some (5,0,1)
  | n+1 => (run n).bind BB6CLine.nextC

private theorem run_reach (n : Nat) (s : State) (h : run n=some s) : BB6CLine.Reach s := by
  induction n generalizing s with
  | zero => simp [run] at h; subst s; exact BB6CLine.Reach.init
  | succ n ih =>
    change (run n).bind BB6CLine.nextC=some s at h
    cases he : run n with
    | none => simp [he] at h
    | some t => exact BB6CLine.Reach.next t s (ih t he) (by simpa [he] using h)

theorem seed12 : BB6CLine.Reach (12,10,0) := run_reach 37 _ (by decide)
theorem seed17 : BB6CLine.Reach (17,11,0) := run_reach 59 _ (by decide)
theorem seed18 : BB6CLine.Reach (18,16,0) := run_reach 95 _ (by decide)
theorem seed23 : BB6CLine.Reach (23,17,0) := run_reach 129 _ (by decide)

theorem accepted_reach (J : State → Prop) (hj : J (5,0,1)) (hc : Closed J)
    (s : State) (h : BB6CLine.Reach s) : J s := by
  induction h with
  | init => exact hj
  | next s t _ ht ih => exact hc s t ih ht

private theorem countdown (J : State → Prop) (hc : Closed J) (n a k : Nat)
    (h : J (a+n,k,n+3)) : J (a,k+n,3) := by
  induction n generalizing k with
  | zero => simpa using h
  | succ n ih =>
    have hs : BB6CLine.nextC (a+n+1,k,n+4)=some (a+n,k+1,n+3) := rfl
    have h' : J (a+n,k+1,n+3) := hc _ _ (by simpa [Nat.add_assoc] using h) hs
    have ht := ih (k+1) h'
    simpa [Nat.add_assoc,Nat.add_comm 1 n] using ht

/-- The direct section return is a finite sequence of genuine CLine steps,
    valid at every sufficiently large representative. -/
theorem source_direct_closed (J : State → Prop) (hc : Closed J) : DirectClosed (secPred J) := by
  intro a k hk ha h
  unfold secPred at h ⊢
  have hA : a=(a-2)+2 := by omega
  have hs : BB6CLine.nextC (a,k,0)=some (a-2,1,2*k+1) := by
    conv => lhs; rw [hA]
    rfl
  have h0 := hc _ _ h hs
  let n := 2*k-2
  have he1 : a-2=(a-2*k)+n := by dsimp [n]; omega
  have he2 : 2*k+1=n+3 := by dsimp [n]; omega
  rw [he1,he2] at h0
  have h1 := countdown J hc n (a-2*k) 1 h0
  have h2 := hc (a-2*k,1+n,3) (a-2*k,1+n+2,1) h1 (by rfl)
  have h3 := hc (a-2*k,1+n+2,1) (a-2*k,1+n+2+1,0) h2 (by rfl)
  have he : 1+n+2+1=2*k+2 := by dsimp [n]; omega
  simpa [he] using h3

/-- Any invariant of the original accelerated source that identifies large
    section representatives modulo 2^p is forced to include the entire
    right=-2 strip, independently of how its other coordinates are tracked. -/
theorem source_direct_tail_forced (p : Nat) (hp : 2≤p) (J : State → Prop)
    (hj : J (5,0,1)) (hc : Closed J) (hcon : Congruent (2^p) (secPred J))
    (a k : Nat) (ha : 8≤a) (hk : 8≤k) (hK : 2^p∣k+2) : J (a,k,0) := by
  have hs : Seeds (secPred J) := ⟨accepted_reach J hj hc _ seed12,accepted_reach J hj hc _ seed17,
      accepted_reach J hj hc _ seed18,accepted_reach J hj hc _ seed23⟩
  exact direct_tail_forced p hp (secPred J) hcon (source_direct_closed J hc) hs a k ha hk hK

private theorem countdown_left (J : State → Prop) (hc : Closed J) (n k c : Nat)
    (h : J (n,k,c+n+4)) : J (0,k+n,c+4) := by
  induction n generalizing k with
  | zero => simpa using h
  | succ n ih =>
    have he : c+(n+1)+4=(c+n+1)+4 := by omega
    have hs' : BB6CLine.nextC (n+1,k,c+(n+1)+4)=some (n,k+1,c+n+4) := by
      rw [he]
      change BB6CLine.nextC (n+1,k,(c+n+1)+4)=some (n,k+1,c+n+4)
      have he' : c+n+1+3=c+n+4 := by omega
      rw [←he']
      rfl
    have h' := hc _ _ h hs'
    have ht := ih (k+1) h'
    simpa [Nat.add_assoc,Nat.add_comm 1 n] using ht

/-- Exact one-bounce (cost two) high section return on a large cone. -/
theorem source_high2_closed (J : State → Prop) (hc : Closed J) (a k : Nat)
    (ha : 8≤a) (hk : 8≤k) (h1 : a+8≤2*k) (h2 : 2*k+8≤3*a)
    (h : J (a,k,0)) :
    J (3*a-2*k+1+2*(a%2),2*k-a+3-a%2,0) := by
  have hA : a=(a-2)+2 := by omega
  have hs : BB6CLine.nextC (a,k,0)=some (a-2,1,2*k+1) := by
    conv => lhs; rw [hA]
    rfl
  have h0 := hc _ _ h hs
  let c := 2*k-a-1
  have he : 2*k+1=c+(a-2)+4 := by dsimp [c]; omega
  rw [he] at h0
  have hz := countdown_left J hc (a-2) 1 c h0
  have hm : 1+(a-2)=a-1 := by omega
  rw [hm] at hz
  by_cases hp : a%2=0
  · have hp' : (a-1)%2=1 := by omega
    have hb : 4*((a-1)/2)+5=2*a+1 := by omega
    have hs' : BB6CLine.nextC (0,a-1,c+4)=some (2*a+1,0,c+4) := by
      simp only [BB6CLine.nextC,show ¬(a-1)%2=0 by omega,ite_false,hb]
    have hr := hc _ _ hz hs'
    let n := 2*k-a
    have he1 : 2*a+1=(3*a-2*k+1)+n := by dsimp [n]; omega
    have he2 : c+4=n+3 := by dsimp [c,n]; omega
    rw [he1,he2] at hr
    have h3 := countdown J hc n (3*a-2*k+1) 0 hr
    have h4 := hc _ _ h3 (show BB6CLine.nextC (3*a-2*k+1,0+n,3)=some (3*a-2*k+1,0+n+2,1) by rfl)
    have h5 := hc _ _ h4 (show BB6CLine.nextC (3*a-2*k+1,0+n+2,1)=some (3*a-2*k+1,0+n+2+1,0) by rfl)
    have hh : 0+n+2+1=2*k-a+3 := by dsimp [n]; omega
    simpa [hp,hh] using h5
  · have hp' : (a-1)%2=0 := by omega
    have hb : 4*((a-1)/2)+2=2*a := by omega
    have hs' : BB6CLine.nextC (0,a-1,c+4)=some (2*a,2,c+1) := by
      simp only [BB6CLine.nextC,hp',ite_true,hb]
    have hr := hc _ _ hz hs'
    let n := 2*k-a-3
    have he1 : 2*a=(3*a-2*k+3)+n := by dsimp [n]; omega
    have he2 : c+1=n+3 := by dsimp [c,n]; omega
    rw [he1,he2] at hr
    have h3 := countdown J hc n (3*a-2*k+3) 2 hr
    have h4 := hc _ _ h3 (show BB6CLine.nextC (3*a-2*k+3,2+n,3)=some (3*a-2*k+3,2+n+2,1) by rfl)
    have h5 := hc _ _ h4 (show BB6CLine.nextC (3*a-2*k+3,2+n+2,1)=some (3*a-2*k+3,2+n+2+1,0) by rfl)
    have hh : 2+n+2+1=2*k-a+2 := by dsimp [n]; omega
    have hp1 : a%2=1 := by omega
    rw [hh] at h5
    simpa [hp1] using h5

#print axioms source_high2_closed

#print axioms seed12
#print axioms seed17
#print axioms seed18
#print axioms seed23
#print axioms source_direct_closed
#print axioms source_direct_tail_forced
end BB6.Agent19DirectBarrier
