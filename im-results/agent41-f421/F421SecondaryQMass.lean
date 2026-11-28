import F421SecondaryConservation

namespace F421SecondaryLifetimes
open F421TertiaryGuard
open BB6Coverage.Agent41F421.EpochWords

def qSum (cs : List PC) : Nat := (cs.map Cell.q).sum

def qBudgetSum (B : Nat) : List PC → Nat
  | [] => 0
  | _::cs => B+qBudgetSum (2*B) cs

theorem qBudgetPow (B : Nat) (cs : List PC) :
    qBudgetSum B cs+B=B*2^cs.length := by
  induction cs generalizing B with
  | nil => simp [qBudgetSum]
  | cons c cs ih =>
    have h:=ih (2*B)
    simp only [qBudgetSum,List.length_cons,Nat.pow_succ]
    calc
      B+qBudgetSum (2*B) cs+B = qBudgetSum (2*B) cs+(2*B) := by omega
      _ = 2*B*2^cs.length := h
      _ = B*(2^cs.length*2) := by ac_rfl

/-- Aggregate Q-survival+terminal carry identity, independent of deletion
    positions and independent of incoming Q entries. -/
theorem drainQmass (B carry : Nat) (cs : List PC)
    (hB : 0<B) (hp : capP B (pProjection cs)) :
    let (as,A,r) := drain (B-1) carry (dec cs)
    qSum as+r = carry+qSum cs+qBudgetSum B cs := by
  induction cs generalizing B carry with
  | nil =>
    simp [dec,drain,qSum,qBudgetSum]
  | cons c cs ih =>
    have ht : capP (2*B) (pProjection cs) := hp.2
    have hn : 0<2*B := by omega
    have hcap : 2*(B-1)+1=2*B-1 := by omega
    have hlow : 2*B≤c.p := by rcases hp.1 with h|h; omega; omega
    rcases hp.1 with h|h
    · have hle : c.p-1≤2*(B-1)+1 := by omega
      have hcarry : carry+c.q+(c.p-1+1)/2=carry+c.q+B := by omega
      have h := ih (2*B) (carry+c.q+B) hn ht
      rcases hd : drain (2*B-1) (carry+c.q+B) (dec cs) with ⟨as,A,r⟩
      rw [hd] at h
      have hle' : c.p-1≤2*B-1 := by omega
      have hstep : B-1+(c.p-1+1)/2=2*B-1 := by omega
      simp only [dec,List.map_cons,drain,hcap,ite_eq_left hle',hstep,hcarry, qSum,qBudgetSum,List.sum_cons]
      rw [show (List.map (fun c : PC => ⟨c.p-1,c.q⟩) cs) = dec cs from rfl, hd]
      simp only [Prod.fst,Prod.snd]
      simpa only [qSum,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    · have hnot : ¬c.p-1≤2*(B-1)+1 := by omega
      have hq : c.q+(B-1)+1+carry=c.q+B+carry := by omega
      have h := ih (2*B) 0 hn ht
      rcases hd : drain (2*B-1) 0 (dec cs) with ⟨as,A,r⟩
      rw [hd] at h
      have hnot' : ¬c.p-1≤2*B-1 := by omega
      simp only [dec,List.map_cons,drain,hcap,ite_eq_right hnot',qSum,qBudgetSum,List.sum_cons]
      rw [show (List.map (fun c : PC => ⟨c.p-1,c.q⟩) cs) = dec cs from rfl, hd]
      change (c.q+(B-1)+1+carry)+qSum as+r=
        carry+(c.q+qSum cs)+(B+qBudgetSum (2*B) cs)
      rw [hq]
      omega

#print axioms qBudgetPow
#print axioms drainQmass
end F421SecondaryLifetimes
