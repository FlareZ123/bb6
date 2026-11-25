import C1ZeroLAFour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent6C1ZeroLACore
open BB6Coverage BB6Coverage.Agent31Pump
open BB6.Agent6C1ZeroLAFour (P Q T L0 h f z u as bs cs rep_add z_add shift)

structure Core (p : PartialMachine) where
  q : Fin 6
  sc : Nat
  st : Nat
  start : ∀ R : List Bool, run0 p st ⟨4,h,f++R⟩ = some ⟨q,L0,R⟩
  scan : ∀ L R : List Bool, run0 p sc ⟨q,L0++L,T++R⟩ = some ⟨q,L0++P++L,R⟩
  pop : ∀ L R : List Bool, run0 p 5 ⟨4,P++L,f++R⟩ = some ⟨4,L,f++Q++R⟩
  finish : ∀ R : List Bool, run0 p 2 ⟨4,P,f++R⟩ = some ⟨4,h,z 3++R⟩

theorem sweep {p : PartialMachine} (c : Core p) (n : Nat) (L R : List Bool) :
    run0 p (c.sc*n) ⟨c.q,L0++L,cs n++R⟩ = some ⟨c.q,L0++as n++L,R⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have H := join0 (c.scan L (cs n++R)) (ih (P++L))
    have hc : c.sc+c.sc*n=c.sc*(n+1) := by rw [Nat.mul_succ,Nat.add_comm]
    rw [hc] at H
    have hp : as (n+1)=as n++P := by change rep P (n+1)=rep P n++rep P 1; rw [rep_add]
    rw [hp]
    simpa only [cs,rep,List.append_assoc] using H

theorem unwind {p : PartialMachine} (c : Core p) (n : Nat) (L R : List Bool) :
    run0 p (5*n) ⟨4,as n++L,f++R⟩ = some ⟨4,L,f++bs n++R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have H := join0 (c.pop (as n++L) R) (ih (Q++R))
    rw [show 5+5*n=5*(n+1) by omega] at H
    have hq : bs (n+1)=bs n++Q := by change rep Q (n+1)=rep Q n++rep Q 1; rw [rep_add]
    rw [hq]
    simpa only [as,rep,List.append_assoc] using H

def cfg (n : Nat) (S : List Bool) : Z0 := ⟨4,h,z 3++bs n++S⟩
def cost {p : PartialMachine} (c : Core p) (n k : Nat) := c.st+c.sc*n+k+5*n+2

theorem step {p : PartialMachine} (c : Core p) (n k : Nat) (S U : List Bool)
    (term : ∀ L : List Bool, run0 p k ⟨c.q,L0++L,z 2++S⟩ = some ⟨4,P++L,f++U⟩) :
    run0 p (cost c n k) (cfg n S) = some (cfg n U) := by
  have H1 := c.start (z 2++bs n++S)
  rw [shift] at H1
  have H2 := sweep c n [] (z 2++S)
  have H3 := term (as n)
  have H4 := unwind c n P U
  have H5 := c.finish (bs n++U)
  have H := join0 H1 (by simpa only [List.append_assoc,List.append_nil] using H2)
  have hp : as n++P=P++as n := by change rep P n++rep P 1=rep P 1++rep P n; rw [←rep_add,←rep_add,Nat.add_comm]
  rw [←hp] at H3
  have H := join0 H (by simpa only [List.append_assoc] using H3)
  have H := join0 H (by simpa only [List.append_assoc] using H4)
  have H := join0 H (by simpa only [List.append_assoc] using H5)
  have he : z 3++bs n++S=f++(cs n++z 2++S) := by
    calc
      z 3++bs n++S = f++(z 2++bs n++S) := by simp only [←List.append_assoc]; rfl
      _ = _ := by rw [shift]
  unfold cfg cost
  rw [he]
  simpa only [List.append_assoc] using H

theorem cfg_add (n k : Nat) (S : List Bool) : cfg n (bs k++S) = cfg (n+k) S := by
  unfold cfg bs
  rw [rep_add]
  simp only [List.append_assoc]

end BB6.Agent6C1ZeroLACore
