import OneLCFast
import SweepPumping
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace BB6.Agent4E0OneLCLate
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent10ZipAudit BB6Coverage.Agent50Zipper BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot

def pack (w:List Bool) (t:Nat) : Nat := value w + 2^w.length*t
def repPack (w:List Bool) : Nat → Nat → Nat
  | 0,t => t
  | n+1,t => pack w (repPack w n t)
theorem value_surj (n:Nat) : ∃ l : List Bool, value l=n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn:n=0
    · exact ⟨[],hn.symm⟩
    · obtain ⟨l,hl⟩ := ih (n/2) (by omega)
      exact ⟨head n :: l, by simp only [value,hl,head_nat]; omega⟩
theorem value_append (w t:List Bool) : value (w++t) = pack w (value t) := by
  induction w with
  | nil => simp [pack,value]
  | cons b w ih =>
    rw [List.cons_append,value,ih]
    simp [pack,value,Nat.pow_succ,Nat.mul_add,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm,Nat.add_assoc]
theorem value_rep_append (w:List Bool) (n:Nat) (t:List Bool) : value (rep w n++t) = repPack w n (value t) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep,List.append_assoc,value_append,ih,repPack]

theorem pack_rep (w:List Bool) (n t:Nat) : pack (rep w n) t = repPack w n t := by
  obtain ⟨l,hl⟩:=value_surj t
  rw [← hl, ← value_append, value_rep_append]

theorem sweepNR (p:PartialMachine) (q:Fin 6) (lp rp I O:List Bool) (k:Nat)
    (one : ∀ L R : List Bool, run0 p k ⟨q,lp++L,rp++I++R⟩ = some ⟨q,lp++O++L,rp++R⟩)
    (n L R:Nat) :
    runN p (k*n) ⟨q,pack lp L,pack rp (repPack I n R)⟩ = some ⟨q,pack lp (repPack O n L),pack rp R⟩ := by
  obtain ⟨l,hl⟩:=value_surj L
  obtain ⟨r,hr⟩:=value_surj R
  have h := sweepR p q lp rp I O k one n l r
  have he := (run_encode p (k*n) ⟨q,lp++l,rp++rep I n++r⟩).trans (congrArg (Option.map encode) h)
  simpa only [Option.map,encode,List.append_assoc,value_rep_append,value_append,pack_rep,hl,hr] using he

theorem sweepNL (p:PartialMachine) (q:Fin 6) (lp rp I O:List Bool) (k:Nat)
    (one : ∀ L R : List Bool, run0 p k ⟨q,lp++I++L,rp++R⟩ = some ⟨q,lp++L,rp++O++R⟩)
    (n L R:Nat) :
    runN p (k*n) ⟨q,pack lp (repPack I n L),pack rp R⟩ = some ⟨q,pack lp L,pack rp (repPack O n R)⟩ := by
  obtain ⟨l,hl⟩:=value_surj L
  obtain ⟨r,hr⟩:=value_surj R
  have h := sweepL p q lp rp I O k one n l r
  have he := (run_encode p (k*n) ⟨q,lp++rep I n++l,rp++r⟩).trans (congrArg (Option.map encode) h)
  simpa only [Option.map,encode,List.append_assoc,value_rep_append,value_append,pack_rep,hl,hr] using he

theorem sweepFR (p:PartialMachine) (a:Nat) (ha:tableCode p a) (q:Fin 6) (lp rp I O:List Bool) (k:Nat)
    (one : ∀ L R : List Bool, run0 p k ⟨q,lp++L,rp++I++R⟩ = some ⟨q,lp++O++L,rp++R⟩)
    (n L R:Nat) :
    runF a (k*n) ⟨q.val,pack lp L,pack rp (repPack I n R)⟩ = some ⟨q.val,pack lp (repPack O n L),pack rp R⟩ := by
  have h := sweepNR p q lp rp I O k one n L R
  exact (runF_encode p a ha (k*n) ⟨q,pack lp L,pack rp (repPack I n R)⟩).trans (congrArg (Option.map encodeFast) h)

theorem sweepFL (p:PartialMachine) (a:Nat) (ha:tableCode p a) (q:Fin 6) (lp rp I O:List Bool) (k:Nat)
    (one : ∀ L R : List Bool, run0 p k ⟨q,lp++I++L,rp++R⟩ = some ⟨q,lp++L,rp++O++R⟩)
    (n L R:Nat) :
    runF a (k*n) ⟨q.val,pack lp (repPack I n L),pack rp R⟩ = some ⟨q.val,pack lp L,pack rp (repPack O n R)⟩ := by
  have h := sweepNL p q lp rp I O k one n L R
  exact (runF_encode p a ha (k*n) ⟨q,pack lp (repPack I n L),pack rp R⟩).trans (congrArg (Option.map encodeFast) h)
#print axioms sweepFR
#print axioms sweepFL
end BB6.Agent4E0OneLCLate
