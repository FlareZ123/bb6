import BusyBeaver.BB6.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC
import SourceBridgeB
set_option maxHeartbeats 0
set_option maxRecDepth 4000
namespace A4UpstreamBridge
open BusyBeaver.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC

def tup : State → Nat × Nat × Nat
  | .B a k c => (a,k,c)

theorem source_next_eq (a k c : Nat) :
    (next (.B a k c)).map tup = A4Backward.nextC (a,k,c) := by
  rcases c with _ | _ | _ | _ | d
  · rcases a with _ | _ | a
    · rfl
    · rcases k with _ | k
      · rfl
      · simp [next,tup,A4Backward.nextC]
        omega
    · simp [next,tup,A4Backward.nextC]
  · rfl
  · rfl
  · rfl
  · rcases a with _ | a
    · by_cases he : k%2=0
      · simp [next,tup,A4Backward.nextC,he]
        omega
      · simp [next,tup,A4Backward.nextC,he]
        omega
    · simp [next,tup,A4Backward.nextC]

inductive UpReach : State → Prop where
  | init : UpReach start
  | next (s t : State) : UpReach s → next s = some t → UpReach t

theorem transported_reach (s : State) (h : UpReach s) :
    BB6CLine.Reach (tup s) := by
  induction h with
  | init => exact BB6CLine.Reach.init
  | next s t hs hn ih =>
      rcases s with ⟨a,k,c⟩
      rcases t with ⟨a',k',c'⟩
      apply BB6CLine.Reach.next (a,k,c) (a',k',c') ih
      have he := source_next_eq a k c
      rw [hn] at he
      change some (a',k',c') = A4Backward.nextC (a,k,c) at he
      rw [← A4Backward.nextC_source_equal]
      exact he.symm

theorem upstream_no_bad (a k c : Nat) (h : UpReach (.B a k c)) :
    ¬A4Backward.bad a k c ∧ ¬A4BackwardB.badB a k c := by
  have hr := transported_reach (.B a k c) h
  exact ⟨A4Backward.source_blank_never_bad _ hr, A4BackwardB.source_blank_never_badB _ hr⟩

def upstreamRun : Nat → Option State
  | 0 => some start
  | n+1 => (upstreamRun n).bind next

theorem upstreamRun_reach (n : Nat) (s : State)
    (h : upstreamRun n = some s) : UpReach s := by
  induction n generalizing s with
  | zero =>
      simp only [upstreamRun] at h
      have he : start=s := Option.some.inj h
      subst s
      exact UpReach.init
  | succ n ih =>
      change (upstreamRun n).bind next = some s at h
      cases hv : upstreamRun n with
      | none => simp [hv] at h
      | some t =>
          have ht := ih t hv
          simpa [hv] using (UpReach.next t s ht (by simpa [hv] using h))

theorem upstreamRun_never_bad (n a k c : Nat)
    (h : upstreamRun n = some (.B a k c)) :
    ¬A4Backward.bad a k c ∧ ¬A4BackwardB.badB a k c :=
  upstream_no_bad a k c (upstreamRun_reach n _ h)

#print axioms upstreamRun_reach
#print axioms upstreamRun_never_bad
#print axioms source_next_eq
#print axioms transported_reach
#print axioms upstream_no_bad
end A4UpstreamBridge
