import SourceSRun

namespace Agent9SourceSRun
open BusyBeaver.M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB

theorem t_226_halt (m : Nat) (h : m%243=226) :
    highLevelNext (.T m) = none := by
  have h0 : m%3=1 := by omega
  have h1 : (2*(2*(m/3))+7)%3=1 := by omega
  have h2 : (2*(2*((2*(2*(m/3))+7)/3))+7)%3=1 := by omega
  have h3 : (2*(2*((2*(2*((2*(2*(m/3))+7)/3))+7)/3))+7)%3=1 := by omega
  simp [highLevelNext, h0, h1, h2, h3]

theorem s_transfer_then_t_halt (b c : Nat)
    (ht : Agent9SProjection.Sstep (b+16) c = none)
    (hd : (b+16)%729=0) :
    (highLevelNext (.S b c)).bind highLevelNext = none := by
  have hq : (b+16)%3=0 := by
    unfold Agent9SProjection.Sstep at ht
    by_cases hx : (b+16)%3=0
    · exact hx
    · by_cases hy : (b+16)%3=1
      · simp [hx, hy] at ht
      · simp [hx, hy] at ht
  have hc : c=0 := by
    simpa [Agent9SProjection.Sstep, hq] using ht
  have hb0 : b%3≠0 := by omega
  have hb1 : b%3≠1 := by omega
  have hm : (4*(b/3)+7)%243=226 := by omega
  have hs : highLevelNext (.S b c) = some (.T (4*(b/3)+7)) := by
    simp [highLevelNext,hb0,hb1,hc]
    omega
  rw [hs]
  simpa using t_226_halt (4*(b/3)+7) hm

theorem source_immediate_halt_after_transfer (n b c q d : Nat)
    (hlive : scalarRun n (some (b+16,c)) = some (q,d))
    (htransfer : scalarRun (n+1) (some (b+16,c)) = none)
    (hdiv : q%729=0) :
    sourceRun (n+2) (some (.S b c)) = none := by
  obtain ⟨b',hq,hs⟩ := live_source_steps n b c q d hlive
  have ht : Agent9SProjection.Sstep (b'+16) d = none := by
    simpa [scalarRun,hlive,hq] using htransfer
  have hd : (b'+16)%729=0 := by omega
  have hg := s_transfer_then_t_halt b' d ht hd
  change ((sourceRun n (some (.S b c))).bind highLevelNext).bind highLevelNext = none
  rw [hs]
  exact hg

theorem sourceRun_add (n m : Nat) (s : Option HighLevelState) :
    sourceRun (n+m) s = sourceRun m (sourceRun n s) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change (sourceRun (n+m) s).bind highLevelNext =
        (sourceRun m (sourceRun n s)).bind highLevelNext
      rw [ih]

theorem original_root_three :
    sourceRun 3 (some (.T 1)) = some (.S 125 3) := by decide

theorem blank_source_halt_if_729_gate (n q d : Nat)
    (hlive : scalarRun n (some (141,3)) = some (q,d))
    (htransfer : scalarRun (n+1) (some (141,3)) = none)
    (hdiv : q%729=0) :
    sourceRun (n+5) (some (.T 1)) = none := by
  have hmain := source_immediate_halt_after_transfer n 125 3 q d hlive htransfer hdiv
  have heq : n+5=3+(n+2) := by omega
  rw [heq,sourceRun_add,original_root_three]
  exact hmain

#print axioms sourceRun_add
#print axioms original_root_three
#print axioms blank_source_halt_if_729_gate
#print axioms t_226_halt
#print axioms s_transfer_then_t_halt
#print axioms source_immediate_halt_after_transfer
end Agent9SourceSRun
