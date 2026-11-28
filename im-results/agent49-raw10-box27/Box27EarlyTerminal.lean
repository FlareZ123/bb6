import Box27D0FastPumps

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent49.Box27EarlyTerminal
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode slot Witness leafCheck)
open BB6.Agent49.Box27Slice (terminal_sound)

structure Entry where
  d0 : Fin 25
  s : Fin 12
  v : Fin 25
  w : Witness

def table (e : Entry) : PartialMachine :=
  refine (Box27D0FastPumps.table e.d0) (slot e.s) (decode e.v)

/-- 137 first-query children: 14 halts and 123 translated cycles. -/
def entries : List Entry := [
  ⟨2,3,0,.halt 5⟩,
  ⟨2,3,2,.cycle 0 6 true (-1)⟩,
  ⟨2,3,5,.cycle 3 6 false (1)⟩,
  ⟨2,3,7,.cycle 3 6 false (1)⟩,
  ⟨2,3,9,.cycle 0 8 true (-1)⟩,
  ⟨2,3,10,.cycle 0 8 true (-1)⟩,
  ⟨2,3,11,.cycle 2 4 true (-1)⟩,
  ⟨2,3,14,.cycle 0 7 true (-1)⟩,
  ⟨2,3,16,.cycle 0 7 true (-1)⟩,
  ⟨3,3,0,.halt 5⟩,
  ⟨3,3,5,.cycle 3 6 false (-1)⟩,
  ⟨3,3,7,.cycle 3 6 false (-1)⟩,
  ⟨3,3,9,.cycle 2 4 false (0)⟩,
  ⟨3,3,11,.cycle 2 4 false (0)⟩,
  ⟨4,3,0,.halt 5⟩,
  ⟨4,3,2,.cycle 0 6 true (-1)⟩,
  ⟨4,3,5,.cycle 3 7 false (1)⟩,
  ⟨4,3,7,.cycle 3 7 false (1)⟩,
  ⟨12,7,0,.halt 5⟩,
  ⟨12,7,1,.cycle 0 6 false (1)⟩,
  ⟨12,7,5,.cycle 3 5 false (0)⟩,
  ⟨12,7,6,.cycle 3 5 false (0)⟩,
  ⟨12,7,7,.cycle 3 5 false (0)⟩,
  ⟨12,7,8,.cycle 1 5 false (1)⟩,
  ⟨12,7,9,.cycle 3 4 false (0)⟩,
  ⟨12,7,10,.cycle 3 4 true (-1)⟩,
  ⟨12,7,11,.cycle 3 4 false (0)⟩,
  ⟨12,7,12,.cycle 4 2 true (-1)⟩,
  ⟨12,7,13,.cycle 3 3 false (0)⟩,
  ⟨12,7,14,.cycle 8 3 true (0)⟩,
  ⟨12,7,15,.cycle 5 3 false (-1)⟩,
  ⟨12,7,16,.cycle 8 3 true (0)⟩,
  ⟨14,7,0,.halt 5⟩,
  ⟨14,7,1,.cycle 0 6 true (-1)⟩,
  ⟨14,7,2,.cycle 0 6 true (-1)⟩,
  ⟨14,7,5,.cycle 3 5 false (1)⟩,
  ⟨14,7,6,.cycle 3 5 true (-1)⟩,
  ⟨14,7,7,.cycle 3 5 false (1)⟩,
  ⟨14,7,8,.cycle 1 5 true (-1)⟩,
  ⟨14,7,9,.cycle 7 1 true (-1)⟩,
  ⟨14,7,10,.cycle 7 1 true (1)⟩,
  ⟨14,7,11,.cycle 3 4 true (-1)⟩,
  ⟨14,7,12,.cycle 5 2 true (1)⟩,
  ⟨14,7,13,.cycle 6 1 true (0)⟩,
  ⟨14,7,14,.cycle 6 1 true (2)⟩,
  ⟨14,7,15,.cycle 4 2 true (0)⟩,
  ⟨14,7,16,.cycle 6 1 true (2)⟩,
  ⟨16,7,0,.halt 5⟩,
  ⟨16,7,2,.cycle 0 6 true (-1)⟩,
  ⟨16,7,9,.cycle 9 1 true (-3)⟩,
  ⟨16,7,10,.cycle 7 1 true (1)⟩,
  ⟨16,7,11,.cycle 3 6 false (1)⟩,
  ⟨16,7,12,.cycle 5 2 true (1)⟩,
  ⟨16,7,13,.cycle 8 1 true (-2)⟩,
  ⟨16,7,14,.cycle 6 1 true (2)⟩,
  ⟨16,7,15,.cycle 6 3 false (0)⟩,
  ⟨16,7,16,.cycle 6 1 true (2)⟩,
  ⟨17,8,0,.halt 4⟩,
  ⟨17,8,1,.cycle 0 5 false (1)⟩,
  ⟨17,8,2,.cycle 0 5 false (1)⟩,
  ⟨17,8,5,.cycle 3 4 false (-1)⟩,
  ⟨17,8,6,.cycle 3 4 false (-1)⟩,
  ⟨17,8,7,.cycle 3 4 false (-1)⟩,
  ⟨17,8,8,.cycle 1 4 false (1)⟩,
  ⟨17,8,9,.cycle 3 3 false (-1)⟩,
  ⟨17,8,10,.cycle 3 3 false (-1)⟩,
  ⟨17,8,11,.cycle 3 3 false (-1)⟩,
  ⟨17,8,13,.cycle 3 2 false (-1)⟩,
  ⟨17,8,14,.cycle 3 2 true (-2)⟩,
  ⟨17,8,15,.cycle 3 2 false (-1)⟩,
  ⟨17,8,17,.cycle 4 1 false (-2)⟩,
  ⟨17,8,19,.cycle 4 1 false (-2)⟩,
  ⟨18,8,0,.halt 4⟩,
  ⟨18,8,1,.cycle 0 5 false (1)⟩,
  ⟨18,8,5,.cycle 3 4 false (0)⟩,
  ⟨18,8,7,.cycle 3 4 false (0)⟩,
  ⟨18,8,9,.cycle 3 3 false (0)⟩,
  ⟨18,8,10,.cycle 6 3 true (0)⟩,
  ⟨18,8,11,.cycle 3 3 false (0)⟩,
  ⟨18,8,13,.cycle 3 2 true (-1)⟩,
  ⟨18,8,17,.cycle 4 1 false (0)⟩,
  ⟨18,8,19,.cycle 4 1 false (0)⟩,
  ⟨19,8,0,.halt 4⟩,
  ⟨19,8,1,.cycle 0 5 false (1)⟩,
  ⟨19,8,5,.cycle 3 4 false (-1)⟩,
  ⟨19,8,7,.cycle 3 4 false (-1)⟩,
  ⟨19,8,9,.cycle 3 3 false (-1)⟩,
  ⟨19,8,10,.cycle 2 3 false (0)⟩,
  ⟨19,8,11,.cycle 3 3 false (-1)⟩,
  ⟨19,8,13,.cycle 3 2 false (-1)⟩,
  ⟨19,8,15,.cycle 3 2 false (-1)⟩,
  ⟨19,8,17,.cycle 4 1 false (-2)⟩,
  ⟨19,8,19,.cycle 4 1 false (-2)⟩,
  ⟨20,8,0,.halt 4⟩,
  ⟨20,8,9,.cycle 2 3 false (0)⟩,
  ⟨20,8,10,.cycle 6 3 true (0)⟩,
  ⟨20,8,11,.cycle 2 3 false (0)⟩,
  ⟨21,10,0,.halt 4⟩,
  ⟨21,10,1,.cycle 0 5 false (1)⟩,
  ⟨21,10,2,.cycle 0 5 false (1)⟩,
  ⟨21,10,5,.cycle 3 4 false (-1)⟩,
  ⟨21,10,6,.cycle 3 4 false (-1)⟩,
  ⟨21,10,7,.cycle 3 4 false (-1)⟩,
  ⟨21,10,8,.cycle 1 4 false (1)⟩,
  ⟨21,10,9,.cycle 3 3 false (-1)⟩,
  ⟨21,10,10,.cycle 3 3 false (-1)⟩,
  ⟨21,10,11,.cycle 3 3 false (-1)⟩,
  ⟨21,10,13,.cycle 3 2 false (-1)⟩,
  ⟨21,10,14,.cycle 3 2 true (-2)⟩,
  ⟨21,10,15,.cycle 3 2 false (-1)⟩,
  ⟨21,10,21,.cycle 4 1 false (-2)⟩,
  ⟨21,10,23,.cycle 4 1 false (-2)⟩,
  ⟨22,10,0,.halt 4⟩,
  ⟨22,10,1,.cycle 0 5 false (1)⟩,
  ⟨22,10,5,.cycle 3 4 false (0)⟩,
  ⟨22,10,7,.cycle 3 4 false (0)⟩,
  ⟨22,10,9,.cycle 3 3 false (0)⟩,
  ⟨22,10,10,.cycle 6 3 true (0)⟩,
  ⟨22,10,11,.cycle 3 3 false (0)⟩,
  ⟨22,10,13,.cycle 3 2 true (-1)⟩,
  ⟨22,10,21,.cycle 4 1 false (0)⟩,
  ⟨22,10,23,.cycle 4 1 false (0)⟩,
  ⟨23,10,0,.halt 4⟩,
  ⟨23,10,1,.cycle 0 5 false (1)⟩,
  ⟨23,10,5,.cycle 3 4 false (-1)⟩,
  ⟨23,10,7,.cycle 3 4 false (-1)⟩,
  ⟨23,10,9,.cycle 3 3 false (-1)⟩,
  ⟨23,10,10,.cycle 2 3 false (0)⟩,
  ⟨23,10,11,.cycle 3 3 false (-1)⟩,
  ⟨23,10,13,.cycle 3 2 false (-1)⟩,
  ⟨23,10,15,.cycle 3 2 false (-1)⟩,
  ⟨23,10,21,.cycle 4 1 false (-2)⟩,
  ⟨23,10,23,.cycle 4 1 false (-2)⟩,
  ⟨24,10,0,.halt 4⟩,
  ⟨24,10,9,.cycle 2 3 false (0)⟩,
  ⟨24,10,10,.cycle 6 3 true (0)⟩,
  ⟨24,10,11,.cycle 2 3 false (0)⟩
]

theorem all_checked : entries.all (fun e => leafCheck 255 #[] (table e) e.w) = true := by decide

theorem source_bound (e : Entry) (he : e ∈ entries) (m : Machine)
    (hm : Fits raw10Remainder[27]! m)
    (hd : m (3,false) = decode e.d0)
    (hv : m (slot e.s) = decode e.v) : WeightedBound 255 m := by
  apply terminal_sound 255 (table e) e.w (List.all_eq_true.mp all_checked e he) m
  unfold table
  rw [← hv]
  exact compatible_refine _ m (slot e.s) (Box27D0FastPumps.source_compatible e.d0 m hm hd)

def selected (d0 d1 e0 b1 f0 : Fin 25) : Bool :=
  entries.any (fun e => decide (e.d0 = d0) &&
    (if e.s = 3 then decide (e.v = b1)
     else if e.s = 7 then decide (e.v = d1)
     else if e.s = 8 then decide (e.v = e0)
     else if e.s = 10 then decide (e.v = f0) else false))

theorem selected_bound (m : Machine) (hm : Fits raw10Remainder[27]! m)
    (d0 d1 e0 b1 f0 : Fin 25)
    (hd0 : m (3,false) = decode d0)
    (hd1 : m (3,true) = decode d1)
    (he0 : m (4,false) = decode e0)
    (hb1 : m (1,true) = decode b1)
    (hf0 : m (5,false) = decode f0)
    (h : selected d0 d1 e0 b1 f0 = true) : WeightedBound 255 m := by
  obtain ⟨e,he,hc⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hc
  apply source_bound e he m hm (hc.1.symm ▸ hd0)
  have hh := hc.2
  split at hh
  · rename_i hs
    have hv : e.v = b1 := of_decide_eq_true hh
    simpa only [hs,hv] using hb1
  · split at hh
    · rename_i hs
      have hv : e.v = d1 := of_decide_eq_true hh
      simpa only [hs,hv] using hd1
    · split at hh
      · rename_i hs
        have hv : e.v = e0 := of_decide_eq_true hh
        simpa only [hs,hv] using he0
      · split at hh
        · rename_i hs
          have hv : e.v = f0 := of_decide_eq_true hh
          simpa only [hs,hv] using hf0
        · contradiction

#print axioms all_checked
#print axioms source_bound
#print axioms selected_bound
end BB6.Agent49.Box27EarlyTerminal
