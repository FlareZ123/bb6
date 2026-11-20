import DRegularTimedShift
import D3SecondReturnAlignment

set_option maxRecDepth 8192
set_option maxHeartbeats 100000000

open DRegular BB6.DRegularShift BB6.DRegularTimedShift
open BB6.Agent37D3SecondReturnAlignment

def seed24956 : L := ⟨24956,2,2⟩
def seed24956Exit : L :=
  ⟨107283033157493534200791430928221345342090,5,1⟩

def baseElapsed : Nat :=
  2511196189848405180808251215091282020771681398870051748082508810955840054369100891

def linear86 : Nat :=
  21682955431020992450687592512031549428761789617393244525648556756170589602211578845156336539672418515126244544667539067

def quadratic86 : Nat :=
  46805438591799611693058414539191317390473422500977082336780432676265067156996244565519795950786187022640336620345338430295663495134566650263613298250975468

theorem seed24956_run86 :
    run 86 seed24956 = some seed24956Exit := by decide

theorem seed24956_elapsed86 :
    accumulated 86 seed24956 = baseElapsed := by decide

theorem seed24956_linear86 :
    linearCoeff 86 seed24956 = linear86 := by decide

theorem seed24956_quadratic86 :
    quadCoeff 86 = quadratic86 := by decide

theorem d3_family_input (v : Nat) :
    BB6.DRegularShift.shiftNat seed24956 (3^86*packetShift v) =
      ⟨familyEndpoint v,2,2⟩ := by
  simp only [BB6.DRegularShift.shiftNat, seed24956]
  congr 1
  exact (input_shift_for_86_steps v).symm

theorem d3_family_output (v : Nat) :
    BB6.DRegularShift.shiftNat seed24956Exit (8^86*packetShift v) =
      ⟨3*shiftedExitK v+4,5,1⟩ := by
  simp only [BB6.DRegularShift.shiftNat, seed24956Exit]
  congr 1
  simpa [baseExitA] using (transported_exit_shape v)

theorem d3_family_run86 (v : Nat) :
    run 86 ⟨familyEndpoint v,2,2⟩ =
      some ⟨3*shiftedExitK v+4,5,1⟩ := by
  have hcanon : Canon seed24956 := by simp [Canon, seed24956]
  have hrun := BB6.DRegularShift.run_shift 86 seed24956 (packetShift v) hcanon
  rw [seed24956_run86] at hrun
  rw [← d3_family_input v, ← d3_family_output v]
  exact hrun

theorem d3_family_elapsed86 (v : Nat) :
    accumulated 86 ⟨familyEndpoint v,2,2⟩ =
      baseElapsed + linear86 * packetShift v +
        quadratic86 * packetShift v * packetShift v := by
  have hcanon : Canon seed24956 := by simp [Canon, seed24956]
  have hrun : run 86 seed24956 = some seed24956Exit := seed24956_run86
  have htime := BB6.DRegularTimedShift.accumulated_shift
    86 seed24956 seed24956Exit (packetShift v) hcanon hrun
  rw [seed24956_elapsed86, seed24956_linear86, seed24956_quadratic86] at htime
  rw [← d3_family_input v]
  exact htime

#print axioms seed24956_run86
#print axioms seed24956_elapsed86
#print axioms seed24956_linear86
#print axioms seed24956_quadratic86
#print axioms d3_family_input
#print axioms d3_family_output
#print axioms d3_family_run86
#print axioms d3_family_elapsed86
