import Lean.Elab.Tactic.Omega
import PacketShift
import E110111Pairs
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace BB6.Agent2PacketEscape
open CryptidBoundary BB6.Agent31PacketSource BB6.Agent31PacketPaths

def initialTail (ys : List Bool) : List Bool := [false,true,true,true] ++ ys
def finalTail (ys : List Bool) : List Bool := [false,true,false,true,false] ++ ys

private theorem swap (q : Nat) (ys : List Bool) :
    oppairs q ++ false :: ys = false :: (pairs q ++ ys) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simpa [oppairs, pairs, List.append_assoc] using
      congrArg (List.cons false ∘ List.cons true) ih

private theorem initial_shape (k q : Nat) (ys : List Bool) :
    physical ⟨3*k+4,q,2⟩ (initialTail ys) =
      init (List.replicate (3*k+2) true ++
        false :: (pairs q ++ ([true,true,false,true,true,true] ++ ys))) := by
  simp only [physical,packet,word,initialTail]
  rw [show List.replicate (3*k+4) true =
      true :: true :: List.replicate (3*k+2) true by
        rw [show 3*k+4=2+(3*k+2) by omega,
            ←List.replicate_append_replicate]; rfl]
  simp only [List.cons_append,List.append_assoc,init]
  congr 1
  rw [swap q]
  simp [List.append_assoc]

private theorem output_shape (k q : Nat) (ys : List Bool) :
    (⟨[],false,List.replicate (8*k+3) true ++
      BB6.Agent37E110111.longPacket q ys,5⟩ : Cfg) =
    physical ⟨8*k+5,0,2*q+6⟩ (finalTail ys) := by
  simp [physical,packet,word,finalTail,BB6.Agent37E110111.longPacket]
  rw [show 8*k+5=(8*k+3)+2 by omega]
  rw [show 2*q+6=3+(2*(q+1)+1) by omega]
  simp only [←List.replicate_append_replicate]
  simp [List.replicate_succ, List.append_assoc, oppairs]

theorem e2_source (k q : Nat) (ys : List Bool) :
    run (12*k*k+49*k+68+4*q)
      (physical ⟨3*k+4,q,2⟩ (initialTail ys)) =
    physical ⟨8*k+5,0,2*q+6⟩ (finalTail ys) := by
  rw [initial_shape]
  rw [BB6.Agent37E110111.full_E_110111_pairs_raw]
  exact output_shape k q ys

def escapeCost (k q : Nat) : Nat := 12*k*k+49*k+68+4*q

private theorem eight_square (n : Nat) : 8^n*8^n=64^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      8^(n+1)*8^(n+1) = (8^n*8^n)*(8*8) := by
        simp only [Nat.pow_succ]
        ac_rfl
      _ = 64^(n+1) := by rw [ih]; simp only [Nat.pow_succ]

private theorem quadratic_right (n : Nat) :
    BB6.Agent31PacketShift.quadratic (n+1) =
      9*BB6.Agent31PacketShift.quadratic n+12*64^n := by
  have h0 := BB6.Agent31PacketShift.quadratic_closed n
  have h1 := BB6.Agent31PacketShift.quadratic_closed (n+1)
  simp only [Nat.pow_succ] at h1
  omega

private theorem cost_join (D U L Q k n x : Nat) :
    (D+L*(3*x)+Q*(3*x)*(3*x))+
      (U+(24*k+49)*(8^n*x)+12*(8^n*x)*(8^n*x)) =
    (D+U)+(3*L+(24*k+49)*8^n)*x+
      (9*Q+12*64^n)*x*x := by
  have h1 : L*(3*x)=(3*L)*x := by ac_rfl
  have h2 : Q*(3*x)*(3*x)=(9*Q)*x*x := by
    calc
      Q*(3*x)*(3*x) = (3*3*Q)*x*x := by ac_rfl
      _ = (9*Q)*x*x := by rfl
  have h3 : (24*k+49)*(8^n*x)=((24*k+49)*8^n)*x := by ac_rfl
  have h4 : 12*(8^n*x)*(8^n*x)=(12*64^n)*x*x := by
    calc
      12*(8^n*x)*(8^n*x)=(12*(8^n*8^n))*x*x := by ac_rfl
      _=(12*64^n)*x*x := by rw [eight_square]
  rw [h1,h2,h3,h4]
  simp only [Nat.add_mul,Nat.mul_assoc]
  omega

private theorem escape_cost_shift (k q r : Nat) :
    escapeCost (k+r) q =
      escapeCost k q+(24*k+49)*r+12*r*r := by
  dsimp [escapeCost]
  have hmul : r*k=k*r := Nat.mul_comm r k
  simp only [Nat.add_mul,Nat.mul_add,Nat.mul_assoc]
  omega

/-- Unbounded B/E packet phase followed by a low-p E boundary that changes
    the arbitrary binary tail. The exact primitive-time quadratic curvature
    survives the suffix grammar reset. This remains a synthetic-input theorem. -/
theorem source_path_escape_shift
    {s : State} {n cost : Nat} (k q : Nat)
    (h : Path s n cost ⟨3*k+4,q,2⟩) (ys : List Bool) :
    ∃ L : Nat, ∀ x : Nat, ∃ elapsed : Nat,
      run elapsed
        (physical (BB6.Agent31PacketShift.shift s (3^(n+1)*x)) (initialTail ys)) =
        physical
          (BB6.Agent31PacketShift.shift (⟨8*k+5,0,2*q+6⟩ : State) (8^(n+1)*x))
          (finalTail ys) ∧
      elapsed = cost+escapeCost k q+L*x+
        BB6.Agent31PacketShift.quadratic (n+1)*x*x := by
  obtain ⟨L,hL⟩ := BB6.Agent31PacketShift.path_shift h
  refine ⟨3*L+(24*k+49)*8^n, ?_⟩
  intro x
  obtain ⟨C,hshift,hcost⟩ := hL (3*x)
  let r := 8^n*x
  have hmid :
      BB6.Agent31PacketShift.shift (⟨3*k+4,q,2⟩ : State) (8^n*(3*x)) =
      (⟨3*(k+r)+4,q,2⟩ : State) := by
    simp only [BB6.Agent31PacketShift.shift]
    congr 1
    have hh : 8^n*(3*x)=3*(8^n*x) := by ac_rfl
    rw [hh]
    dsimp [r]
    omega
  have hfin :
      (⟨8*(k+r)+5,0,2*q+6⟩ : State) =
      BB6.Agent31PacketShift.shift (⟨8*k+5,0,2*q+6⟩ : State)
        (8^(n+1)*x) := by
    simp only [BB6.Agent31PacketShift.shift]
    congr 1
    have hh : 8^(n+1)*x = 8*(8^n*x) := by
      simp only [Nat.pow_succ]
      ac_rfl
    rw [hh]
    dsimp [r]
    omega
  have hp : 3^(n+1)*x=3^n*(3*x) := by
    simp only [Nat.pow_succ]
    ac_rfl
  have hsource := BB6.Agent31PacketPaths.path_sound hshift (initialTail ys)
  have hE := e2_source (k+r) q ys
  rw [←hmid, hfin] at hE
  have hrun :
      run (C+escapeCost (k+r) q)
        (physical (BB6.Agent31PacketShift.shift s (3^(n+1)*x)) (initialTail ys)) =
        physical
          (BB6.Agent31PacketShift.shift (⟨8*k+5,0,2*q+6⟩ : State) (8^(n+1)*x))
          (finalTail ys) := by
    rw [hp, run_add, hsource]
    exact hE
  refine ⟨C+escapeCost (k+r) q,hrun,?_⟩
  have hec := escape_cost_shift k q r
  calc
    C+escapeCost (k+r) q =
      (cost+L*(3*x)+BB6.Agent31PacketShift.quadratic n*(3*x)*(3*x))+
        (escapeCost k q+(24*k+49)*(8^n*x)+12*(8^n*x)*(8^n*x)) := by
          rw [hcost,hec]
    _=(cost+escapeCost k q)+
      (3*L+(24*k+49)*8^n)*x+
      (9*BB6.Agent31PacketShift.quadratic n+12*64^n)*x*x := by
        exact cost_join cost (escapeCost k q) L
          (BB6.Agent31PacketShift.quadratic n) k n x
    _=(cost+escapeCost k q)+
      (3*L+(24*k+49)*8^n)*x+
      BB6.Agent31PacketShift.quadratic (n+1)*x*x := by
        rw [quadratic_right n]

#print axioms source_path_escape_shift
#print axioms e2_source
end BB6.Agent2PacketEscape
