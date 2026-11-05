import Std
set_option maxHeartbeats 0
namespace CascadeFastReturn

/-- Primitive recursion on an explicit upper bound, to make even large
    numeral instances kernel-reducible without well-founded evaluator magic. -/
def stripAux (q:Nat) : Nat → Nat × Nat
| 0 => (0,q)
| fuel+1 =>
   if q%2=1 then (0,q)
   else if q=0 then (0,0)
   else
     let p := stripAux (q/2) fuel
     (p.1+1,p.2)

def stripTwos (q:Nat) : Nat × Nat := stripAux q q

theorem stripAux_spec (q fuel : Nat) (hq : 0<q) (hf:q≤fuel) :
    q = 2^(stripAux q fuel).1 * (stripAux q fuel).2 ∧
    (stripAux q fuel).2%2=1 := by
  induction fuel generalizing q with
  | zero => omega
  | succ fuel ih =>
    by_cases hodd:q%2=1
    · simp [stripAux,hodd]
    · have heven:q%2=0 := by omega
      have hq2:0<q/2 := by omega
      have hlt:q/2≤fuel := by omega
      obtain ⟨hfac,hpar⟩:=ih (q/2) hq2 hlt
      have hqeq:q=2*(q/2) := by omega
      have hstep: stripAux q (fuel+1) =
          ((stripAux (q/2) fuel).1+1,(stripAux (q/2) fuel).2) := by
        simp [stripAux,hodd,show q≠0 by omega]
      rw [hstep]
      constructor
      · simp only [Prod.fst,Prod.snd]
        calc
          q=2*(q/2) := hqeq
          _=2*(2^(stripAux (q/2) fuel).1*(stripAux (q/2) fuel).2) := congrArg (2*·) hfac
          _=2^((stripAux (q/2) fuel).1+1)*(stripAux (q/2) fuel).2 := by
            rw [Nat.pow_succ]; ac_rfl
      · exact hpar

theorem stripTwos_spec (q:Nat) (hq:0<q) :
    q=2^(stripTwos q).1*(stripTwos q).2 ∧ (stripTwos q).2%2=1 :=
  stripAux_spec q q hq (Nat.le_refl q)

#print axioms stripTwos_spec
end CascadeFastReturn
