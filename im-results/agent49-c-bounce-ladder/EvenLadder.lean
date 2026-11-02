import Ladder
import Lean.Elab.Tactic.Omega
namespace BB6.Agent49
open BB6.Agent46 (run run_high)

private theorem even_high_start (k c : Nat) (hk : k%2=0) (hc : 4≤c) :
    BB6CLine.nextC (0,k,c)=some (2*k+2,2,c-3) := by
  obtain ⟨d,rfl⟩ : ∃ d, c=d+4 := ⟨c-4,by omega⟩
  have hdiv : k%2+2*(k/2)=k := Nat.mod_add_div k 2
  simp only [BB6CLine.nextC,hk,ite_true,Option.some.injEq,Prod.mk.injEq]
  constructor
  · omega
  · constructor
    · trivial
    · omega

theorem even_full_bounce (k c : Nat) (hk : k%2=0) (hc : 2*k+9≤c) :
    run (2*k+3) (some (0,k,c)) = some (0,2*k+4,c-(2*k+5)) := by
  have hfirst := even_high_start k c hk (by omega)
  have hh := run_high (2*k+2) (2*k+2) 2 (c-3) (by omega) (by omega)
  have hn : 2*k+3=(2*k+2)+1 := by omega
  rw [hn]
  change run (2*k+2) ((some (0,k,c)).bind BB6CLine.nextC) = _
  simp only [Option.bind_some,hfirst]
  rw [hh]
  simp only [Option.some.injEq,Prod.mk.injEq]
  constructor
  · omega
  · constructor
    · omega
    · omega

def KE (k : Nat) : Nat → Nat
  | 0 => k
  | n+1 => 2*KE k n+4
def DE (k : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => DE k n + 2*KE k n+5
def TE (k : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => TE k n + 2*KE k n+3

theorem KE_even (k n : Nat) (hk : k%2=0) : KE k n %2=0 := by
  induction n with
  | zero => simpa [KE] using hk
  | succ n ih => simp [KE]
theorem KE_closed (k n : Nat) : KE k n+4=(k+4)*2^n := by
  induction n with
  | zero => simp [KE]
  | succ n ih =>
      calc
        KE k (n+1)+4=2*(KE k n+4) := by simp [KE]; omega
        _=2*((k+4)*2^n) := by rw [ih]
        _=(k+4)*2^(n+1) := by simp only [Nat.pow_succ]; ac_rfl
theorem DE_conservation (k n : Nat) : DE k n+3*n+2*k=2*KE k n := by
  induction n with
  | zero => simp [KE,DE]
  | succ n ih => simp only [KE,DE]; omega
theorem TE_conservation (k n : Nat) : TE k n+5*n+2*k=2*KE k n := by
  induction n with
  | zero => simp [KE,TE]
  | succ n ih => simp only [KE,TE]; omega

theorem even_ladder (k c n : Nat) (hk : k%2=0) (hc : DE k n+4≤c) :
    run (TE k n) (some (0,k,c)) = some (0,KE k n,c-DE k n) := by
  induction n with
  | zero => simp [TE,KE,DE,run]
  | succ n ih =>
      have hsmall : DE k n+4≤c := by simp only [DE] at hc; omega
      have hmid : 2*KE k n+9≤c-DE k n := by simp only [DE] at hc; omega
      have hprefix := ih hsmall
      have hstep := even_full_bounce (KE k n) (c-DE k n) (KE_even k n hk) hmid
      have ht : TE k (n+1)=TE k n+(2*KE k n+3) := by simp only [TE]; omega
      rw [ht,run_add,hprefix,hstep]
      simp only [KE,DE,Option.some.injEq,Prod.mk.injEq]
      constructor
      · trivial
      · constructor
        · trivial
        · omega

theorem even_five_halts (k : Nat) (hk : k%2=0) :
    run 2 (some (0,k,5))=none := by
  have hfirst := even_high_start k 5 hk (by omega)
  change run 1 (BB6CLine.nextC (0,k,5)) = none
  rw [hfirst]
  rfl
theorem even_ladder_halts (k n : Nat) (hk : k%2=0) :
    run (TE k n+2) (some (0,k,DE k n+5))=none := by
  have hw := even_ladder k (DE k n+5) n hk (by omega)
  have he : DE k n+5-DE k n=5 := by omega
  rw [he] at hw
  rw [run_add,hw,even_five_halts (KE k n) (KE_even k n hk)]

#print axioms even_full_bounce
#print axioms even_ladder
#print axioms KE_closed
#print axioms DE_conservation
#print axioms TE_conservation
#print axioms even_ladder_halts
end BB6.Agent49
