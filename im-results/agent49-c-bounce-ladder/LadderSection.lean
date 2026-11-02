import Ladder
import Lean.Elab.Tactic.Omega
namespace BB6.Agent49
open BB6.Agent46 (run run_high)

private theorem odd_tail_start (k c : Nat) (hk : k%2=1) (hc : 4≤c) :
    BB6CLine.nextC (0,k,c)=some (2*k+3,0,c) := by
  obtain ⟨d,rfl⟩ : ∃ d, c=d+4 := ⟨c-4,by omega⟩
  have hne : k%2 ≠ 0 := by omega
  have hdiv : k%2+2*(k/2)=k := Nat.mod_add_div k 2
  simp only [BB6CLine.nextC,hne,ite_false,Option.some.injEq, Prod.mk.injEq]
  constructor
  · omega
  · trivial

/-- Finish an odd-middle bounce exactly when c is between 4 and 2k+6. -/
theorem odd_last_bounce (k c : Nat) (hk : k%2=1)
    (hlo : 4≤c) (hhi : c≤2*k+6) :
    run c (some (0,k,c)) = some (2*k+6-c,c,0) := by
  have hfirst := odd_tail_start k c hk hlo
  have hp : c-3≤2*k+3 := by omega
  have hhigh := run_high (c-3) (2*k+3) 0 c hp (by omega)
  have hstate : some (2*k+3-(c-3),c-3,3) =
      (some (2*k+6-c,c-3,3) : Option S) := by
    simp only [Option.some.injEq,Prod.mk.injEq]
    constructor
    · omega
    · constructor <;> rfl
  have htarget : run (c-3) (some (2*k+3,0,c)) =
      some (2*k+6-c,c-3,3) := by
    rw [hhigh]
    rw [show 0+(c-3)=c-3 by omega,
        show c-(c-3)=3 by omega]
    exact hstate

  have htail : run 2 (some (2*k+6-c,c-3,3)) =
      some (2*k+6-c,c,0) := by
    simp [run,BB6CLine.nextC]
    omega
  have hn : c=1+(c-3)+2 := by omega
  have h1 : run 1 (some (0,k,c)) = some (2*k+3,0,c) := by
    simp [run,hfirst]
  calc
    run c (some (0,k,c)) = run (1+(c-3)+2) (some (0,k,c)) :=
      congrArg (fun t => run t (some (0,k,c))) hn
    _ = run 2 (run (c-3) (run 1 (some (0,k,c)))) := by
      rw [run_add,run_add]
    _ = some (2*k+6-c,c,0) := by rw [h1,htarget,htail]

/-- All a>=2 starts in the c=0 section with a<=2k reach the first zero-left
    high state after exactly a-1 transitions. -/
theorem start_to_zero (a k : Nat) (ha : 2≤a) (hk : a≤2*k) :
    run (a-1) (some (a,k,0)) = some (0,a-1,2*k-a+3) := by
  have hfirst : BB6CLine.nextC (a,k,0) = some (a-2,1,2*k+1) := by
    obtain ⟨u,rfl⟩ : ∃ u, a=u+2 := ⟨a-2,by omega⟩
    simp [BB6CLine.nextC]
  have hh := run_high (a-2) (a-2) 1 (2*k+1) (by omega) (by omega)
  have hn : a-1=(a-2)+1 := by omega
  rw [hn]
  change run (a-2) ((some (a,k,0)).bind BB6CLine.nextC) = _
  simp only [Option.bind_some,hfirst]
  rw [hh]
  simp only [Option.some.injEq,Prod.mk.injEq]
  omega

/-- A single all-depth formula extends the known one-bounce even-start cone.
    This gives an exact c=0 section return, irrespective of ladder depth n. -/
theorem even_section_ladder (a k n : Nat)
    (ha : 2≤a) (he : a%2=0) (hk : a≤2*k)
    (hlo : D (a-1) n+4≤2*k-a+3)
    (hhi : 2*k-a+3-D (a-1) n≤2*K (a-1) n+6) :
    run (2*k+n+2) (some (a,k,0)) =
      some (2*K (a-1) n+6-(2*k-a+3-D (a-1) n),
            2*k-a+3-D (a-1) n,0) := by
  have hstart := start_to_zero a k ha hk
  have hodd : (a-1)%2=1 := by omega
  have hlad := odd_ladder (a-1) (2*k-a+3) n hodd hlo
  have htail := odd_last_bounce (K (a-1) n)
      (2*k-a+3-D (a-1) n) (K_odd (a-1) n hodd)
      (by omega) hhi
  have hn : 2*k+n+2 = (a-1)+T (a-1) n+(2*k-a+3-D (a-1) n) := by
    have ht := time_eq_deduction_plus_n (a-1) n
    omega
  rw [hn,run_add,run_add,hstart,hlad,htail]

#print axioms odd_last_bounce
#print axioms start_to_zero
#print axioms even_section_ladder

end BB6.Agent49
