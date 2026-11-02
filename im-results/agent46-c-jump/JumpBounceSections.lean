import JumpOneReturn
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

theorem odd_zero_exit (k c : Nat) (hk : k%2=1) (hc : 4≤c) (hsmall : c≤2*k+6) :
    run c (some (0,k,c)) = some (2*k+6-c,c,0) := by
  have hb := odd_bounce_to_three k c hk hc (by omega)
  have hnum : c = (1+(c-3))+2 := by omega
  calc
    run c (some (0,k,c)) = run ((1+(c-3))+2) (some (0,k,c)) :=
      congrArg (fun n => run n (some (0,k,c))) hnum
    _ = run 2 (run (1+(c-3)) (some (0,k,c))) := run_add _ _ _
    _ = run 2 (some (2*k+3-(c-3),c-3,3)) := by rw [hb]
    _ = some (2*k+6-c,c,0) := by
      rw [run_three_to_zero]
      have hA : 2*k+3-(c-3) = 2*k+6-c := by omega
      have hK : c-3+3=c := by omega
      rw [hA,hK]

theorem odd_zero_continue (k c : Nat) (hk : k%2=1) (hlarge : 2*k+6<c) :
    run (2*k+4) (some (0,k,c)) = some (0,2*k+3,c-(2*k+3)) := by
  have hc : 4≤c := by omega
  have hfirst : BB6CLine.nextC (0,k,c) = some (2*k+3,0,c) := by
    obtain ⟨d,rfl⟩ : ∃ d, c=d+4 := ⟨c-4,by omega⟩
    change (if k%2=0 then some (4*(k/2)+2,2,d+1)
      else some (4*(k/2)+5,0,d+4)) = some (2*k+3,0,d+4)
    have hne : k%2≠0 := by omega
    have hd : k%2+2*(k/2)=k := Nat.mod_add_div k 2
    simp only [hne,ite_false,Option.some.injEq,Prod.mk.injEq]
    constructor
    · omega
    · trivial
  have hh := run_high (2*k+3) (2*k+3) 0 c (by omega) (by omega)
  have hnum : 2*k+4=(2*k+3)+1 := by omega
  rw [hnum]
  change run (2*k+3) ((some (0,k,c)).bind BB6CLine.nextC) = _
  simp only [Option.bind_some,hfirst]
  rw [hh]
  simp [Nat.sub_self, Nat.zero_add]

theorem even_zero_exit (k c : Nat) (hk : k%2=0) (hc : 6≤c) (hsmall : c≤2*k+8) :
    run (c-3) (some (0,k,c)) = some (2*k+8-c,c-1,0) := by
  have hb := even_bounce_to_three k c hk hc (by omega)
  have hnum : c-3=(1+(c-6))+2 := by omega
  rw [hnum,run_add,hb,run_three_to_zero]
  have hA : 2*k+2-(c-6) = 2*k+8-c := by omega
  have hK : 2+(c-6)+3=c-1 := by omega
  rw [hA,hK]

theorem even_zero_continue (k c : Nat) (hk : k%2=0) (hlarge : 2*k+8<c) :
    run (2*k+3) (some (0,k,c)) = some (0,2*k+4,c-(2*k+5)) := by
  have hc : 4≤c := by omega
  have hfirst : BB6CLine.nextC (0,k,c) = some (2*k+2,2,c-3) := by
    obtain ⟨d,rfl⟩ : ∃ d, c=d+4 := ⟨c-4,by omega⟩
    change (if k%2=0 then some (4*(k/2)+2,2,d+1)
      else some (4*(k/2)+5,0,d+4)) = some (2*k+2,2,(d+4)-3)
    have hd : k%2+2*(k/2)=k := Nat.mod_add_div k 2
    simp only [hk,ite_true,Option.some.injEq,Prod.mk.injEq]
    constructor
    · omega
    · constructor
      · trivial
      · omega
  have hh := run_high (2*k+2) (2*k+2) 2 (c-3) (by omega) (by omega)
  have hnum : 2*k+3=(2*k+2)+1 := by omega
  rw [hnum]
  change run (2*k+2) ((some (0,k,c)).bind BB6CLine.nextC) = _
  simp only [Option.bind_some,hfirst]
  rw [hh]
  simp only [Option.some.injEq,Prod.mk.injEq]
  constructor
  · omega
  · constructor
    · omega
    · omega

#print axioms odd_zero_exit
#print axioms odd_zero_continue
#print axioms even_zero_exit
#print axioms even_zero_continue
end BB6.Agent46
