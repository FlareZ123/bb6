import JumpBounce
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

theorem run_add (n m : Nat) (s : Option S) :
    run (n+m) s = run m (run n s) := by
  calc
    run (n+m) s = BB6.Agent8Section.run BB6CLine.nextC (n+m) s := run_eq _ _
    _ = BB6.Agent8Section.run BB6CLine.nextC m
         (BB6.Agent8Section.run BB6CLine.nextC n s) := BB6.Agent8Section.run_add _ _ _ _
    _ = run m (run n s) := by rw [←run_eq m, ←run_eq n]

theorem start_to_zero (a k : Nat) (ha : 2≤a) (hk : a≤2*k) :
    run (a-1) (some (a,k,0)) = some (0,a-1,2*k-a+3) := by
  have hfirst : BB6CLine.nextC (a,k,0) = some (a-2,1,2*k+1) := by
    obtain ⟨u,rfl⟩ : ∃ u, a=u+2 := ⟨a-2,by omega⟩
    simp [BB6CLine.nextC]
  have hp : a-2≤a-2 := Nat.le_refl _
  have hc : a-2+3≤2*k+1 := by omega
  have hh := run_high (a-2) (a-2) 1 (2*k+1) hp hc
  have hnum : a-1=(a-2)+1 := by omega
  rw [hnum]
  change run (a-2) ((some (a,k,0)).bind BB6CLine.nextC) = _
  simp only [Option.bind_some,hfirst]
  rw [hh]
  simp only [Option.some.injEq,Prod.mk.injEq]
  constructor
  · omega
  · constructor <;> omega

theorem run_three_to_zero (a k : Nat) :
    run 2 (some (a,k,3)) = some (a,k+3,0) := by
  simp [run, BB6CLine.nextC]

theorem even_one_bounce (a k : Nat) (ha : 2≤a) (he : a%2=0)
    (hsmall : a<2*k) (hub : 2*k≤3*a+1) :
    run (2*k+2) (some (a,k,0)) =
      some (3*a+1-2*k, 2*k-a+3, 0) := by
  have hstart := start_to_zero a k ha (by omega)
  have hk : (a-1)%2=1 := by omega
  have hc : 4≤2*k-a+3 := by omega
  have hbound : (2*k-a+3)-3≤2*(a-1)+3 := by omega
  have hb := odd_bounce_to_three (a-1) (2*k-a+3) hk hc hbound
  have hmid :
      some (2*(a-1)+3-((2*k-a+3)-3), (2*k-a+3)-3, 3) =
      (some (3*a+1-2*k,2*k-a,3) : Option S) := by
    clear he hk hc hbound hstart hb
    have hA : 2*(a-1)+3-((2*k-a+3)-3) = 3*a+1-2*k := by omega
    have hK : (2*k-a+3)-3 = 2*k-a := by omega
    rw [hA, hK]
  have hnum : 2*k+2 = ((a-1)+(1+((2*k-a+3)-3)))+2 := by omega
  rw [hnum, run_add, run_add, hstart, hb, hmid, run_three_to_zero]

theorem odd_one_bounce (a k : Nat) (ha : 3≤a) (he : a%2=1)
    (hsmall : a+3≤2*k) (hub : 2*k≤3*a+3) :
    run (2*k-1) (some (a,k,0)) =
      some (3*a+3-2*k, 2*k-a+2, 0) := by
  have hstart := start_to_zero a k (by omega) (by omega)
  have hk : (a-1)%2=0 := by omega
  have hc : 6≤2*k-a+3 := by omega
  have hbound : (2*k-a+3)-6≤2*(a-1)+2 := by omega
  have hb := even_bounce_to_three (a-1) (2*k-a+3) hk hc hbound
  have hmid :
      some (2*(a-1)+2-((2*k-a+3)-6), 2+((2*k-a+3)-6), 3) =
      (some (3*a+3-2*k,2*k-a-1,3) : Option S) := by
    clear he hk hc hbound hstart hb
    have hA : 2*(a-1)+2-((2*k-a+3)-6) = 3*a+3-2*k := by omega
    have hK : 2+((2*k-a+3)-6) = 2*k-a-1 := by omega
    rw [hA, hK]
  have hnum : 2*k-1 = ((a-1)+(1+((2*k-a+3)-6)))+2 := by omega
  rw [hnum, run_add, run_add, hstart, hb, hmid, run_three_to_zero]
  exact congrArg (fun x : Nat => (some (3*a+3-2*k,x,0) : Option S)) (by omega)

theorem odd_boundary (k : Nat) (hk : 2≤k) :
    run (2*k) (some (2*k-1,k,0)) = some (4*k-2,3,0) := by
  have hp := start_to_zero (2*k-1) k (by omega) (by omega)
  have hpre : 2*k-1-1 = 2*k-2 := by omega
  rw [hpre] at hp
  have he : (2*k-2)%2=0 := by omega
  have hdiv : (2*k-2)%2 + 2*((2*k-2)/2) = 2*k-2 :=
    Nat.mod_add_div (2*k-2) 2
  have hb : BB6CLine.nextC (0,2*k-2,4) = some (4*k-2,2,1) := by
    change (if (2*k-2)%2=0 then some (4*((2*k-2)/2)+2,2,1)
      else some (4*((2*k-2)/2)+5,0,4)) = some (4*k-2,2,1)
    simp only [he, ite_true,Option.some.injEq,Prod.mk.injEq]
    constructor
    · omega
    · trivial
  have hlast : run 2 (some (0,2*k-2,4)) = some (4*k-2,3,0) := by
    change run 1 ((some (0,2*k-2,4)).bind BB6CLine.nextC) = _
    simp only [Option.bind_some,hb]
    simp [run,BB6CLine.nextC]
  have hn : 2*k = (2*k-2)+2 := by omega
  rw [hn, run_add]
  have hs : 2*k-2+2-1=2*k-1 := by omega
  rw [hs, hp]
  have hfour : 2*k-(2*k-1)+3=4 := by omega
  rw [hfour, hlast]

#print axioms odd_boundary
#print axioms even_one_bounce
#print axioms odd_one_bounce
#print axioms start_to_zero
#print axioms run_add
end BB6.Agent46
