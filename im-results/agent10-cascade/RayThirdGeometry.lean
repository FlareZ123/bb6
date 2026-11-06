import RayTwoGateExact
set_option maxHeartbeats 0
namespace CascadeRayThirdGeometry

/-- Four pure even inverse steps occur before a strict dyadic reset-image
    gap for the high-margin next odd-fork parent at scale n-4. -/
theorem four_forced_geometry (n D h w d g:Nat) (hn:20≤n)
  (hm:2048*D+16384*n+16384≤2^n)
  (hl:9*h+8*D+9*n+7=14*2^n)
  (hw:2*h=2*2^n+w+(n-2))
  (hd:2*w+5=9*d)
  (hg:4*d=8*2^(n-4)+g+(n-4)+5):
  let p:=2^(n-4)
  let e:=8*p+(n-4)
  let g1:=2*g-e
  let g2:=4*g-3*e
  let g3:=8*g-7*e
  let g4:=16*g-15*e
  (6*p-1≤g ∧ g≤8*p-3) ∧
  (6*p-1≤g1 ∧ g1≤8*p-3) ∧
  (6*p-1≤g2 ∧ g2≤8*p-3) ∧
  (6*p-1≤g3 ∧ g3≤8*p-3) ∧
  (4*p-3<g4 ∧ g4<6*p-1) ∧
  (2*g=e+g1) ∧ (2*g1=e+g2) ∧
  (2*g2=e+g3) ∧ (2*g3=e+g4) := by
  dsimp
  have hp:2^n=16*2^(n-4):=by
    have he:n=(n-4)+4:=by omega
    calc
      2^n=2^((n-4)+4):=congrArg (fun x:Nat=>2^x) he
      _=16*2^(n-4):=by rw[Nat.pow_add];omega
  have h0:6*2^(n-4)-1≤g ∧ g≤8*2^(n-4)-3:=by constructor <;> omega
  have h1:6*2^(n-4)-1≤2*g-(8*2^(n-4)+(n-4)) ∧
       2*g-(8*2^(n-4)+(n-4))≤8*2^(n-4)-3:=by constructor <;> omega
  have h2:6*2^(n-4)-1≤4*g-3*(8*2^(n-4)+(n-4)) ∧
       4*g-3*(8*2^(n-4)+(n-4))≤8*2^(n-4)-3:=by constructor <;> omega
  have h3:6*2^(n-4)-1≤8*g-7*(8*2^(n-4)+(n-4)) ∧
       8*g-7*(8*2^(n-4)+(n-4))≤8*2^(n-4)-3:=by constructor <;> omega
  have h4:4*2^(n-4)-3<16*g-15*(8*2^(n-4)+(n-4)) ∧
       16*g-15*(8*2^(n-4)+(n-4))<6*2^(n-4)-1:=by constructor <;> omega
  rcases h0 with ⟨h0a,h0b⟩
  rcases h1 with ⟨h1a,h1b⟩
  rcases h2 with ⟨h2a,h2b⟩
  rcases h3 with ⟨h3a,h3b⟩
  rcases h4 with ⟨h4a,h4b⟩
  refine ⟨⟨h0a,h0b⟩,⟨h1a,h1b⟩,⟨h2a,h2b⟩,⟨h3a,h3b⟩,⟨h4a,h4b⟩,?_,?_,?_,?_⟩
  all_goals omega

#print axioms four_forced_geometry
end CascadeRayThirdGeometry
