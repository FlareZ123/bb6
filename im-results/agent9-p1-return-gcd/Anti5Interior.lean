import Anti5Core
set_option maxHeartbeats 0
namespace BB6.Agent9Anti5

/-- Two-position antiperiodicity at modulus five gives a geometric
    determinant decay across each pair of chronological transitions. -/
theorem no_anti5_interior (q dir C : Int) (B L : Nat)
    (b c w x : Nat→Int)
    (hdir : dir=1∨dir= -1) (hL : 2*B+2≤L)
    (hinit : 1≤b 0 ∧ b 0≤4)
    (hx : ∀ j<L, x j=0∨x j=1)
    (hb : ∀ j<L, 2*b (j+1)=b j+5*x j)
    (hc : ∀ j<L, 2*c (j+1)=c j+(q+dir*(j:Int))*x j)
    (hw : ∀ j<L, 2*w (j+1)=w j+(q+dir*(j:Int))*(1-x j))
    (hbound : ∀ j≤L, 1≤c j ∧ c j≤C ∧ 1≤w j ∧ w j≤C)
    (hscale : 5*(C+3)<(2:Int)^(2*B)) : False := by
  obtain ⟨hbin,hflip⟩ := slope5_orbit b x L hinit hx hb
  let E : Nat→Int := fun j => 5*(c (j+2)-w j)+2*dir*b j-10*dir
  have hfour : ∀ j, j+4≤L → 4*E (j+2)=E j := by
    intro j hj
    have hcs0 := hc (j+2) (by omega)
    have hcs1 := hc (j+3) (by omega)
    have hws0 := hw j (by omega)
    have hws1 := hw (j+1) (by omega)
    have hbs0 := hb j (by omega)
    have hbs1 := hb (j+1) (by omega)
    rw [show j+2+1=j+3 by omega] at hcs0
    rw [show j+3+1=j+4 by omega] at hcs1
    rw [show j+1+1=j+2 by omega] at hws1 hbs1
    have hflip0 := hflip j (by omega)
    have hflip1 := hflip (j+1) (by omega)
    have hclock2 : q+dir*((j+2:Nat):Int)=q+dir*(j:Int)+2*dir := by
      push_cast
      simp only [Int.mul_add]
      omega
    have hclock3 : q+dir*((j+3:Nat):Int)=q+dir*(j:Int)+3*dir := by
      push_cast
      simp only [Int.mul_add]
      omega
    have hclock1 : q+dir*((j+1:Nat):Int)=q+dir*(j:Int)+dir := by
      push_cast
      simp only [Int.mul_add]
      omega
    rw [hclock2,hflip0.2.1] at hcs0
    rw [hclock3,hflip1.2.1] at hcs1
    rw [hclock1] at hws1
    have hb2 : b (j+2)=5-b j := hflip0.1
    change 4*(5*(c (j+4)-w (j+2))+2*dir*b (j+2)-10*dir) =
      5*(c (j+2)-w j)+2*dir*b j-10*dir
    rcases hdir with hd|hd <;> rcases hx j (by omega) with hbit0|hbit0 <;>
      rcases hx (j+1) (by omega) with hbit1|hbit1 <;>
      simp [hd,hbit0,hbit1] at hcs0 hcs1 hws0 hws1 hb2 ⊢ <;> omega
  have hiter : ∀ k≤B, E 0=(4:Int)^k*E (2*k) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hstep := hfour (2*k) (by omega)
      have hprior := ih (by omega)
      rw [show 2*(k+1)=2*k+2 by omega,Int.pow_succ]
      calc
        E 0 = (4:Int)^k*E (2*k) := hprior
        _ = (4:Int)^k*(4*E (2*k+2)) := by rw [hstep]
        _ = (4:Int)^k*4*E (2*k+2) := by ac_rfl
  have h0 := hbound 0 (by omega)
  have h2 := hbound 2 (by omega)
  have hinitB := hbin 0 (by omega)
  have hE : -(2:Int)^(2*B)<E 0 ∧ E 0<(2:Int)^(2*B) := by
    dsimp [E]
    rcases hdir with hd|hd <;> rw [hd] <;> omega
  have hpow : (4:Int)^B = (2:Int)^(2*B) := by
    rw [show (4:Int)=2^2 by decide,←Int.pow_mul]
  have hEB : E (2*B)=0 := by
    have he := hiter B (by omega)
    rw [hpow] at he
    have hp : 0 < (2:Int)^(2*B) := Int.pow_pos (by decide)
    by_cases hneg : E (2*B)≤0
    · by_cases heq : E (2*B)=0
      · exact heq
      · have hn : E (2*B)≤ -1 := by omega
        have hmul := Int.mul_le_mul_of_nonneg_left hn (by omega : 0≤(2:Int)^(2*B))
        rw [Int.mul_neg,Int.mul_one] at hmul
        rw [he] at hE
        omega
    · have hn : 1≤E (2*B) := by omega
      have hmul := Int.mul_le_mul_of_nonneg_left hn (by omega : 0≤(2:Int)^(2*B))
      rw [Int.mul_one] at hmul
      rw [he] at hE
      omega
  have hlast := hbin (2*B) (by omega)
  dsimp [E] at hEB
  rcases hdir with hd|hd <;> rw [hd] at hEB <;> omega

#print axioms no_anti5_interior
end BB6.Agent9Anti5
