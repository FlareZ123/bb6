import Counted421ClosedCost

namespace Counted421

theorem regular_le {r c : Nat} (hr : r≤c) : regularCost r c≤20*c*c+80*c+78 := by
  obtain ⟨d,rfl⟩ : ∃ d, c=r+d := ⟨c-r,by omega⟩
  have h : regularCost r (r+d)+d*(32*r+20*d+66)=20*(r+d)*(r+d)+80*(r+d)+78 := by
    unfold regularCost
    rw [Nat.add_sub_cancel_left]
    poly
  omega

theorem band_score_le (i r : Nat) (hr : r≤Cap.c i+2) : score (Cap.lo i+r)≤600*4^i := by
  have hc := Cap.c_add i
  have hp := Cap.pow_lower i
  have hp4 : 2^i≤4^i := Nat.pow_le_pow_left (by decide) _
  have hR := resetPrefix_closed i
  have hR' : resetPrefix i≤42*4^i := by omega
  have hs : (Cap.c i+4)*(Cap.c i+4)=25*4^i := by
    rw [hc]
    calc
      5*2^i*(5*2^i)=(5*5)*(2^i*2^i) := by ac_rfl
      _=25*4^i := by rw [←Nat.mul_pow]
  have hm : 20*Cap.c i*Cap.c i+80*Cap.c i+78+400*2^i=500*4^i+78 := by poly
  have hmax : 20*Cap.c i*Cap.c i+80*Cap.c i+78≤500*4^i := by omega
  have hcpos : 0<Cap.c i := by omega
  have hd : fastD r (Cap.c i)≤20*Cap.c i*Cap.c i+80*Cap.c i+78 := by
    rw [fastD]
    by_cases h : r≤Cap.c i
    · rw [ite_eq_left h]; exact regular_le h
    · rw [ite_eq_right h]
      by_cases h1 : r=Cap.c i+1
      · rw [ite_eq_left h1]; unfold terminalCost; poly
      · have h2 : r=Cap.c i+2 := by omega
        rw [ite_eq_right h1,ite_eq_left h2]; unfold specialCost; poly
  rw [score_band]
  omega

def q (i r : Nat) := 2*r+i+6

def bandBudget (i : Nat) := (i+5)*(600*4^i)
def bandPrefix : Nat → Nat
  | 0 => 0
  | i+1 => bandPrefix i+bandBudget i

def potential (i r : Nat) := bandPrefix i+(Nat.log2 (q i r)+1)*(600*4^i)

theorem log_upper (i r : Nat) (hr : r≤Cap.c i+2) : Nat.log2 (q i r)≤i+3 := by
  have hc := Cap.c_add i
  have hp := Cap.pow_lower i
  have h : q i r<2^(i+4) := by
    rw [Nat.pow_add]; unfold q; simp; omega
  have hz : q i r≠0 := by unfold q; omega
  have hh := (Nat.log2_lt hz).mpr h
  omega

theorem log_grows (i r s : Nat) (h : s=3*r+i+6) : Nat.log2 (q i r)+1≤Nat.log2 (q i s) := by
  have hz : q i r≠0 := by unfold q; omega
  have hz' : q i s≠0 := by unfold q; omega
  have hh := (Nat.le_log2 hz).mp (Nat.le_refl (Nat.log2 (q i r)))
  have hq : q i s=3*q i r := by unfold q; omega
  apply (Nat.le_log2 hz').mpr
  rw [Nat.pow_succ,hq]
  omega

theorem prefix_mono {i j : Nat} (h : i≤j) : bandPrefix i≤bandPrefix j := by
  induction j with
  | zero =>
    have he : i=0 := by omega
    subst i
    exact Nat.le_refl _
  | succ j ih =>
    by_cases e : i=j+1
    · simp [e]
    · rw [bandPrefix]; have := ih (by omega); omega

theorem potential_end (i r : Nat) (hr : r≤Cap.c i+2) :
    potential i r+score (Cap.lo i+r)≤bandPrefix (i+1) := by
  have h := band_score_le i r hr
  have hl := log_upper i r hr
  have hm := Nat.mul_le_mul_right (600*4^i) (show Nat.log2 (q i r)+1+1≤i+5 by omega)
  rw [Nat.add_mul,Nat.one_mul] at hm
  unfold potential
  rw [bandPrefix,bandBudget]
  omega

theorem potential_edge {i j r s : Nat} (hr : r≤Cap.c i+2) (hs : s≤Cap.c j+2)
    (e : Cap.Edge (Cap.lo i+r) (Cap.lo j+s)) :
    potential i r+score (Cap.lo i+r)≤potential j s := by
  have hg := Cap.edge_grows e
  have hi : i≤j := by
    by_cases h : i≤j
    · exact h
    · have hle : Cap.lo (j+1)≤Cap.lo i := by
        by_cases he : j+1=i
        · simp [he]
        · exact Nat.le_of_lt (Cap.lo_strict (by omega))
      rw [Cap.lo_step] at hle
      omega
  by_cases hij : i=j
  · subst j
    have hreg : r≤Cap.c i := by
      by_cases h : r≤Cap.c i
      · exact h
      · have he := Cap.edge_iff.mp e
        rw [Cap.f_band] at he
        rw [ite_eq_right h] at he
        by_cases ht : r=Cap.c i+1
        · simp [ht] at he
        · have hh : r=Cap.c i+2 := by omega
          simp [hh] at he
          have := Cap.lo_c i
          omega
    have h := (Cap.same_band_regular i r s hreg).mp e
    have hl := log_grows i r s h
    have hb := band_score_le i r hr
    have hm := Nat.mul_le_mul_right (600*4^i) (show Nat.log2 (q i r)+1+1≤Nat.log2 (q i s)+1 by omega)
    rw [Nat.add_mul,Nat.one_mul] at hm
    unfold potential
    omega
  · have h1 := potential_end i r hr
    have h2 := prefix_mono (show i+1≤j by omega)
    unfold potential at h1 ⊢
    omega

theorem arrival_potential {x : Nat} (hr : Cap.Reach 2 x) : ∀ i r, x=Cap.lo i+r → r≤Cap.c i+2 → arrivalCost x≤potential i r := by
  induction hr with
  | refl => intro i r _ _; rw [arrival_two]; omega
  | @tail x y h e ih =>
    intro j s hy hs
    obtain ⟨i,hlo,hhi⟩ := Cap.band_exists x (Cap.reach_le h)
    let r := x-Cap.lo i
    have hx : x=Cap.lo i+r := by dsimp [r]; omega
    have hr' : r≤Cap.c i+2 := by rw [Cap.lo_step] at hhi; dsimp [r]; omega
    have hp := ih i r hx hr'
    have he : Cap.Edge (Cap.lo i+r) (Cap.lo j+s) := by rw [←hx,←hy]; exact e
    have hb := potential_edge hr' hs he
    rw [←hx] at hb
    rw [arrival_edge e]
    omega

theorem bandPrefix_bound (i : Nat) : bandPrefix (i+1)≤800*(i+5)*4^i := by
  induction i with
  | zero => decide
  | succ i ih =>
    rw [bandPrefix,bandBudget,Nat.pow_succ]
    have hbase : 800*(i+5)*4^i≤800*(i+6)*4^i := Nat.mul_le_mul_right _ (by omega)
    rw [show i+1+5=i+6 by omega]
    have h1 : (i+6)*(600*(4^i*4)) = 2400*((i+6)*4^i) := by
      calc _ = (600*4)*((i+6)*4^i) := by ac_rfl
           _ = _ := rfl
    have h2 : 800*(i+6)*4^i=800*((i+6)*4^i) := Nat.mul_assoc ..
    have h3 : 800*(i+6)*(4^i*4)=3200*((i+6)*4^i) := by
      calc _ = (800*4)*((i+6)*4^i) := by ac_rfl
           _ = _ := rfl
    rw [h1,h3]
    rw [h2] at hbase
    omega

theorem halt_score_bound_sharp (n : Nat) (h : Exact ⟨.A,0,0⟩ n none) :
    ∃ i, Cap.rootOf (Cap.halt i)=2 ∧ n≤8+800*(i+5)*4^i := by
  obtain ⟨i,hr,hn⟩ := (exact_blank_iff n).mp h
  refine ⟨i,hr,?_⟩
  have he : Cap.halt i=Cap.lo i+(Cap.c i+1) := by unfold Cap.halt; omega
  have hp := arrival_potential ((Cap.root_iff_reach _).mp hr) i (Cap.c i+1) he (by omega)
  have hb := potential_end i (Cap.c i+1) (by omega)
  rw [←he] at hb
  have hf := bandPrefix_bound i
  omega

#print axioms band_score_le
#print axioms potential_edge
#print axioms halt_score_bound_sharp
end Counted421
