import Lean

namespace BB6.Agent19ShadowGap

set_option maxHeartbeats 300000

/-- The exact direct-edge equations, including accumulated mass. -/
inductive DirectBlock (c : Nat) : Nat → Nat → Nat → Nat → Nat → Prop where
  | nil (u v : Nat) : DirectBlock c 0 u v u v
  | cons {t u v a k b l : Nat}
      (hu : a=u+v+2*c) (hv : 2*k=v+2*c)
      (tail : DirectBlock c t a k b l) :
      DirectBlock c (t+1) u v b l

theorem direct_block_mass {c t u v a k : Nat}
    (h : DirectBlock c t u v a k) :
    a+2*k=u+2*v+4*c*t := by
  induction h with
  | nil => simp
  | @cons t u v a k b l hu hv tail ih =>
    rw [ih,Nat.mul_succ]
    omega

theorem direct_block_right {c t u v a k h : Nat}
    (hb : DirectBlock c t u v a k) (hk : k=2*c+h) :
    v=2*c+2^t*h := by
  induction hb with
  | nil => simpa using hk
  | @cons t u v a k b l hu hv tail ih =>
    have he := ih hk
    rw [Nat.pow_succ,Nat.mul_right_comm (2^t) 2 h]
    omega

/-- Exact high edge followed by any number of direct edges.
    p=2^(d-1), S=u+2*v and w=v-2*c.
    o is the parity bit, not an independently chosen sign. -/
theorem high_block_identity
    (c d t u v a k b l w h : Nat)
    (hd : 2≤d)
    (hv : v=2*c+w)
    (hlo : c*((u+v)%2)≤u+v)
    (hu : 2^(d-1)*a=u+v-c*((u+v)%2)+2^(d-1)*(c*(2+(u+v)%2)))
    (hm : 2*k+a=u+2*v+c*(3*d+1))
    (hb : DirectBlock c t a k b l)
    (hl : l=2*c+h) :
    (2^(d-1)-1)*(u+2*v)+w+c*(2+(u+v)%2)+
        2^(d-1)*(c*(3*d-5-(u+v)%2)) =
      2^d*(2^t*h) ∧
    b+2*l=u+2*v+c*(3*d+1+4*t) := by
  let p := (2:Nat)^(d-1)
  let o := (u+v)%2
  have hp : 2≤p := by
    dsimp [p]
    simpa using Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (show 1≤d-1 by omega)
  have ho : o≤1 := by dsimp [o]; omega
  have hpow : 2^d=2*p := by
    calc
      2^d = 2^((d-1)+1) := congrArg (fun n : Nat => 2^n) (by omega)
      _ = 2*p := by rw [Nat.pow_succ]; exact Nat.mul_comm _ _
  have hk := direct_block_right hb hl
  have hmass := direct_block_mass hb
  constructor
  · change (p-1)*(u+2*v)+w+c*(2+o)+p*(c*(3*d-5-o))=2^d*(2^t*h)
    rw [hpow,Nat.mul_comm 2 p]
    have hA : p*a+c*o=u+v+p*(c*(2+o)) := by
      change p*a=u+v-c*o+p*(c*(2+o)) at hu
      change c*o≤u+v at hlo
      omega
    have hM : p*2*k+p*a=p*(u+2*v)+p*c*(3*d+1) := by
      have h := congrArg (p*·) hm
      rw [Nat.mul_add p (2*k) a,←Nat.mul_assoc p 2 k,
        Nat.mul_add p (u+2*v) (c*(3*d+1)),←Nat.mul_assoc p c (3*d+1)] at h
      exact h
    have hC : p*c*(3*d+1)=p*c*(3*d-5-o)+p*c*(6+o) := by
      rw [←Nat.mul_add]
      congr 1
      omega
    have hP : p*(u+2*v)=(p-1)*(u+2*v)+(u+2*v) := by
      rw [←Nat.succ_mul]
      congr 1
      omega
    have hK : p*2*k=p*2*(2*c)+p*2*(2^t*h) := by
      rw [hk,Nat.mul_add]
    have h2 : p*c*(6+o)=p*c*(2+o)+p*2*(2*c) := by
      rw [show 6+o=(2+o)+4 by omega,Nat.mul_add]
      congr 1
      grind
    rw [←Nat.mul_assoc] at hA
    rw [hP,hC,h2,hK] at hM
    rw [←Nat.mul_assoc p c (3*d-5-o)]
    have hco : c*(2+o)=2*c+c*o := by rw [Nat.mul_add,Nat.mul_comm c 2]
    omega
  · rw [hmass]
    rw [Nat.mul_add, ←Nat.mul_assoc c 4 t,Nat.mul_comm c 4]
    omega

#print axioms direct_block_mass
#print axioms direct_block_right
#print axioms high_block_identity


/-- A high/direct block with right excess at most M starts below a
    dyadic-scaled integer center, within a sharply bounded one-sided error.
    The denominator p-1 is intentional: this is a bound on the actual
    mass interval, not a modular restriction. -/
theorem scaled_interval_bracket (p c d o S w z M : Nat)
    (hp : 2≤p) (hd : 2≤d) (ho : o≤1) (hw : w≤M)
    (he : (p-1)*S+w+c*(2+o)+p*(c*(3*d-5-o))=2*p*z) :
    (p-1)*S≤2*p*z ∧
    2*p*z≤(p-1)*(S+6*c*d)+M := by
  constructor
  · omega
  · have hsub : 3*d-5-o+(2+o)≤3*d := by omega
    have h1 := Nat.mul_le_mul_left c hsub
    rw [Nat.mul_add] at h1
    have h2 := Nat.mul_le_mul_left p h1
    rw [Nat.mul_add] at h2
    have h3 : c*(2+o)≤p*(c*(2+o)) := by
      simpa using Nat.mul_le_mul_right (c*(2+o)) (show 1≤p by omega)
    have hp2 : p≤2*(p-1) := by omega
    have h4 := Nat.mul_le_mul_right (c*(3*d)) hp2
    have h5 : 2*(p-1)*(c*(3*d))=(p-1)*(6*c*d) := by grind
    rw [h5] at h4
    rw [Nat.mul_add]
    omega

/-- If the final right excess is positive, a complete direct run cannot
    consume more binary digits than the right excess available at its start. -/
theorem direct_block_cost_bound {c t u v a k h : Nat}
    (hb : DirectBlock c t u v a k) (hk : k=2*c+h) (hh : 0<h) :
    2^t≤v ∧ t≤v.log2 := by
  have he := direct_block_right hb hk
  have hm : 2^t≤2^t*h := by
    simpa using Nat.mul_le_mul_left (2^t) (show 1≤h by omega)
  have hv : 2^t≤v := by omega
  exact ⟨hv, (Nat.le_log2 (show v≠0 by have := Nat.two_pow_pos t; omega)).mpr hv⟩

#print axioms scaled_interval_bracket
#print axioms direct_block_cost_bound


/-- Integer center version of the interval bracket. -/
theorem integer_center_bounds (p c d o S w z M : Nat)
    (hp : 2≤p) (hd : 2≤d) (ho : o≤1) (hw : w≤M)
    (he : (p-1)*S+w+c*(2+o)+p*(c*(3*d-5-o))=2*p*z) :
    let center := 2*p*z/(p-1)
    S≤center ∧ center≤S+6*c*d+M/(p-1) := by
  obtain ⟨hl,hu⟩ := scaled_interval_bracket p c d o S w z M hp hd ho hw he
  have hpos : 0<p-1 := by omega
  dsimp only
  constructor
  · apply (Nat.le_div_iff_mul_le hpos).mpr
    simpa only [Nat.mul_comm S (p-1)] using hl
  · have hh := Nat.div_le_div_right (c:=p-1) hu
    rwa [Nat.mul_add_div hpos] at hh

theorem high_cost_bound (c d u v : Nat)
    (hpos : c*((u+v)%2)<u+v)
    (hdiv : 2^d∣u+v-c*((u+v)%2)) :
    2^d≤u+2*v ∧ d≤(u+2*v).log2 := by
  have hh := Nat.le_of_dvd (show 0<u+v-c*((u+v)%2) by omega) hdiv
  have hm : 2^d≤u+2*v := by omega
  exact ⟨hm,(Nat.le_log2 (show u+2*v≠0 by have := Nat.two_pow_pos d; omega)).mpr hm⟩

#print axioms integer_center_bounds
#print axioms high_cost_bound

end BB6.Agent19ShadowGap
