import PeriodWordBounds
import PeriodPrimitive
import PeriodSecondary

namespace PeriodWord

/-- The depth word obtained by repeating a finite block. -/
def repeatWord (u : List Nat) : Nat → List Nat
  | 0 => []
  | k+1 => u ++ repeatWord u k

/-- Finite binary geometric sum. -/
def geomN (a : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => 1 + a * geomN a k

/-- Decode the marker whose highest set bit is at position n-1. -/
def decodeAt : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, q =>
      if q % 2 = 1 then 0 :: decodeAt n (q / 2)
      else
        match decodeAt n (q / 2) with
        | [] => []
        | t :: ts => (t+1) :: ts

theorem decodeAt_spec (n q : Nat) (hn : 0 < n)
    (hlo : 2^(n-1) ≤ q) (hhi : q < 2^n) :
    cost (decodeAt n q) = n ∧ weight (decodeAt n q) = q := by
  induction n generalizing q with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        have hq : q = 1 := by omega
        subst q
        simp [decodeAt, cost, weight]
      · have hnpos : 0 < n := by omega
        have hpow : 2^(n-1) * 2 = 2^n := by
          have he : n-1+1=n := Nat.sub_add_cancel hnpos
          calc
            2^(n-1)*2 = 2^(n-1+1) := by rw [Nat.pow_succ]
            _ = 2^n := by rw [he]
        have hlo' : 2^(n-1) ≤ q/2 := by
          rw [Nat.le_div_iff_mul_le (by decide : 0<2)]
          calc
            2^(n-1)*2 = 2^n := hpow
            _ ≤ q := by simpa using hlo
        have hhi' : q/2 < 2^n := by
          rw [Nat.div_lt_iff_lt_mul (by decide : 0<2)]
          calc
            q < 2^(n+1) := hhi
            _ = 2^n*2 := by rw [Nat.pow_succ]
        have hsmall : 0 < n := hnpos
        by_cases hodd : q%2=1
        · have hdiv : q = 2*(q/2)+1 := by
            have h := Nat.mod_add_div q 2
            omega
          have hs := ih (q/2) hsmall hlo' hhi'
          constructor
          · simp [decodeAt, hodd, cost, hs.1]
            omega
          · simp [decodeAt, hodd, weight, hs.2]
            omega
        · have heven : q%2=0 := by omega
          have hdiv : q = 2*(q/2) := by
            have h := Nat.mod_add_div q 2
            omega
          have hs := ih (q/2) hsmall hlo' hhi'
          cases htail : decodeAt n (q/2) with
          | nil =>
              simp [htail, cost, weight] at hs
              omega
          | cons t ts =>
              have hcost : t+1+cost ts=n := by simpa [htail, cost] using hs.1
              have hweight2 : 2^t + 2^(t+1)*weight ts = q/2 := by
                simpa [htail, weight] using hs.2
              constructor
              · simp [decodeAt, heven, htail, cost]
                omega
              · simp [decodeAt, heven, htail, weight]
                rw [Nat.pow_succ, Nat.pow_succ]
                have hmult := congrArg (fun x : Nat => 2*x) hweight2
                calc
                  2^t*2 + 2^(t+1)*2*weight ts = 2*2^t + 2*(2^(t+1)*weight ts) := by ac_rfl
                  _ = 2*(2^t+2^(t+1)*weight ts) := by rw [← Nat.mul_add]
                  _ = 2*(q/2) := hmult
                  _ = q := hdiv.symm

theorem decodeAt_cost_weight : ∀ n w, cost w = n → decodeAt n (weight w) = w := by
  intro n
  refine Nat.strongRecOn n (fun n ih => ?_)
  intro w hcost
  cases w with
  | nil =>
      simp [cost, weight] at hcost
      subst n
      simp [decodeAt]
  | cons t ts =>
      have hcostOrig : cost (t::ts)=n := hcost
      simp only [cost] at hcost
      by_cases ht : t=0
      · subst t
        have hsmall : cost ts < n := by omega
        have ih' := ih (cost ts) hsmall ts rfl
        have hcostCons : cost (0::ts)=cost ts+1 := by simp [cost]; omega
        have hweightCons : weight (0::ts)=2*weight ts+1 := by simp [weight]; omega
        have hmod : (2*weight ts+1)%2=1 := by simp
        have hdiv : (2*weight ts+1)/2=weight ts := by
          have h := Nat.mod_add_div (2*weight ts+1) 2
          rw [hmod] at h
          omega
        rw [← hcostOrig, hcostCons, hweightCons]
        simp [decodeAt, hmod, hdiv, ih']
      · have htpos : 0<t := by omega
        let v : List Nat := (t-1)::ts
        have hcostv : cost v + 1 = n := by simp [v, cost]; omega
        have hsmall : cost v < n := by omega
        have ih' := ih (cost v) hsmall v rfl
        have hweightv : weight (t::ts)=2*weight v := by
          simp only [weight, v]
          have htv : t-1+1=t := Nat.sub_add_cancel htpos
          have hp1 : 2^t = 2^(t-1)*2 := by
            calc
              2^t = 2^(t-1+1) := by congr 1; omega
              _ = 2^(t-1)*2 := by rw [Nat.pow_succ]
          have hp2 : 2^(t+1) = 2^t*2 := by rw [Nat.pow_succ]
          rw [htv, hp1, hp2]
          calc
            2^(t-1)*2 + 2^t*2*weight ts = 2*2^(t-1) + 2*(2^t*weight ts) := by ac_rfl
            _ = 2*(2^(t-1)+2^t*weight ts) := by rw [← Nat.mul_add]
            _ = 2*(2^(t-1)+2^(t-1)*2*weight ts) := by rw [hp1]
        have hmod : weight (t::ts)%2=0 := by rw [hweightv]; simp
        have hdiv : weight (t::ts)/2=weight v := by rw [hweightv]; simp
        have hcostEq : cost (t::ts)=cost v+1 := by simp [v, cost]; omega
        rw [← hcostOrig, hcostEq]
        change decodeAt (cost v+1) (weight (t::ts)) = t::ts
        simp only [decodeAt, hmod, hdiv, ih']
        simp [v]
        omega

theorem cost_append (u v : List Nat) : cost (u++v)=cost u+cost v := by
  induction u with
  | nil => simp [cost]
  | cons t ts ih => simp [cost, ih, Nat.add_assoc]

theorem weight_append (u v : List Nat) :
    weight (u++v)=weight u+2^(cost u)*weight v := by
  induction u with
  | nil => simp [weight, cost]
  | cons t ts ih =>
      simp only [List.cons_append, weight, cost]
      rw [ih]
      simp only [Nat.pow_add, Nat.mul_add]
      ac_rfl

theorem cost_repeat (u : List Nat) (k : Nat) :
    cost (repeatWord u k)=cost u*k := by
  induction k with
  | zero => simp [repeatWord, cost]
  | succ k ih =>
      rw [repeatWord, cost_append, ih, Nat.mul_succ]
      omega

theorem weight_repeat (u : List Nat) (k : Nat) :
    weight (repeatWord u k)=weight u*geomN (2^(cost u)) k := by
  induction k with
  | zero => simp [repeatWord, weight, geomN]
  | succ k ih =>
      rw [repeatWord, weight_append, ih, geomN]
      simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem geomN_identity (a k : Nat) (ha : 0<a) :
    (a-1)*geomN a k = a^k-1 := by
  induction k with
  | zero => simp [geomN]
  | succ k ih =>
      simp only [geomN, Nat.pow_succ]
      calc
        (a-1)*(1+a*geomN a k) = (a-1)+a*((a-1)*geomN a k) := by
          rw [Nat.mul_add]
          simp only [Nat.mul_one]
          congr 1
          calc
            (a-1)*(a*geomN a k) = (a-1)*a*geomN a k := by rw [Nat.mul_assoc]
            _ = a*(a-1)*geomN a k := by ac_rfl
            _ = a*((a-1)*geomN a k) := by rw [Nat.mul_assoc]
        _ = (a-1)+a*(a^k-1) := by rw [ih]
        _ = a*a^k-1 := by
          rw [Nat.mul_sub_left_distrib]
          have hp : 1≤a^k := Nat.one_le_pow k a ha
          have hm : a≤a*a^k := by
            have h := Nat.mul_le_mul_left a hp
            simpa using h
          omega
        _ = a^(k+1)-1 := by rw [Nat.pow_succ]; ac_rfl

theorem weight_lower (w : List Nat) (hne : w ≠ []) :
    2^(cost w-1) ≤ weight w := by
  cases w with
  | nil => contradiction
  | cons t ts =>
      cases ts with
      | nil => simp [cost, weight]
      | cons s ss =>
          have htail : 2^(cost (s::ss)-1) ≤ weight (s::ss) :=
            weight_lower (s::ss) (by simp)
          have hexp : cost (t::s::ss)-1 = t+cost (s::ss) := by
            simp [cost]
          rw [hexp]
          have htailcost : 0<cost (s::ss) := by simp [cost]; omega
          have hp : 2^(t+cost (s::ss)) = 2^(t+1)*2^(cost (s::ss)-1) := by
            rw [← Nat.pow_add]
            congr 1
            omega
          rw [hp]
          have hmul := Nat.mul_le_mul_left (2^(t+1)) htail
          calc
            2^(t+1)*2^(cost (s::ss)-1) ≤ 2^(t+1)*weight (s::ss) := hmul
            _ ≤ 2^t+2^(t+1)*weight (s::ss) := Nat.le_add_left _ _

theorem factor_word_of_rotation_period (w : List Nat) (d : Nat)
    (hdpos : 0<d) (hdlt : d<cost w)
    (hdvd : d ∣ cost w)
    (hHlt : weight w < 2^(cost w)-1)
    (hrot : (2^d*weight w)%(2^(cost w)-1)=weight w) :
    ∃ u k, 0<k ∧ cost u=d ∧ weight u<2^d-1 ∧ w=repeatWord u k := by
  rcases hdvd with ⟨k,hkS⟩
  have hSpos : 0<cost w := Nat.lt_trans hdpos hdlt
  have hkpos : 0<k := by
    by_cases hk0 : k=0
    · rw [hkS, hk0] at hdlt
      omega
    · omega
  have hne : w≠[] := by
    intro h
    subst w
    simp [cost] at hSpos
  have hHpos : 0<weight w := by
    cases w with
    | nil => contradiction
    | cons t ts =>
        simp only [weight]
        exact Nat.lt_of_lt_of_le (Nat.pow_pos (by decide : 0<2)) (Nat.le_add_right _ _)
  have hHlower : 2^(cost w-1)≤weight w := weight_lower w hne
  let A : Nat := 2^d
  let B : Nat := 2^(cost w)-1
  let H : Nat := weight w
  let J : Nat := geomN A k
  let q : Nat := (A*H)/B
  have hApos : 0<A := by exact Nat.pow_pos (by decide : 0<2)
  have hmod : (A*H)%B=H := by simpa [A,B,H] using hrot
  have hquot : A*H=H+B*q := by
    have h := Nat.mod_add_div (A*H) B
    rw [hmod] at h
    change H+B*q=A*H at h
    omega
  have hdivEq : (A-1)*H=B*q := by
    calc
      (A-1)*H=A*H-H := by rw [Nat.sub_mul]; simp
      _=B*q := by omega
  have hApow : A^k=2^(cost w) := by
    dsimp [A]
    calc
      (2^d)^k=2^(d*k) := (Nat.pow_mul 2 d k).symm
      _=2^(cost w) := by rw [← hkS]
  have hJid : (A-1)*J=B := by
    calc
      (A-1)*J=A^k-1 := geomN_identity A k hApos
      _=B := by simp [B,hApow]
  have hJpos : 0<J := by
    cases k with
    | zero => omega
    | succ k =>
        change 0<1+A*geomN A k
        omega
  have hmul : (A-1)*H=(A-1)*(J*q) := by
    calc
      (A-1)*H=B*q := hdivEq
      _=((A-1)*J)*q := by rw [hJid]
      _=(A-1)*(J*q) := by ac_rfl
  have hHmul : H=J*q := Nat.eq_of_mul_eq_mul_left (by omega) hmul
  have hqpos : 0<q := by
    have hqne : q≠0 := by
      intro hq0
      rw [hq0] at hHmul
      simp at hHmul
      omega
    exact Nat.pos_of_ne_zero hqne
  have hqhi : q<A-1 := by
    by_cases hqge : A-1≤q
    · have hmulq := Nat.mul_le_mul_left J hqge
      have hB_le_H : B≤H := by
        calc
          B=(A-1)*J := hJid.symm
          _=J*(A-1) := by ac_rfl
          _≤J*q := hmulq
          _=H := hHmul.symm
      have hHlt' : H<B := by simpa [H] using hHlt
      omega
    · omega
  have hAd : A=2^(d-1)*2 := by
    dsimp [A]
    have he : d-1+1=d := Nat.sub_add_cancel hdpos
    calc
      2^d=2^(d-1+1) := by congr 1; omega
      _=2^(d-1)*2 := by rw [Nat.pow_succ]
  have hcoeff : 2*(2^(d-1)-1)<A-1 := by omega
  have hprod : 2*(J*(2^(d-1)-1))<2^(cost w) := by
    have hmulc := Nat.mul_lt_mul_of_pos_left hcoeff hJpos
    calc
      2*(J*(2^(d-1)-1))=J*(2*(2^(d-1)-1)) := by ac_rfl
      _<J*(A-1) := hmulc
      _=2^(cost w)-1 := by
        calc
          J*(A-1)=(A-1)*J := by ac_rfl
          _=B := hJid
          _=2^(cost w)-1 := rfl
      _<2^(cost w) := by omega
  have hqlo : 2^(d-1)≤q := by
    by_cases hqsmall : q<2^(d-1)
    · have hqle : q≤2^(d-1)-1 := by omega
      have hHle : H≤J*(2^(d-1)-1) := by
        calc H=J*q := hHmul
             _≤J*(2^(d-1)-1) := Nat.mul_le_mul_left J hqle
      have htwice : 2*H≤2*(J*(2^(d-1)-1)) := Nat.mul_le_mul_left 2 hHle
      have hpowS : 2^(cost w-1)*2=2^(cost w) := by
        have he : cost w-1+1=cost w := Nat.sub_add_cancel hSpos
        calc
          2^(cost w-1)*2=2^(cost w-1+1) := by rw [Nat.pow_succ]
          _=2^(cost w) := by rw [he]
      have hHlower2 : 2^(cost w)≤2*H := by
        calc
          2^(cost w)=2^(cost w-1)*2 := hpowS.symm
          _≤2*H := by simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hHlower
      omega
    · omega
  have hqhi2 : q<2^d := by
    exact Nat.lt_of_lt_of_le hqhi (Nat.sub_le A 1)
  let u : List Nat := decodeAt d q
  have hdecode := decodeAt_spec d q hdpos hqlo hqhi2
  have hcostU : cost u=d := by simpa [u] using hdecode.1
  have hweightU : weight u=q := by simpa [u] using hdecode.2
  have hcostR : cost (repeatWord u k)=cost w := by
    rw [cost_repeat,hcostU,hkS]
  have hweightR : weight (repeatWord u k)=weight w := by
    calc
      weight (repeatWord u k)=weight u*geomN (2^(cost u)) k := weight_repeat u k
      _=q*J := by simp [hcostU,hweightU,J,A]
      _=H := by rw [hHmul]; ac_rfl
  have hwd : decodeAt (cost w) (weight w)=w := decodeAt_cost_weight (cost w) w rfl
  have hrd : decodeAt (cost (repeatWord u k)) (weight (repeatWord u k))=repeatWord u k :=
    decodeAt_cost_weight (cost (repeatWord u k)) (repeatWord u k) rfl
  rw [hcostR,hweightR,hwd] at hrd
  refine ⟨u,k,hkpos,hcostU,?_,hrd⟩
  simpa [hweightU,A] using hqhi



/-- Exact offset under concatenation; the second block is translated by the
    cost of the first block. -/
theorem offset_append (u v : List Nat) :
    offset (u++v)=offset u+(2^(cost u):Int)*(offset v+(cost u:Int)*(weight v:Int)) := by
  induction u with
  | nil => simp [offset, cost]
  | cons t ts ih =>
      simp only [List.cons_append, offset, cost]
      rw [weight_append, ih]
      simp only [Nat.pow_add, Int.natCast_add, Int.natCast_mul, Int.natCast_pow]
      grind

theorem weight_repeat_int (u : List Nat) (k : Nat) :
    (weight (repeatWord u k):Int)=(weight u:Int)*PeriodSecondary.geom (2^(cost u):Int) k := by
  induction k with
  | zero => simp [repeatWord, weight, PeriodSecondary.geom]
  | succ k ih =>
      rw [repeatWord]
      have hw := congrArg (fun n : Nat => (n:Int)) (weight_append u (repeatWord u k))
      simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow] at hw
      rw [hw, ih]
      simp [PeriodSecondary.geom, Int.mul_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

/-- Repetition has the exact affine offset coefficient used by
    PeriodSecondary.repeated_affine_obstruction. -/
theorem offset_repeat (u : List Nat) (k : Nat) :
    offset (repeatWord u k)=offset u*PeriodSecondary.geom (2^(cost u):Int) k +
      (weight u:Int)*(cost u:Int)*PeriodSecondary.weighted (2^(cost u):Int) k := by
  induction k with
  | zero => simp [repeatWord, offset, PeriodSecondary.geom, PeriodSecondary.weighted]
  | succ k ih =>
      rw [repeatWord, offset_append, ih, weight_repeat_int]
      simp only [PeriodSecondary.geom, PeriodSecondary.weighted, Int.mul_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      grind

#print axioms factor_word_of_rotation_period
#print axioms weight_repeat_int
#print axioms offset_repeat



/-- The original scalar run recurrence, with the exact affine coefficients
    exposed for every block index. -/
theorem periodic_run_affine_recurrence (L w : Nat) (m z : Nat → Nat)
    (hr : ∀ n, Run L w (m n) (z n) (m (n+1)) (z (n+1))) :
    ∀ n, ((2:Nat)^(cost w):Int)*(z (n+1):Int) =
      (z n:Int)+(weight w:Int)*((L:Int)+(m 0:Int))+
        ((weight w:Int)*(cost w:Int))*(n:Int)+offset w := by
  have hm : ∀ n, m (n+1)=m n+cost w := by
    intro n
    exact run_cost L w (m n) (z n) (m (n+1)) (z (n+1)) (hr n)
  have hline := linear_cost_orbit w m hm
  intro n
  have hb := block_affine L w (m n) (z n) (m (n+1)) (z (n+1)) (hr n)
  rw [hline n] at hb
  simp only [Int.natCast_add, Int.natCast_mul] at hb
  grind

/-- The increment between the first two output boundaries is the unique
    affine slope forced by an infinite fixed-word run. -/
theorem periodic_run_slope_at_zero (L w : Nat) (hw : 0<cost w)
    (m z : Nat → Nat)
    (hr : ∀ n, Run L w (m n) (z n) (m (n+1)) (z (n+1))) :
    (((2:Nat)^(cost w):Int)-1)*((z 1:Int)-(z 0:Int)) =
      (weight w:Int)*(cost w:Int) := by
  let A : Nat := 2^(cost w)
  let zi : Nat → Int := fun n => (z n:Int)
  let H : Int := (weight w:Int)
  let S : Int := (cost w:Int)
  let X : Int := (L:Int)+(m 0:Int)
  let D : Int := offset w
  have hA : 2≤A := by
    dsimp [A]
    have h := Nat.one_lt_two_pow (Nat.ne_of_gt hw)
    omega
  have hrec : ∀ n, (A:Int)*zi (n+1)=zi n+H*X+(H*S)*(n:Int)+D := by
    simpa [A,zi,H,S,X,D] using periodic_run_affine_recurrence L w m z hr
  let delta : Nat → Int := fun n => zi (n+1)-zi n
  let err : Nat → Int := fun n => ((A:Int)-1)*delta n-H*S
  have hdiff := PeriodCore.affine_difference (A:Int) H S X D zi hrec
  have herr : ∀ n, err n=(A:Int)*err (n+1) := by
    intro n
    have hd : (A:Int)*delta (n+1)=delta n+H*S := by
      simpa only [delta, show n+1+1=n+2 by omega] using hdiff n
    have hmul := congrArg (fun x : Int => ((A:Int)-1)*x) hd
    have hx : (A:Int)*(((A:Int)-1)*delta (n+1)) =
        ((A:Int)-1)*delta n+((A:Int)-1)*(H*S) := by
      calc
        (A:Int)*(((A:Int)-1)*delta (n+1)) =
            ((A:Int)-1)*((A:Int)*delta (n+1)) := by
              simp only [Int.mul_left_comm]
        _ = ((A:Int)-1)*delta n+((A:Int)-1)*(H*S) := by
              simpa only [Int.mul_add] using hmul
    have hs : ((A:Int)-1)*(H*S)=(A:Int)*(H*S)-H*S := by
      rw [Int.sub_mul]
      simp
    change ((A:Int)-1)*delta n-H*S =
      (A:Int)*(((A:Int)-1)*delta (n+1)-H*S)
    rw [hs] at hx
    calc
      _ = (A:Int)*(((A:Int)-1)*delta (n+1))-(A:Int)*(H*S) := by omega
      _ = _ := by exact (Int.mul_sub _ _ _).symm
  have hz := PeriodCore.forced_zero A hA err herr
  dsimp [err,delta,zi,A] at hz
  omega

#print axioms periodic_run_affine_recurrence
#print axioms periodic_run_slope_at_zero



/-- An infinite run of a repeated primitive depth block is impossible by
    the exact repeated affine coefficients and the primitive obstruction. -/
theorem no_infinite_repeated_word_ray (L : Nat) (u : List Nat) (k : Nat)
    (hkpos : 0<k) (hp : ∃ t ∈ u, 0<t) (hprim : Primitive u)
    (m z : Nat → Nat)
    (hr : ∀ n, Run L (repeatWord u k) (m n) (z n) (m (n+1)) (z (n+1))) : False := by
  let w : List Nat := repeatWord u k
  have hcostu : 0<cost u := by
    have h := positive_depth_cost u hp
    omega
  have hwcost : 0<cost w := by
    rw [w, cost_repeat]
    exact Nat.mul_pos hcostu hkpos
  let a : Int := (2^(cost u):Nat)
  let h : Int := (weight u:Nat)
  let r : Int := (cost u:Nat)
  let T : Nat := k
  let J : Int := PeriodSecondary.geom a T
  let A : Int := (2^(cost w):Nat)
  let H : Int := (weight w:Nat)
  let S : Int := (cost w:Nat)
  let D : Int := offset w
  let Q : Int := (z 1:Int)-(z 0:Int)
  let X : Int := (L:Int)+(m 0:Int)
  let Z : Int := (z 0:Int)
  have hJ : J=PeriodSecondary.geom a T := rfl
  have hA : A=a^T := by
    dsimp [A,a,T]
    rw [cost_repeat]
    rw [← Int.natCast_pow, Nat.pow_mul]
  have hH : H=h*J := by
    simpa [H,h,J,a,T,w] using weight_repeat_int u k
  have hS : S=r*(T:Int) := by
    dsimp [S,r,T,w]
    have hc := congrArg (fun n : Nat => (n:Int)) (cost_repeat u k)
    simpa using hc
  have hD : D=offset u*J+h*r*PeriodSecondary.weighted a T := by
    simpa [D,h,r,J,a,T,w] using offset_repeat u k
  have hB : A-1=(a-1)*J := by
    rw [hA,hJ]
    exact (PeriodSecondary.geom_identity a T).symm
  have ha : 0<a := by
    dsimp [a]
    exact Int.ofNat_pos.mpr (Nat.pow_pos (by decide : 0<2))
  have hgeom_nonneg : ∀ n, 0≤PeriodSecondary.geom a n := by
    intro n
    induction n with
    | zero => simp [PeriodSecondary.geom]
    | succ n ih =>
        simp [PeriodSecondary.geom]
        omega
  have hJpos : 0<J := by
    cases k with
    | zero => omega
    | succ k =>
        change 0<1+a*PeriodSecondary.geom a k
        have hg := hgeom_nonneg k
        omega
  have hbase : ¬(a-1) ∣ h*r := by
    intro hdiv
    rcases hdiv with ⟨q,hq⟩
    have hd : ((2^(cost u):Nat):Int)-1*q =
        (weight u:Int)*(cost u:Int) := by
      simpa [a,h,r] using hq.symm
    exact primitive_no_integral_slope u hp hprim q hd
  have hSlope : (A-1)*Q=H*S := by
    simpa [A,H,S,Q,w] using periodic_run_slope_at_zero L w hwcost m z hr
  have hrec : ∀ n, A*(z (n+1):Int) =
      (z n:Int)+H*X+(H*S)*(n:Int)+D := by
    simpa [A,H,S,X,D,w] using periodic_run_affine_recurrence L w m z hr
  have h0 := hrec 0
  have hStart : (A-1)*Z=H*X+D-A*Q := by
    dsimp [Z,Q] at *
    simp at h0
    omega
  exact PeriodSecondary.repeated_affine_obstruction
    a h r (offset u) T J A H D S Q X Z
    hJ hA hH hS hD hB hJpos hbase hSlope hStart

#print axioms no_infinite_repeated_word_ray


end PeriodWord
