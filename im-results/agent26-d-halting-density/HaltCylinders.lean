import Std
import Boundary

namespace BB6.Agent26.HaltCylinders
open CryptidBoundary

private theorem nine_pow_mod (d : Nat) : 9^d%8=1 := by
  induction d with
  | zero => decide
  | succ d ih => rw [Nat.pow_succ, Nat.mul_mod, ih]

/-- A constructive inverse for 8 modulo each ternary power, expressed with
    natural-number equality instead of subtraction or integer inverses. -/
theorem inv8_exact (d : Nat) : ∃ u v : Nat, 8*u=1+3^d*v := by
  have hmod : (7*9^d+1)%8=0 := by
    rw [Nat.add_mod, Nat.mul_mod, nine_pow_mod]
  have hdiv := Nat.mod_add_div (7*9^d+1) 8
  rw [hmod, Nat.zero_add] at hdiv
  refine ⟨(7*9^d+1)/8,7*3^d,?_⟩
  rw [hdiv, show 9^d=3^d*3^d by rw [←Nat.mul_pow]]
  ac_rfl

theorem inv8pow_exact (d L : Nat) : ∃ u v : Nat, 8^L*u=1+3^d*v := by
  induction L with
  | zero => exact ⟨1,0,by simp⟩
  | succ L ih =>
    obtain ⟨u,v,huv⟩ := ih
    obtain ⟨x,y,hxy⟩ := inv8_exact d
    refine ⟨u*x,v+y+3^d*v*y,?_⟩
    rw [Nat.pow_succ,show 8^L*8*(u*x)=(8^L*u)*(8*x) by ac_rfl,huv,hxy]
    simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
    ac_rfl

/-- Every arithmetic progression with ratio 8^L intersects any progression
    with ratio 3^d, at nonnegative indices on both sides. -/
theorem affine_preimage (d L m c : Nat) : ∃ p t : Nat, m+8^L*p=c+3^d*t := by
  obtain ⟨u,v,huv⟩ := inv8pow_exact d L
  let P := 3^d
  let a := c+P*m-m
  have hp : 1≤P := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.pow_pos (by decide)))
  have hm : m ≤ P*m := by
    simpa using Nat.mul_le_mul_right m hp
  have ha : m+a=c+P*m := by dsimp [a]; omega
  refine ⟨u*a,m+v*a,?_⟩
  change m+8^L*(u*a)=c+P*(m+v*a)
  rw [←Nat.mul_assoc,huv]
  change m+(1+P*v)*a=c+P*(m+v*a)
  simp only [Nat.add_mul,Nat.one_mul,Nat.mul_add,Nat.mul_assoc,←Nat.add_assoc,ha]

/-- A full, explicitly encoded F/0 section. No canonical suffix assumption. -/
def sec (n : Nat) (w : List Bool) : Cfg :=
  ⟨[],false,List.replicate n true ++ w,5⟩

def Halts (c : Cfg) : Prop := ∃ t, (run t c).st=6

def zeros : List Bool → Nat
  | [] => 0
  | true::w => zeros w
  | false::w => zeros w+1

theorem sec_true (n : Nat) (w : List Bool) : sec n (true::w)=sec (n+1) w := by
  unfold sec
  rw [show List.replicate (n+1) true = List.replicate n true ++ [true] by
    rw [←List.replicate_append_replicate]; rfl]
  simp

theorem sec_B (k : Nat) (w : List Bool) :
    run (12*k*k+49*k+40) (sec (3*k+2) (false::w))=sec (8*k+9) w := by
  have hin : sec (3*k+2) (false::w)=init (List.replicate (3*k) true ++ false::w) := by
    unfold sec init
    rw [show 3*k+2=2+3*k by omega,←List.replicate_append_replicate]
    rfl
  rw [hin,full_B]
  rfl

theorem halt_of_return {c d : Cfg} {s : Nat} (h : run s c=d) (hd : Halts d) : Halts c := by
  obtain ⟨t,ht⟩ := hd
  exact ⟨s+t,by rw [run_add,h,ht]⟩

/-- B-only deletion of an explicit suffix; leading ones are absorbed into
    the unary parameter without performing a raw step. -/
inductive Flush : Nat → List Bool → Nat → Prop where
  | nil (n : Nat) : Flush n [] n
  | one {n m : Nat} {w : List Bool} : Flush (n+1) w m → Flush n (true::w) m
  | zero {k m : Nat} {w : List Bool} : Flush (8*k+9) w m → Flush (3*k+2) (false::w) m

theorem flush_source {n m : Nat} {w : List Bool} (h : Flush n w m) :
    ∃ t, run t (sec n w)=sec m [] := by
  induction h with
  | nil n => exact ⟨0,rfl⟩
  | one h ih => simpa [sec_true] using ih
  | @zero k m w h ih =>
    obtain ⟨t,ht⟩ := ih
    exact ⟨12*k*k+49*k+40+t,by rw [run_add,sec_B,ht]⟩

def flushEval (n : Nat) : List Bool → Option Nat
  | [] => some n
  | true::w => flushEval (n+1) w
  | false::w => if n%3=2 then flushEval (8*(n/3)+9) w else none

theorem flush_eval {n m : Nat} {w : List Bool} (h : Flush n w m) :
    flushEval n w=some m := by
  induction h with
  | nil => rfl
  | one h ih => exact ih
  | @zero k m w h ih =>
    simpa [flushEval,show (3*k+2)%3=2 by omega,show (3*k+2)/3=k by omega] using ih

theorem flush_unique {n m m' : Nat} {w : List Bool}
    (h : Flush n w m) (h' : Flush n w m') : m=m' := by
  have h1 := flush_eval h
  have h2 := flush_eval h'
  rw [h1] at h2
  exact Option.some.inj h2

/-- Every desired final ternary residue has a preparatory residue for
    each finite suffix. All representatives n≥2 have a B-only flush to
    that target class; one extra ternary digit per zero suffices. -/
theorem flush_class (d c : Nat) :
    ∀ w, ∃ r, r<3^(d+zeros w) ∧
      ∀ n, 2≤n → n%3^(d+zeros w)=r →
        ∃ m, 2≤m ∧ Flush n w m ∧ m%3^d=c%3^d := by
  intro w
  induction w with
  | nil =>
    exact ⟨c%3^d,Nat.mod_lt _ (Nat.pow_pos (by decide)),fun n hn hr => ⟨n,hn,Flush.nil n,hr⟩⟩
  | cons b w ih =>
    obtain ⟨a,ha,hh⟩ := ih
    let P := 3^(d+zeros w)
    have hp : 0<P := Nat.pow_pos (by decide)
    change a<P at ha
    cases b with
    | true =>
      change ∃ r, r<P ∧ ∀ n, 2≤n → n%P=r → ∃ m, 2≤m ∧ Flush n (true::w) m ∧ m%3^d=c%3^d
      let r := (a+P-1)%P
      refine ⟨r,Nat.mod_lt _ hp,?_⟩
      intro n hn hr
      have hnext : (n+1)%P=a := by
        calc
          (n+1)%P = (n%P+1)%P := (Nat.mod_add_mod _ _ _).symm
          _ = (r+1)%P := by rw [hr]
          _ = (a+P-1+1)%P := Nat.mod_add_mod _ _ _
          _ = a := by rw [show a+P-1+1=a+P by omega]; simp [Nat.mod_eq_of_lt ha]
      obtain ⟨m,hm,hf,hc⟩ := hh (n+1) (by omega) hnext
      exact ⟨m,hm,Flush.one hf,hc⟩
    | false =>
      obtain ⟨p,t,hpt⟩ := affine_preimage (d+zeros w) 1 9 a
      change 9+8*p=a+P*t at hpt
      let r := 3*(p%P)+2
      have hpl : p%P<P := Nat.mod_lt _ hp
      have hr : r<P*3 := by dsimp [r]; omega
      rw [show d+zeros (false::w)=d+zeros w+1 by simp [zeros,Nat.add_assoc],Nat.pow_succ]
      change ∃ r, r<P*3 ∧ ∀ n, 2≤n → n%(P*3)=r → ∃ m, 2≤m ∧ Flush n (false::w) m ∧ m%3^d=c%3^d
      refine ⟨r,hr,?_⟩
      intro n hn hnmod
      let k := p%P+P*(n/(P*3))
      have hdiv := Nat.mod_add_div n (P*3)
      rw [hnmod] at hdiv
      have hn' : n=3*k+2 := by
        rw [←hdiv]; dsimp [k,r]; rw [Nat.mul_add]; ac_rfl
      have hkm : k%P=p%P := by simp [k,Nat.add_mod]
      have h1 : (8*k+9)%P=(8*p+9)%P := by
        calc
          (8*k+9)%P = ((8%P*(k%P))%P+9%P)%P := by rw [Nat.add_mod (8*k) 9, Nat.mul_mod 8 k]
          _ = ((8%P*(p%P))%P+9%P)%P := by rw [hkm]
          _ = (8*p+9)%P := by rw [Nat.add_mod (8*p) 9, Nat.mul_mod 8 p]
      have hnext : (8*k+9)%P=a := by
        rw [h1,Nat.add_comm (8*p) 9,hpt]
        simp [Nat.add_mod,Nat.mod_eq_of_lt ha]
      obtain ⟨m,hm,hf,hc⟩ := hh (8*k+9) (by omega) hnext
      rw [hn']
      exact ⟨m,hm,Flush.zero hf,hc⟩

/-- A single pure-unary halting cylinder produces a halting cylinder for
    every finite suffix. The exponent overhead is exactly its zero count. -/
theorem suffix_cylinder (d c : Nat)
    (hbase : ∀ n, 2≤n → n%3^d=c%3^d → Halts (sec n [])) (w : List Bool) :
    ∃ r, r<3^(d+zeros w) ∧
      ∀ n, 2≤n → n%3^(d+zeros w)=r → Halts (sec n w) := by
  obtain ⟨r,hr,hf⟩ := flush_class d c w
  refine ⟨r,hr,?_⟩
  intro n hn hmod
  obtain ⟨m,hm,hw,hmr⟩ := hf n hn hmod
  obtain ⟨t,ht⟩ := flush_source hw
  exact halt_of_return ht (hbase m hm hmr)

noncomputable def pullback (d c : Nat) (w : List Bool) : Nat :=
  Classical.choose (flush_class d c w)

theorem pullback_spec (d c : Nat) (w : List Bool) :
    pullback d c w < 3^(d+zeros w) ∧
      ∀ n, 2≤n → n%3^(d+zeros w)=pullback d c w →
        ∃ m, 2≤m ∧ Flush n w m ∧ m%3^d=c%3^d :=
  Classical.choose_spec (flush_class d c w)

theorem pullback_inj (d a b : Nat) (w : List Bool)
    (ha : a<3^d) (hb : b<3^d)
    (h : pullback d a w=pullback d b w) : a=b := by
  let P := 3^(d+zeros w)
  let n := pullback d a w+2*P
  have hp : 0<P := Nat.pow_pos (by decide)
  have hn : 2≤n := by dsimp [n]; omega
  have hmod : n%P=pullback d a w := by
    simp [n,Nat.add_mod,Nat.mod_eq_of_lt (pullback_spec d a w).1,P]
  obtain ⟨x,hx,hfx,hxa⟩ := (pullback_spec d a w).2 n hn hmod
  obtain ⟨y,hy,hfy,hyb⟩ := (pullback_spec d b w).2 n hn (hmod.trans h)
  have he := flush_unique hfx hfy
  rw [he,hyb,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] at hxa
  exact hxa.symm

/-- Pull back an arbitrary finite family of disjoint pure-unary halting
    cylinders through the B-flush. No enumeration of its elements occurs. -/
theorem suffix_family (d : Nat) (R : List Nat) (w : List Bool)
    (hnd : R.Nodup) (hR : ∀ a∈R, a<3^d ∧
      ∀ n, 2≤n → n%3^d=a → Halts (sec n [])) :
    ∃ S : List Nat, S.length=R.length ∧ S.Nodup ∧
      ∀ a∈S, a<3^(d+zeros w) ∧
        ∀ n, 2≤n → n%3^(d+zeros w)=a → Halts (sec n w) := by
  refine ⟨R.map (fun a => pullback d a w),by simp,?_,?_⟩
  · rw [List.nodup_iff_pairwise_ne,List.pairwise_map]
    apply List.Pairwise.imp_of_mem (p:=List.nodup_iff_pairwise_ne.mp hnd)
    intro a b ha hb hne he
    exact hne (pullback_inj d a b w (hR a ha).1 (hR b hb).1 he)
  · intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    obtain ⟨hr,hf⟩ := pullback_spec d b w
    refine ⟨hr,?_⟩
    intro n hn hmod
    obtain ⟨m,hm,hflush,hmb⟩ := hf n hn hmod
    obtain ⟨t,ht⟩ := flush_source hflush
    rw [Nat.mod_eq_of_lt (hR b hb).1] at hmb
    exact halt_of_return ht ((hR b hb).2 m hm hmb)

/-- A certified affine-liftable prefix can always be extended into a
    halting cylinder after changing only higher ternary digits of n. -/
theorem prefix_extension (d c L n m : Nat) (v w : List Bool) (hm : 2≤m)
    (hbase : ∀ z, 2≤z → z%3^d=c%3^d → Halts (sec z []))
    (hlift : ∀ q, Halts (sec (m+8^L*q) w) → Halts (sec (n+3^L*q) v)) :
    ∃ p, ∀ q, Halts (sec (n+3^L*(p+3^(d+zeros w)*q)) v) := by
  obtain ⟨r,hr,hh⟩ := suffix_cylinder d c hbase w
  obtain ⟨p,t,ht⟩ := affine_preimage (d+zeros w) L m r
  refine ⟨p,?_⟩
  intro q
  apply hlift
  apply hh _ (by omega)
  rw [Nat.mul_add,←Nat.add_assoc,ht]
  simp [Nat.add_mod,Nat.mul_mod,Nat.mod_eq_of_lt hr]

#print axioms pullback_inj
#print axioms suffix_family
#print axioms prefix_extension

#print axioms flush_source
#print axioms flush_unique
#print axioms flush_class
#print axioms suffix_cylinder
end BB6.Agent26.HaltCylinders
