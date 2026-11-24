import NearPowerAffine

namespace BB6.Agent41NearPower
open BB6.Agent49CorrectionGrowth

def SymRep (C : Nat) (k : Aff) (W B : Int) (n b : Nat) : Prop :=
  2*(b:Int)=(C:Int)*3^(k.eval n).toNat+W*9^n+B

def StatsRep (s : Aff×Aff) (n b : Nat) : Prop :=
  drift b=s.1.eval n ∧ (excess b:Int)=s.2.eval n

def addStats (s : Aff×Aff) (J E : Aff) : Aff×Aff := (s.1+J,s.2+E)

theorem addStats_correct {s : Aff×Aff} {J E : Aff} {n b c : Nat} (hs : StatsRep s n c)
    (hj : drift b=drift c+J.eval n) (he : (excess b:Int)=(excess c:Int)+E.eval n) :
    StatsRep (addStats s J E) n b := by
  unfold StatsRep addStats at *
  simp only [eval_add]
  omega

def stable_dec (w : Int) : Decidable (stable w) := by unfold stable; infer_instance
instance (w : Int) : Decidable (stable w) := stable_dec w

inductive StatsCert where
  | fixed | cycle | step (child : StatsCert) | pump (child : StatsCert)
  deriving Repr

def baseStats (C : Nat) (B : Int) : Aff×Aff :=
  (ac (directStats C 2 B).1, ac (directStats C 2 B).2)

def symStats (C : Nat) (k : Aff) (W B : Int) : StatsCert → Option (Aff×Aff)
  | .fixed =>
    if W=0 ∧ fixed B ∧ ge k 2=true then
      some (addStats (baseStats C B) (driftCharge (residue B).toNat*(k-ac 2)) ((excessCharge (residue B).toNat:Int)*(k-ac 2)))
    else none
  | .cycle =>
    if W=0 ∧ cycling B ∧ ge k 2=true ∧ modEq k 2 0=true then
      some (addStats (baseStats C B) (ac 0) (k-ac 2))
    else none
  | .step child =>
    if W%3=0 ∧ dominance k W B=true ∧ ge k 1=true then
      (symStats C (k-ac 1) (W/3) (residualStep B) child).map fun s =>
        addStats s (ac (driftCharge (residue B).toNat)) (ac (excessCharge (residue B).toNat))
    else none
  | .pump child =>
    if stable B ∧ dominance k W B=true then
      (symStats C (k-(2:Int)*an) 0 (W+B) child).map fun s =>
        addStats s (pairJ B*an) ((pairE B:Int)*an)
    else none

private theorem baseRep (C : Nat) (k : Aff) (B : Int) (n b : Nat) (hC : 0<C)
    (hB : -3≤B) (h : SymRep C k 0 B n b) : 2*(blockVal C 2 B:Int)=(C:Int)*3^2+B := by
  unfold SymRep at h
  simp only [Int.zero_mul,Int.add_zero] at h
  have ho : ∀ j : Nat, (3:Int)^j%2=1 := by
    intro j; induction j with
    | zero => decide
    | succ j ih => rw [Int.pow_succ,Int.mul_emod,ih]; decide
  have hm := Int.mul_emod (C:Int) ((3:Int)^(k.eval n).toNat) 2
  rw [ho] at hm
  have hp : ((C:Int)*3^(k.eval n).toNat)%2=(C:Int)%2 := by omega
  unfold blockVal
  change 2*((((C:Int)*9+B)/2).toNat:Int)=(C:Int)*9+B
  omega

private theorem residue_shift (W B : Int) (n : Nat) (hW : W%3=0) :
    residue (W*9^n+B)=residue B ∧ residualStep (W*9^n+B)=(W/3)*9^n+residualStep B := by
  have hw : W=3*(W/3) := by omega
  have hp : W*9^n=3*((W/3)*9^n) := by conv => lhs; rw [hw,Int.mul_assoc]; skip
  have hr : residue (W*9^n+B)=residue B := by unfold residue; omega
  constructor
  · exact hr
  · unfold residualStep
    rw [hr]
    omega

private theorem reduced_rep {C : Nat} {k : Aff} {W B : Int} {n b : Nat}
    (hC : 0<C) (hW : W%3=0) (hdom : dominance k W B=true) (hk : ge k 1=true)
    (hr : SymRep C k W B n b) :
    SymRep C (k-ac 1) (W/3) (residualStep B) n (nextBlock b) ∧
    drift b=drift (nextBlock b)+driftCharge (residue B).toNat ∧
    excess b=excess (nextBlock b)+excessCharge (residue B).toNat := by
  have hpos := (dominance_positive hC hdom n).2
  have hkn := ge_sound hk n
  have he : (k.eval n).toNat=((k-ac 1).eval n).toNat+1 := by simp; omega
  have hh : 0<b := by unfold SymRep at hr; omega
  unfold SymRep at hr
  rw [he,Int.add_assoc] at hr
  obtain ⟨hm,hn⟩ := residual_step C _ b (W*9^n+B) hh hr
  have hs := residue_shift W B n hW
  rw [hs.1] at hm
  rw [hs.2] at hn
  have hst := nextBlock_stats b hh
  have hmod : b%3=(residue B).toNat := by omega
  rw [hmod] at hst
  exact ⟨by unfold SymRep; omega,hst⟩

private theorem pump_rep {C : Nat} {k : Aff} {W B : Int} {n b : Nat}
    (hC : 0<C) (hs : stable B) (hd : dominance k W B=true) (hr : SymRep C k W B n b) :
    ∃ c, SymRep C (k-(2:Int)*an) 0 (W+B) n c ∧
      drift b=drift c+(n:Int)*pairJ B ∧ excess b=excess c+n*pairE B := by
  let l := ((k-(2:Int)*an).eval n).toNat
  have hkn := (dominance_sound hd n).1
  have hl : l=(k.eval n-2*n).toNat := by simp [l]
  have hk : (k.eval n).toNat=l+2*n := by rw [hl]; omega
  have hp := (dominance_positive hC hd n).1
  rw [←hl] at hp
  have hB : -3≤B := by unfold stable fixed cycling at hs; omega
  let c := blockVal C l (W+B)
  have hcpos : 0≤(C:Int)*3^l+W+B := by omega
  have hmod : (3:Int)^(2*n)%2=1 := by
    rw [←pow9_eq]; have h:=pow9_mod8 n; omega
  unfold SymRep at hr
  rw [hk,Int.pow_add,←Int.mul_assoc,←pow9_eq,←Int.add_mul] at hr
  have hq : (9:Int)^n=3^(2*n) := pow9_eq n
  have hpar : ((C:Int)*3^l+W+B)%2=0 := by
    have hh : 2*(b:Int)=((C:Int)*3^l+W)*3^(2*n)+B := by
      rw [←hq] ; omega
    have hm := Int.mul_emod ((C:Int)*3^l+W) ((3:Int)^(2*n)) 2
    rw [hmod] at hm
    omega
  have hc : 2*(c:Int)=(C:Int)*3^l+W+B := by unfold c blockVal; omega
  have hbb : 2*(b:Int)=(C:Int)*3^(l+2*n)+W*3^(2*n)+B := by
    rw [Int.pow_add,←Int.mul_assoc,←hq,←Int.add_mul]; exact hr
  have hh := nested_pump C l n b c W B hs hp hbb hc
  exact ⟨c,by unfold SymRep; change 2*(c:Int)=(C:Int)*3^l+0*9^n+(W+B); omega,hh⟩

theorem symStats_sound (C : Nat) (hC : 0<C) (cert : StatsCert) :
    ∀ k W B n b s, SymRep C k W B n b → symStats C k W B cert=some s → StatsRep s n b := by
  induction cert with
  | fixed =>
    intro k W B n b s hr h
    simp only [symStats] at h
    split at h
    next hh =>
      obtain ⟨rfl,hf,hg⟩ := hh
      injection h with he; subst s
      have hb : -3≤B := by unfold fixed at hf; omega
      have hfix : residualStep B=B := by unfold fixed at hf; rcases hf with h|h|h <;> subst B <;> decide
      have hbase := baseRep C k B n b hC hb hr
      have hk := ge_sound hg n
      have hke : (k.eval n).toNat=(k.eval n-2).toNat+2 := by omega
      unfold SymRep at hr
      simp only [Int.zero_mul,Int.add_zero] at hr
      rw [hke] at hr
      have htail := fixed_tail C _ b (blockVal C 2 B) B hC hb hfix hr hbase
      unfold StatsRep addStats baseStats directStats
      simp only [eval_add,eval_scale,eval_sub,eval_ac]
      constructor
      · rw [htail.1]; have hcast : ((k.eval n-2).toNat:Int)=k.eval n-2 := by omega
        rw [hcast,Int.mul_comm (k.eval n-2)]
      · rw [htail.2,Int.natCast_add,Int.natCast_mul]; have hcast : ((k.eval n-2).toNat:Int)=k.eval n-2 := by omega
        rw [hcast,Int.mul_comm (k.eval n-2)]
    next => contradiction
  | cycle =>
    intro k W B n b s hr h
    simp only [symStats] at h
    split at h
    next hh =>
      obtain ⟨rfl,hcy,hg,hm⟩ := hh
      injection h with he; subst s
      have hb : -3≤B := by unfold cycling at hcy; omega
      have hbase := baseRep C k B n b hC hb hr
      have hk := ge_sound hg n
      have hmod := modEq_sound (Or.inl rfl) hm n
      let m := ((k.eval n-2)/2).toNat
      have hke : (k.eval n).toNat=2*m+2 := by dsimp [m]; omega
      unfold SymRep at hr
      simp only [Int.zero_mul,Int.add_zero] at hr
      rw [hke] at hr
      have htail := cycle_tail C m b (blockVal C 2 B) B hC hcy hr hbase
      unfold StatsRep addStats baseStats directStats
      simp only [eval_add,eval_sub,eval_ac]
      constructor
      · omega
      · rw [htail.2,Int.natCast_add,Int.natCast_mul]; dsimp [m]; omega
    next => contradiction
  | step child ih =>
    intro k W B n b s hr h
    simp only [symStats] at h
    split at h
    next hh =>
      obtain ⟨hW,hd,hk⟩ := hh
      cases he : symStats C (k-ac 1) (W/3) (residualStep B) child with
      | none => simp [he] at h
      | some s' =>
        simp only [he,Option.map_some,Option.some.injEq] at h
        subst s
        obtain ⟨hr',hj,hE⟩ := reduced_rep hC hW hd hk hr
        have hs := ih _ _ _ n _ _ hr' he
        apply addStats_correct hs
        · simpa using hj
        · simp only [eval_ac]; omega
    next => contradiction
  | pump child ih =>
    intro k W B n b s hr h
    simp only [symStats] at h
    split at h
    next hh =>
      obtain ⟨hs,hd⟩ := hh
      cases he : symStats C (k-(2:Int)*an) 0 (W+B) child with
      | none => simp [he] at h
      | some s' =>
        simp only [he,Option.map_some,Option.some.injEq] at h
        subst s
        obtain ⟨c,hr',hj,hE⟩ := pump_rep hC hs hd hr
        have hst := ih _ _ _ n _ _ hr' he
        apply addStats_correct hst
        · simpa [Int.mul_comm] using hj
        · simp only [eval_scale,eval_an]; rw [hE,Int.natCast_add,Int.natCast_mul,Int.mul_comm (n:Int)]
    next => contradiction

#print axioms symStats_sound
end BB6.Agent41NearPower
