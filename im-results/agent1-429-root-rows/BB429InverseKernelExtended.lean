import BB429NewResidue
import BB429RootMod32
import BB429NewRootRows
import Lean.Elab.Tactic.Omega

namespace BB429KernelExtended
open BB429NewResidue

structure Affine where
  A : Nat
  a : Nat
  B : Nat
  b : Nat
  deriving Repr, DecidableEq

def va (s : Affine) (q : Nat) := s.A*q+s.a
def vb (s : Affine) (q : Nat) := s.B*q+s.b

def F (s : Affine) : Affine := ⟨s.A/2,(s.a-3)/2,s.B+s.A,s.b+s.a⟩
def S (s : Affine) : Affine := ⟨s.A+s.B/4,(4*s.a+s.b-26)/4,s.B/2,(s.b+4)/2⟩
def E (s : Affine) : Affine := ⟨s.A+s.B/4,(4*s.a+s.b-14)/4,s.B/2,s.b/2⟩

private def Bad (s : Affine) : Prop :=
  (s.A%8=0 ∧ s.B%4=0 ∧ ¬BB429Mod8.Allowed s.a s.b) ∨
  (s.A%2=0 ∧ s.B%8=0 ∧ s.a>0 ∧ s.a%2=0 ∧ s.b%8≠2) ∨
  (s.A%8=0 ∧ s.B%8=0 ∧ s.a%8=7 ∧ s.b%8=7) ∨
  (s.A%16=0 ∧ s.B%8=0 ∧ s.a%16=1 ∧ s.b%8=6) ∨
  (s.A%16=0 ∧ s.B%8=0 ∧ s.a%16=5 ∧ s.b%8=6) ∨
  (s.A%32=0 ∧ s.B%16=0 ∧ s.a%32=5 ∧ s.b%16=1) ∨
  (s.A%16=0 ∧ s.B%8=0 ∧ s.a%16=11 ∧ s.b%8≠2 ∧ s.b%8≠6 ∧ s.b%8≠7) ∨
  (s.A%32=0 ∧ s.B%8=0 ∧ (s.a%32=19 ∨ s.a%32=27) ∧ s.b%8≠2 ∧ s.b%8≠7)

instance (s : Affine) : Decidable (Bad s) := by
  unfold Bad BB429Mod8.Allowed
  infer_instance

private def Odd (s : Affine) : Prop :=
  13≤s.a ∧ s.a%2=1 ∧ s.A%2=0 ∧ s.B%4=0
private def Even (s : Affine) : Prop :=
  6≤s.a ∧ s.a%2=0 ∧ s.A%2=0 ∧ s.B%4=0

instance (s : Affine) : Decidable (Odd s) := by unfold Odd; infer_instance
instance (s : Affine) : Decidable (Even s) := by unfold Even; infer_instance

def cert : Nat → Affine → Bool
  | 0,s => decide (Bad s)
  | d+1,s =>
    if Bad s then true
    else if Odd s then
      cert d (F s) && (if s.b%4=2 then cert d (S s) else true)
    else if Even s then
      if s.b%4=2 then cert d (E s) else true
    else false

private theorem val_mod (s : Affine) (q m : Nat) (hm : s.A %m=0) :
    va s q %m = s.a%m := by
  simp [va, Nat.add_mod, Nat.mul_mod, hm]
private theorem valb_mod (s : Affine) (q m : Nat) (hm : s.B %m=0) :
    vb s q %m = s.b%m := by
  simp [vb, Nat.add_mod, Nat.mul_mod, hm]

private theorem bad_sound (s : Affine) (q : Nat) (hb : Bad s) :
    ¬ Reach (va s q) (vb s q) := by
  intro hr
  rcases hb with h|h|h|h|h|h|h|h
  · have ha := val_mod s q 8 h.1
    have hb := valb_mod s q 4 h.2.1
    have hall := reach_allowed (va s q) (vb s q) hr
    unfold BB429Mod8.Allowed at hall h
    omega
  · rcases h with ⟨hA,hB,ha,hpar,hb⟩
    have ham := val_mod s q 2 hA
    have hbm := valb_mod s q 8 hB
    obtain ⟨n,hn⟩ := hr
    have hx : 0 < va s q := by simp [va]; omega
    have hh := BB429RootEven8.rooted_positive_even_eight n (va s q) (vb s q) hn hx (by omega)
    omega
  · rcases h with ⟨hA,hB,ha,hb⟩
    have ham := val_mod s q 8 hA
    have hbm := valb_mod s q 8 hB
    obtain ⟨n,hn⟩ := hr
    have hh := BB429RootMod16.rooted_not_7_7 n (va s q) (vb s q) hn (by omega)
    omega
  · rcases h with ⟨hA,hB,ha,hb⟩
    have ham := val_mod s q 16 hA
    have hbm := valb_mod s q 8 hB
    obtain ⟨n,hn⟩ := hr
    have hh := BB429RootMod16.rooted_not_1_6 n (va s q) (vb s q) hn (by omega)
    omega
  · rcases h with ⟨hA,hB,ha,hb⟩
    have ham := val_mod s q 16 hA
    have hbm := valb_mod s q 8 hB
    obtain ⟨n,hn⟩ := hr
    have hh := BB429RootMod16.rooted_not_5_6 n (va s q) (vb s q) hn (by omega)
    omega
  · rcases h with ⟨hA,hB,ha,hb⟩
    have ham := val_mod s q 32 hA
    have hbm := valb_mod s q 16 hB
    obtain ⟨n,hn⟩ := hr
    have hh := BB429RootMod32.rooted_not_5_1 n (va s q) (vb s q) hn (by omega)
    omega
  · rcases h with ⟨hA,hB,ha,hb,hc,hd⟩
    have ham := val_mod s q 16 hA
    have hbm := valb_mod s q 8 hB
    obtain ⟨n,hn⟩ := hr
    have hh := BB429NewRootRows.rooted_eleven n (va s q) (vb s q) hn (by omega)
    omega
  · rcases h with ⟨hA,hB,ha,hb,hc⟩
    have ham := val_mod s q 32 hA
    have hbm := valb_mod s q 8 hB
    obtain ⟨n,hn⟩ := hr
    have hh := BB429NewRootRows.rooted_nineteen_or_twentyseven n (va s q) (vb s q) hn (by omega)
    omega

private theorem halved_coeff (x q k : Nat) (hk : x%k=0) (hkpos : 0<k) :
    x*q = k*((x/k)*q) := by
  have heq : x=k*(x/k) := by
    have hd:= Nat.mod_add_div x k
    omega
  calc
    x*q = (k*(x/k))*q := congrArg (· * q) heq
    _ = k*((x/k)*q) := by simp only [Nat.mul_assoc]

private theorem eq_F (s : Affine) (q x y : Nat) (h : Odd s)
    (hx : va s q=2*x+3) (hy : y=vb s q+va s q) :
    x=va (F s) q ∧ y=vb (F s) q := by
  rcases h with ⟨hlarge,hodd,hA,hB⟩
  have hcoeff := halved_coeff s.A q 2 hA (by omega)
  have hconst : s.a=2*((s.a-3)/2)+3 := by omega
  unfold va vb F at *
  dsimp at *
  constructor
  · omega
  · simp only [Nat.add_mul]; omega

private theorem eq_S (s : Affine) (q x y : Nat) (h : Odd s)
    (hb : s.b%4=2) (hx : 4*x+26=4*(va s q)+vb s q)
    (hy : 2*y=vb s q+4) :
    x=va (S s) q ∧ y=vb (S s) q := by
  rcases h with ⟨hlarge,hodd,hA,hB⟩
  have hcoeff := halved_coeff s.B q 4 hB (by omega)
  have hcoeff2 : s.B*q=2*((s.B/2)*q) :=
    halved_coeff s.B q 2 (by omega) (by omega)
  have hc : 4*s.a+s.b=4*((4*s.a+s.b-26)/4)+26 := by omega
  have hcb : s.b+4=2*((s.b+4)/2) := by omega
  have hdist : (s.A+s.B/4)*q = s.A*q+(s.B/4)*q := by simp [Nat.add_mul]
  unfold va vb S at *
  dsimp at *
  constructor
  · omega
  · omega

private theorem eq_E (s : Affine) (q x y : Nat) (h : Even s)
    (hb : s.b%4=2) (hx : 4*x+14=4*(va s q)+vb s q)
    (hy : 2*y=vb s q) :
    x=va (E s) q ∧ y=vb (E s) q := by
  rcases h with ⟨hlarge,heven,hA,hB⟩
  have hcoeff := halved_coeff s.B q 4 hB (by omega)
  have hcoeff2 : s.B*q=2*((s.B/2)*q) :=
    halved_coeff s.B q 2 (by omega) (by omega)
  have hc : 4*s.a+s.b=4*((4*s.a+s.b-14)/4)+14 := by omega
  have hcb : s.b=2*(s.b/2) := by omega
  have hdist : (s.A+s.B/4)*q = s.A*q+(s.B/4)*q := by simp [Nat.add_mul]
  unfold va vb E at *
  dsimp at *
  constructor
  · omega
  · omega

set_option maxHeartbeats 10000000
set_option maxRecDepth 30000

/-- All-parameter soundness of the bounded inverse-tree certificate. -/
theorem cert_sound (d : Nat) (s : Affine) (q : Nat)
    (hc : cert d s=true) : ¬Reach (va s q) (vb s q) := by
  induction d generalizing s q with
  | zero =>
      have hb : Bad s := of_decide_eq_true (by simpa [cert] using hc)
      exact bad_sound s q hb
  | succ d ih =>
      by_cases hb : Bad s
      · exact bad_sound s q hb
      · by_cases ho : Odd s
        · have hcert : cert d (F s) && (if s.b%4=2 then cert d (S s) else true) = true := by
            simpa [cert, hb, ho] using hc
          have hf : cert d (F s)=true := by
            cases hF : cert d (F s) with
            | false => simp [hF] at hcert
            | true => rfl
          intro hr
          have hlarge0 : 13≤s.a := ho.1
          have hodd0 : s.a%2=1 := ho.2.1
          have ham := val_mod s q 2 ho.2.2.1
          have hbm := valb_mod s q 4 ho.2.2.2
          rcases odd_back (va s q) (vb s q) (by simp only [va]; omega) (by omega) hr with
            ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hm⟩
          · obtain ⟨hex,hey⟩ := eq_F s q x y ho hx hy
            rw [hex,hey] at hp
            exact (ih (F s) q hf) hp
          · by_cases hsb : s.b%4=2
            · have hcertS : cert d (S s)=true := by
                simpa [hsb,hf] using hcert
              obtain ⟨hex,hey⟩ := eq_S s q x y ho hsb hx hy
              rw [hex,hey] at hp
              exact (ih (S s) q hcertS) hp
            · omega
        · by_cases he : Even s
          · by_cases hsb : s.b%4=2
            · have hcertE : cert d (E s)=true := by
                simpa [cert,hb,ho,he,hsb] using hc
              intro hr
              have ham := val_mod s q 2 he.2.2.1
              have hbm := valb_mod s q 4 he.2.2.2
              have hlarge0 : 6≤s.a := he.1
              have heven0 : s.a%2=0 := he.2.1
              obtain ⟨x,y,hp,hx,hy,hm⟩ := even_back (va s q) (vb s q) (by simp only [va]; omega) (by omega) hr
              obtain ⟨hex,hey⟩ := eq_E s q x y he hsb hx hy
              rw [hex,hey] at hp
              exact (ih (E s) q hcertE) hp
            · intro hr
              have ham := val_mod s q 2 he.2.2.1
              have hbm := valb_mod s q 4 he.2.2.2
              have hlarge0 : 6≤s.a := he.1
              have heven0 : s.a%2=0 := he.2.1
              obtain ⟨x,y,hp,hx,hy,hm⟩ := even_back (va s q) (vb s q) (by simp only [va]; omega) (by omega) hr
              omega
          · simp [cert,hb,ho,he] at hc

#print axioms cert_sound
end BB429KernelExtended
