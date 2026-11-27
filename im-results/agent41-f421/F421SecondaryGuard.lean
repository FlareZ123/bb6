import F421SecondaryCycle

namespace BB6Coverage.Agent41F421.EpochWords
open F421TertiaryGuard (drain QBudget)

/-- Each cell independently uses a full-epoch budget or positional divisibility.
    The farthest cell must use a budget. This is strictly more general than
    a single protected far prefix followed by a fully divisible head. -/
def sPGood (k B : Nat) : List PC → Prop
  | [] => True
  | c::cs => (2*B*k+3≤c.p ∨ (2≤B ∧ ∃ l : Nat, 0<l ∧ c.p=l*(2*B))) ∧ sPGood k (2*B) cs

def sPrimary (k a b : Nat) (cs : List PC) : Prop :=
  a=2*2^cs.length-1 ∧ 3*2^cs.length-1≤b ∧ sPGood k 1 cs ∧ QBudget 1 1 cs ∧ 1≤cs.length

theorem sPgoodLower (k B : Nat) (cs : List PC) (hB : 1≤B) (hg : sPGood k B cs) : pLower 3 cs := by
  induction cs generalizing B with
  | nil => simp [pLower]
  | cons c cs ih =>
    rcases hg with ⟨hp,ht⟩
    apply pLowerCons
    · rcases hp with h|⟨hB',l,hl,he⟩
      · omega
      · have hm := Nat.mul_le_mul_right (2*B) (show 1≤l by omega)
        simp only [Nat.one_mul] at hm
        omega
    · exact ih (2*B) (by omega) ht

theorem sPgoodStep (k B : Nat) (c : PC) (hB : 1≤B)
    (hp : 2*B*(k+1)+3≤c.p ∨ (2≤B ∧ ∃ l : Nat, 0<l ∧ c.p=l*(2*B))) :
    2*B≤c.p ∧ (c.p=2*B ∨ 2*B+3≤c.p) := by
  rcases hp with h|⟨hB',l,hl,he⟩
  · rw [Nat.mul_succ] at h; omega
  · have hm := Nat.mul_le_mul_right (2*B) (show 1≤l by omega)
    simp only [Nat.one_mul] at hm
    refine ⟨by omega,?_⟩
    by_cases h : l=1
    · exact Or.inl (by simpa [h] using he)
    · right
      have hm' := Nat.mul_le_mul_right (2*B) (show 2≤l by omega)
      omega

def trimQ (B : Nat) : List PC → List PC
  | [] => []
  | c::cs => ⟨c.p,c.q-B⟩::trimQ (2*B) cs

theorem trimLength (B : Nat) (cs : List PC) : (trimQ B cs).length=cs.length := by
  induction cs generalizing B with
  | nil => rfl
  | cons c cs ih => simp [trimQ,ih]

theorem trimPGood (k B : Nat) (cs : List PC) (hg : sPGood k B cs) : sPGood k B (trimQ B cs) := by
  induction cs generalizing B with
  | nil => trivial
  | cons c cs ih => exact ⟨hg.1,ih _ hg.2⟩

theorem trimQGood (B : Nat) (cs : List PC) (hg : QBudget 2 B cs) : QBudget 1 B (trimQ B cs) := by
  induction cs generalizing B with
  | nil => trivial
  | cons c cs ih => exact ⟨by change 2+1*B≤c.q-B; have h := hg.1; omega,ih _ hg.2⟩

/-- Full positional A horizon is preserved even for terminal deletions.
    Surviving cells retain the mixed P budget at their smaller scales. -/
theorem sDrainA (k B C carry : Nat) (cs : List PC) (hB : 1≤B) (hC : 1≤C)
    (hCB : C≤B) (hdvd : C∣B) (hsmall : C=1 → B=1)
    (hp : sPGood (k+1) B cs) (hq : QBudget 1 B cs) :
    guarded (B-1) (dec cs) ∧
    let (as,H,r) := drain (B-1) carry (dec cs)
    H=B*2^cs.length-1 ∧ sPGood k C as ∧ QBudget 2 C as ∧ as.length≤cs.length := by
  induction cs generalizing B C carry with
  | nil => simp [dec,MergedDrain.guarded,drain,sPGood,QBudget]
  | cons c cs ih =>
    rcases hp with ⟨hp,ht⟩
    rcases hq with ⟨hq,hqt⟩
    have hready := sPgoodStep k B c hB hp
    let d : PC := ⟨c.p-1,c.q⟩
    have he : dec (c::cs)=d::dec cs := rfl
    rw [he]
    have hmin : min d.p (2*(B-1)+1)=2*B-1 := by dsimp [d]; omega
    have hh : B-1+(2*B-1+1)/2=2*B-1 := by omega
    have hcap : 2*(B-1)+1=2*B-1 := by omega
    by_cases hz : c.p=2*B
    · have hC2 : 2≤C := by
        by_cases h : C=1
        · have hB' := hsmall h
          rcases hp with hh'|⟨hh',_⟩
          · rw [Nat.mul_succ] at hh'; omega
          · omega
        · omega
      have hd' : C∣2*B := by obtain ⟨t,he⟩ := hdvd; exact ⟨2*t,by rw [he]; ac_rfl⟩
      have hi := ih (2*B) C (carry+c.q+B) (by omega) hC (by omega) hd' (by omega) ht hqt
      have hd : d.p≤2*B-1 := by dsimp [d]; omega
      constructor
      · simp only [MergedDrain.guarded,hmin,hh]
        exact ⟨by dsimp [d]; omega,by dsimp [d]; omega,by dsimp [d]; omega,hi.1⟩
      · simp only [drain,hcap,if_pos hd]
        have he : (d.p+1)/2=B := by dsimp [d]; omega
        rw [he,show B-1+B=2*B-1 by omega]
        rcases hr : drain (2*B-1) (carry+c.q+B) (dec cs) with ⟨as,H,r⟩
        rw [hr] at hi
        simp only [List.length_cons]
        refine ⟨?_,hi.2.2.1,hi.2.2.2.1,by have h := hi.2.2.2.2; omega⟩
        rw [hi.2.1,Nat.pow_succ]; rw [show (2*B)*2^cs.length=B*(2^cs.length*2) by ac_rfl]
    · have hsurv : 2*B+3≤c.p := hready.2.resolve_left hz
      have hd' : (2*C)∣2*B := Nat.mul_dvd_mul_left 2 hdvd
      have hi := ih (2*B) (2*C) 0 (by omega) (by omega) (by omega) hd' (by omega) ht hqt
      have hd : ¬d.p≤2*B-1 := by dsimp [d]; omega
      constructor
      · simp only [MergedDrain.guarded,hmin,hh]
        exact ⟨by dsimp [d]; omega,by dsimp [d]; omega,by dsimp [d]; omega,hi.1⟩
      · simp only [drain,hcap,if_neg hd]
        rcases hr : drain (2*(B-1)+1) 0 (dec cs) with ⟨as,H,r⟩
        rw [show 2*(B-1)+1=2*B-1 by omega] at hr
        rw [hr] at hi
        rw [hr]
        refine ⟨?_,⟨?_,hi.2.2.1⟩,⟨?_,hi.2.2.2.1⟩,by simpa using hi.2.2.2.2⟩
        · rw [hi.2.1,List.length_cons,Nat.pow_succ]; rw [show (2*B)*2^cs.length=B*(2^cs.length*2) by ac_rfl]
        · change 2*C*k+3≤d.p-(2*B-1) ∨ (2≤C ∧ ∃ l : Nat, 0<l ∧ d.p-(2*B-1)=l*(2*C))
          rcases hp with hp|⟨hB2,l,hl,hp⟩
          · left; rw [Nat.mul_succ] at hp
            have hm := Nat.mul_le_mul_right k (show 2*C≤2*B by omega)
            dsimp [d]; omega
          · right
            have hC2 : 2≤C := by by_cases h : C=1; have := hsmall h; omega; omega
            obtain ⟨t,he⟩ := hdvd
            have hl2 : 2≤l := by by_cases h : l=1; simp [h] at hp; omega; omega
            have ht : 0<t := by by_cases h : t=0; simp [h] at he; omega; omega
            refine ⟨hC2,⟨(l-1)*t,Nat.mul_pos (by omega) ht,?_⟩⟩
            have hh : d.p-(2*B-1)=c.p-2*B := by dsimp [d]; omega
            rw [hh,hp]
            calc
              l*(2*B)-2*B = l*(2*B)-1*(2*B) := by simp
              _ = (l-1)*(2*B) := (Nat.sub_mul l 1 (2*B)).symm
              _ = (l-1)*t*(2*C) := by rw [he]; ac_rfl
        · change 2+2*C≤d.q+(B-1)+1+carry
          dsimp [d]; omega

#print axioms sDrainA
end BB6Coverage.Agent41F421.EpochWords
