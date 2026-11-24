import NearPowerSymbolic

namespace BB6.Agent41NearPower
open BB6.Agent49CorrectionGrowth

def symImage (w E : Aff) (z : Nat) : Aff := (3:Int)*w+(2:Int)*(E+ac z)

def symRestore (s : SymState) (q : Sector) (w J : Aff) : SymState :=
  let k := s.k-ac 1
  let a := s.u-(2:Int)*J+w
  match q with
  | .LO => ⟨3*s.C+s.D,s.D,k,a+ac 4,w-ac 6⟩
  | .LE => ⟨3*s.C+s.D,s.D,k,a,w-ac 4⟩
  | .RO => ⟨s.D,3*s.C+s.D,k,w+ac 2,a-ac 6⟩
  | .RE => ⟨s.D,3*s.C+s.D,k,w-ac 2,a-ac 4⟩

def symReject (s : SymState) (q : Sector) : Bool :=
  symParity s.C s.k s.u 1 || symParity s.D s.k s.v (1-dp q)

def symGap (s : SymState) (q : Sector) (w E : Aff) : Bool :=
  match symEval s.D (s.k-ac 1) (w+ac 4) with
  | none => false
  | some st => ge (s.v-symImage w E (z q)) 1 && ge (symImage (w+ac 4) st.2 (z q)-s.v) 1

def symBranch (s : SymState) (q : Sector) (w : Aff) (childOK : SymState→Bool) : Bool :=
  match symEval s.D (s.k-ac 1) w with
  | none => false
  | some st => domAff (s.k-ac 1) w && symParity s.D (s.k-ac 1) w (bp q) &&
      (symGap s q w st.2 || (decide (symImage w st.2 (z q)=s.v) &&
        (symReject (symRestore s q w st.1) q || childOK (symRestore s q w st.1))))

def symLeft (s : SymState) : Sector := if symParity s.D s.k s.v 0 then .LE else .LO

def symRight (s : SymState) : Sector := if symParity s.D s.k s.v 0 then .RO else .RE

inductive SymCert where
  | stop
  | fork (wl wr : Aff) (l r : SymCert)
  deriving Repr

def symCheck (s : SymState) : SymCert → Bool
  | .stop => false
  | .fork wl wr l r => symGuard s && (symParity s.D s.k s.v 0 || symParity s.D s.k s.v 1) &&
    symBranch s (symLeft s) wl (fun t => symCheck t l) && symBranch s (symRight s) wr (fun t => symCheck t r)

theorem symSectors_sound {s : SymState} {n x y : Nat} (_hr : Represents (s.atN n) x y)
    (h : (symParity s.D s.k s.v 0 || symParity s.D s.k s.v 1)=true) :
    leftSector (s.atN n)=symLeft s ∧ rightSector (s.atN n)=symRight s := by
  by_cases he : symParity s.D s.k s.v 0=true
  · have hp := symParity_sound he n
    simp [leftSector,rightSector,symLeft,symRight,he,SymState.atN,hp]
  · have hp1 : symParity s.D s.k s.v 1=true := by simp [he] at h; exact h
    have hp := symParity_sound hp1 n
    have h1 := parityOK_sound hp
    have hn : parityOK s.D (s.k.eval n).toNat (s.v.eval n) 0=false := by
      cases hh : parityOK s.D (s.k.eval n).toNat (s.v.eval n) 0
      · rfl
      · have h0 := parityOK_sound hh; omega
    simp [leftSector,rightSector,symLeft,symRight,he,SymState.atN,hn]

private theorem symImage_at {s : SymState} {n : Nat} {w : Aff} {st : Aff×Aff} {q : Sector}
    (hD : 0<s.D) (he : symEval s.D (s.k-ac 1) w=some st) (hlo : lowerBound s.D ((s.k-ac 1).eval n).toNat (w.eval n) 0=true)
    (hp : parityOK s.D ((s.k-ac 1).eval n).toNat (w.eval n) (bp q)=true) :
    imageResidual s.D ((s.k-ac 1).eval n).toNat (z q) (w.eval n)=(symImage w st.2 (z q)).eval n ∧
    (fastStats s.D ((s.k-ac 1).eval n).toNat (w.eval n)).1=st.1.eval n := by
  obtain ⟨b,hb,_⟩ := blockRep_exists hlo hp
  have hs := symEval_sound hD he n b hb
  have hf := fastStats_correct s.D _ b _ hD hb
  unfold StatsRep at hs
  unfold imageResidual symImage
  simp only [hf,eval_add,eval_scale,eval_ac,Int.natCast_add]
  omega

private theorem symImage_next {s : SymState} {n : Nat} {w : Aff} {st : Aff×Aff} {q : Sector}
    (hD : 0<s.D) (he : symEval s.D (s.k-ac 1) (w+ac 4)=some st)
    (hlo : lowerBound s.D ((s.k-ac 1).eval n).toNat (w.eval n) 0=true)
    (hp : parityOK s.D ((s.k-ac 1).eval n).toNat (w.eval n) (bp q)=true) :
    imageResidual s.D ((s.k-ac 1).eval n).toNat (z q) (w.eval n+4)=(symImage (w+ac 4) st.2 (z q)).eval n := by
  obtain ⟨b,hb,_⟩ := blockRep_exists hlo hp
  have hb' : 2*((b+2:Nat):Int)=(s.D:Int)*3^((s.k-ac 1).eval n).toNat+(w+ac 4).eval n := by simp only [eval_add,eval_ac,Int.natCast_add]; omega
  have hs := symEval_sound hD he n (b+2) hb'
  have hf := fastStats_correct s.D _ (b+2) ((w+ac 4).eval n) hD hb'
  simp only [eval_add,eval_ac] at hf
  unfold StatsRep at hs
  unfold imageResidual symImage
  simp only [hf,eval_add,eval_scale,eval_ac,Int.natCast_add]
  omega

private theorem symRestore_at {s : SymState} {q : Sector} {w : Aff} {st : Aff×Aff} {n : Nat}
    (hj : (fastStats s.D ((s.k-ac 1).eval n).toNat (w.eval n)).1=st.1.eval n) :
    (symRestore s q w st.1).atN n=restore (s.atN n) q (w.eval n) := by
  have hk : ((s.k-ac 1).eval n).toNat=(s.k.eval n).toNat-1 := by simp
  rw [hk] at hj
  cases q <;> simp [symRestore,SymState.atN,restore,hj]

private theorem symReject_at {s : SymState} {q : Sector} {n : Nat} (h : symReject s q=true) : rejectParity (s.atN n) q=true := by
  unfold symReject at h
  unfold rejectParity SymState.atN
  simp only [Bool.or_eq_true] at *
  rcases h with h|h
  · exact Or.inl (symParity_sound h n)
  · exact Or.inr (symParity_sound h n)

/-- Every true symbolic branch covers its entire actual parent sector at every
parameter, either by contradiction or by an accepted represented child. -/
theorem symBranch_parent {s : SymState} {q : Sector} {w : Aff} {childOK : SymState→Bool}
    {n x y A b a d : Nat} (hr : Represents (s.atN n) x y) (hk : 0<(s.atN n).k) (hD : 0<s.D)
    (ha : a%2=0) (hd : d%2=dp q) (hb : b%2=bp q) (hi : y=z q+image b)
    (hj : (x:Int)=(A:Int)+drift b) (haf : affine q A b a d)
    (h : symBranch s q w childOK=true) :
    ∃ t : SymState, Represents (t.atN n) a d ∧ childOK t=true := by
  unfold symBranch at h
  cases he : symEval s.D (s.k-ac 1) w with
  | none => simp [he] at h
  | some st =>
    simp only [he,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at h
    have hlo := domAff_lower hD h.1.1 n
    have hp := symParity_sound h.1.2 n
    have hs := symImage_at (q:=q) hD he hlo hp
    have hk1 : ((s.k-ac 1).eval n).toNat=(s.atN n).k-1 := by simp [SymState.atN]
    have hy := hr.2
    rw [show (s.atN n).k=(s.atN n).k-1+1 by omega,←hk1] at hy
    change 2*(y:Int)=(s.D:Int)*3^(((s.k-ac 1).eval n).toNat+1)+s.v.eval n at hy
    rcases h.2 with hg|⟨hiteq,hrest⟩
    · unfold symGap at hg
      cases hnext : symEval s.D (s.k-ac 1) (w+ac 4) with
      | none => simp [hnext] at hg
      | some st' =>
        simp only [hnext,Bool.and_eq_true] at hg
        have hs' := symImage_next (q:=q) hD hnext hlo hp
        have hL := ge_sound hg.1 n
        have hR := ge_sound hg.2 n
        simp only [eval_sub] at hL hR
        have hg' : gapOK s.D ((s.k-ac 1).eval n).toNat (z q) (bp q) (w.eval n) (s.v.eval n)=true := by
          unfold gapOK
          simp only [hlo,hp,Bool.true_and,decide_eq_true_eq,hs.1,hs']
          omega
        exact False.elim ((gapOK_sound hy hg' b hb) hi)
    · have hhit : hitOK s.D ((s.k-ac 1).eval n).toNat (z q) (bp q) (w.eval n) (s.v.eval n)=true := by
        unfold hitOK
        simp only [hlo,hp,Bool.true_and,decide_eq_true_eq,hs.1,hiteq]
      obtain ⟨b',hrep,_,_,hu⟩ := hitOK_sound hy hhit
      have hbe := hu b hi
      subst b'
      rw [hk1] at hrep
      have hpar := restore_sound hr hk (show 0<(s.atN n).D from hD) hrep hj haf
      rw [←symRestore_at hs.2] at hpar
      rcases hrest with hrej|hc
      · exact False.elim (rejectParity_sound hpar ha hd (symReject_at hrej))
      · exact ⟨_,hpar,hc⟩

#print axioms symSectors_sound
#print axioms symBranch_parent
end BB6.Agent41NearPower
