import Q0SignedCarry
import Q0ExactHalf

namespace BB429Q0Macro.HalfStep
set_option maxHeartbeats 8000000

def stripOK (a : Nat) (s : Bool) (w : List Bool) (q e : Int) : Prop :=
  w≠[] ∧ q%2=bit s ∧ (s=false → ((a:Int)*digits w+e)%2=0) ∧
  min q 0 - 2≤3*e ∧ 3*e≤max q 0+a+2

/-- A delayed carry execution. Each transition consumes the oldest bit of
    its k-bit history and appends the chosen output bit, exactly enforcing
    the delay rather than allowing independent input bits. -/
inductive DelayTrace (a : Nat) : Bool → List Bool → Int → Int → List Bool → List Bool → Int → Int → Prop where
  | nil (s : Bool) (w : List Bool) (q e : Int) (ok : stripOK a s w q e) :
      DelayTrace a s w q e [] w q e
  | cons (s r d : Bool) {w v W : List Bool} {q e E Q F : Int}
      (ok : stripOK a s (r::w) q e)
      (he : 4*E=e+(a:Int)*bit r+(bit d:Int)*q+off s d)
      (tail : DelayTrace a (!s) (w++[d]) (q+len s d) E v W Q F) :
      DelayTrace a s (r::w) q e (d::v) W Q F

theorem DelayTrace.length_eq {a s w q e v W Q F} (h : DelayTrace a s w q e v W Q F) :
    W.length=w.length := by
  induction h with
  | nil => rfl
  | cons s r d ok he ht ih => simp at ih ⊢; omega

theorem modulus_roll (r d : Bool) (w : List Bool) : modulus (r::w)=modulus (w++[d]) := by
  rw [modulus_cons,modulus_snoc]

theorem strip_of_history {s w p y P Y} (h : ExactTrace s w p y P Y) (hne : w≠[])
    (hy : 0<y) (hc : 3*y<p) (a : Nat) (hq : 5*((P:Int)-a*modulus w)≤2*modulus w) :
    stripOK a (phase s w) w ((P:Int)-a*modulus w) ((Y:Int)-a*digits w) := by
  have hs := signed_strip h.trace hy hc a ((P:Int)-a*modulus w) (by omega) hq
  have hl := h.terminal
  have hm : modulus w%2=0 := by
    cases w with
    | nil => contradiction
    | cons d w => rw [modulus_cons]; omega
  have hpar : ((a:Int)*modulus w)%2=0 := by
    rw [Int.mul_emod,hm]; simp
  have hvalid : (P:Int)%2=bit (phase s w) := by
    have hh := hl.1
    unfold valid at hh
    omega
  refine ⟨hne,by omega,?_,hs.1,hs.2⟩
  intro hphase
  have hh := hl.2 hphase
  omega

/-- Every exact suffix of a strict k-history induces the signed delayed
    carry trace, as long as its terminal offset is at most 2M/5. -/
theorem delay_of_exact {t v p y P Y} (h : ExactTrace t v p y P Y) (a : Nat) :
    ∀ {s w p0 y0}, ExactTrace s w p0 y0 p y → phase s w=t → w≠[] →
    0<y0 → 3*y0<p0 → 5*((P:Int)-a*modulus w)≤2*modulus w →
    ∃ W, DelayTrace a t w ((p:Int)-a*modulus w) ((y:Int)-a*digits w) v W
      ((P:Int)-a*modulus w) ((Y:Int)-a*digits W) ∧ W.length=w.length := by
  induction h with
  | nil t p y hl =>
    intro s w p0 y0 hw hp hne hy hc hq
    have ok := strip_of_history hw hne hy hc a hq
    rw [hp] at ok
    exact ⟨w,.nil t w _ _ ok,rfl⟩
  | @cons t d v p y P Y hl hd ht ih =>
    intro s w p0 y0 hw hp hne hy hc hq
    have hr := trace_rank (ExactTrace.cons t d hl hd ht).trace
    have ok := strip_of_history hw hne hy hc a (by omega : 5*((p:Int)-a*modulus w)≤2*modulus w)
    rw [hp] at ok
    cases w with
    | nil => contradiction
    | cons r w =>
      cases hw with
      | @cons s r w p0 y0 p y hl0 hd0 hw =>
        have hstep : ExactTrace t [d] p y (p+len t d) (numerator t d p y/4) :=
          .cons t d hl hd (.nil (!t) _ _ ht.initial)
        have hs : phase (!s) w=t := by simpa only [phase_cons] using hp
        rw [←hs] at hstep
        have hw' := hw.append hstep
        rw [hs] at hw'
        have hs' : phase (!s) (w++[d])= !t := by rw [phase_append,hs]; cases t <;> simp [phase]
        have hne' : w++[d]≠[] := by simp
        have hM := modulus_roll r d w
        have hq' : 5*((P:Int)-a*modulus (w++[d]))≤2*modulus (w++[d]) := by rwa [←hM]
        have hpos := strict_step s r p0 y0 hy hc hd0
        obtain ⟨W,hD,hW⟩ := ih hw' hs' hne' hpos.1 hpos.2 hq'
        have hp' : ((p+len t d:Nat):Int)-a*modulus (w++[d])=((p:Int)-a*modulus (r::w))+len t d := by
          rw [←hM]; omega
        have hn : 4*((numerator t d p y/4:Nat):Int)=(y:Int)+(bit d:Int)*p+off t d := by
          have hn₁ : 4*((numerator t d p y/4:Nat):Int)=(numerator t d p y:Int) := by omega
          simpa [numerator] using hn₁
        have he : 4*(((numerator t d p y/4:Nat):Int)-a*digits (w++[d])) =
          ((y:Int)-a*digits (r::w))+(a:Int)*bit r+(bit d:Int)*((p:Int)-a*modulus (r::w))+off t d := by
          rw [digits_snoc,digits,modulus_cons]
          grind
        rw [hp',←hM] at hD
        exact ⟨W,.cons t r d ok he hD,by simp at hW ⊢; omega⟩

/-- The carry equations are an exact reconstruction, not an approximation.
    Any delay trace with natural decoded initial coordinates reconstructs
    an exact half trace, including the intermediate lattice conditions. -/
theorem exact_of_delay {a s w q e v W Q F} (h : DelayTrace a s w q e v W Q F) :
    ∀ p y : Nat, (p:Int)=a*modulus w+q → (y:Int)=a*digits w+e →
    ∃ P Y : Nat, ExactTrace s v p y P Y ∧
      (P:Int)=a*modulus W+Q ∧ (Y:Int)=a*digits W+F := by
  induction h with
  | nil s w q e ok =>
    intro p y hp hy
    have hm : modulus w%2=0 := by
      cases w with
      | nil => exact False.elim (ok.1 rfl)
      | cons r w => rw [modulus_cons]; omega
    have ha : ((a:Int)*modulus w)%2=0 := by rw [Int.mul_emod,hm]; simp
    have hl : lattice s p y := by
      refine ⟨?_,?_⟩
      · unfold valid
        have hh := ok.2.1
        omega
      · intro hs
        have hh := ok.2.2.1 hs
        omega
    exact ⟨p,y,.nil s p y hl,hp,hy⟩
  | @cons s r d w v W q e E Q F ok he ht ih =>
    intro p y hp hy
    have hm : modulus (r::w)%2=0 := by rw [modulus_cons]; omega
    have ha : ((a:Int)*modulus (r::w))%2=0 := by rw [Int.mul_emod,hm]; simp
    have hl : lattice s p y := by
      refine ⟨?_,?_⟩
      · unfold valid
        have hh := ok.2.1
        omega
      · intro hs
        have hh := ok.2.2.1 hs
        omega
    have hM := modulus_roll r d w
    have hp' : ((p+len s d:Nat):Int)=a*modulus (w++[d])+(q+len s d) := by rw [←hM]; omega
    have hn : 4*((a:Int)*digits (w++[d])+E)=(numerator s d p y:Int) := by
      simp only [numerator,Int.natCast_add,Int.natCast_mul]
      rw [hp,hy,digits_snoc,digits,modulus_cons]
      grind
    have hd : numerator s d p y%4=0 := by omega
    have hy' : ((numerator s d p y/4:Nat):Int)=a*digits (w++[d])+E := by omega
    obtain ⟨P,Y,htrace,hP,hY⟩ := ih _ _ hp' hy'
    exact ⟨P,Y,.cons s d hl hd htrace,hP,hY⟩

#print axioms delay_of_exact
#print axioms exact_of_delay
end BB429Q0Macro.HalfStep
