import Frontier
import Lean.Elab.Tactic.Omega

namespace BB6Bubble
open BB6Coverage

private def A : Fin 6 := ⟨0, by decide⟩
private def B : Fin 6 := ⟨1, by decide⟩
private def F : Fin 6 := ⟨5, by decide⟩

def zeroTest (h x : Int) (k : Nat) : Prop :=
  0 ≤ h - x ∧ h - x < 2 * (k : Int) ∧ (h - x) % 2 = 0

instance zeroTestDecidable (h x : Int) (k : Nat) : Decidable (zeroTest h x k) := by
  unfold zeroTest
  infer_instance

def zeroPaint (t : Int → Bool) (h : Int) (k : Nat) : Int → Bool :=
  fun x => if zeroTest h x k then false else t x

theorem zeroTest_next (h x : Int) (k : Nat)
    (hne : x ≠ h - 2 * (k : Int)) :
    zeroTest h x (k+1) ↔ zeroTest h x k := by
  unfold zeroTest
  constructor <;> intro hh
  · rcases hh with ⟨a,b,c⟩
    constructor
    · omega
    constructor
    · omega
    · omega
  · rcases hh with ⟨a,b,c⟩
    constructor
    · omega
    constructor
    · omega
    · omega

theorem zeroPaint_next (t : Int → Bool) (h : Int) (k : Nat) :
    zeroPaint t h (k+1) = fun x => if x = h-2*(k:Int) then false else zeroPaint t h k x := by
  funext x
  by_cases hx : x = h-2*(k:Int)
  · have hh : zeroTest h x (k+1) := by
      subst x
      unfold zeroTest
      omega
    simp only [zeroPaint, if_pos hh, if_pos hx]
  · have hi := zeroTest_next h x k hx
    by_cases test : zeroTest h x k
    · have test' : zeroTest h x (k+1) := hi.mpr test
      simp only [zeroPaint, if_pos test, if_pos test', if_neg hx]
    · have test' : ¬zeroTest h x (k+1) := fun v => test (hi.mp v)
      simp only [zeroPaint, if_neg test, if_neg test', if_neg hx]

theorem zeroPaint_zero (t : Int → Bool) (h : Int) : zeroPaint t h 0 = t := by
  funext x
  change (if zeroTest h x 0 then false else t x) = t x
  have hh : ¬zeroTest h x 0 := by unfold zeroTest; omega
  simp [hh]

theorem zeroPaint_outside (t : Int → Bool) (h : Int) (k : Nat) (x : Int)
    (hbelow : x ≤ h-2*(k:Int)) : zeroPaint t h k x = t x := by
  change (if zeroTest h x k then false else t x) = t x
  have hh : ¬zeroTest h x k := by unfold zeroTest; omega
  simp [hh]

theorem zeroPaint_odd (t : Int → Bool) (h : Int) (k : Nat) :
    zeroPaint t h k (h-2*(k:Int)-1) = t (h-2*(k:Int)-1) := by
  apply zeroPaint_outside
  omega

theorem run_add' (m : Machine) (a b : Nat) (c : Config) :
    run m (a+b) c = (run m a c).bind (fun d => run m b d) := by
  induction b with
  | zero => simp [run]
  | succ b ih =>
    calc
      run m (a+(b+1)) c = (run m (a+b) c).bind (rawStep m) := by rfl
      _ = ((run m a c).bind (fun d => run m b d)).bind (rawStep m) := by rw [ih]
      _ = (run m a c).bind (fun d => run m (b+1) d) := by
        cases h : run m a c with
        | none => simp [h]
        | some d => simp [h,run]

theorem run_two_AF (m : Machine) (h : Int) (t : Int → Bool)
    (hmA : m (A,true)=some ⟨false,false,F⟩)
    (hmF : m (F,true)=some ⟨true,false,A⟩)
    (h0 : t h=true) (h1 : t (h-1)=true) :
    run m 2 {state:=A,head:=h,tape:=t} =
      some {state:=A,head:=h-2,tape:=fun x => if x=h then false else t x} := by
  let c : Config := {state:=A,head:=h,tape:=t}
  let a : Move := ⟨false,false,F⟩
  let f : Move := ⟨true,false,A⟩
  have ha : rawStep m c = some (applyMove c a) := by
    simp [rawStep,readSlot,hmA,h0,c,a]
  have hread : (applyMove c a).tape ((applyMove c a).head) = true := by
    have hn : h + (-1) = h-1 := by omega
    have hh : ¬(h-1=h) := by omega
    simp only [applyMove,c,a,ite_false]
    exact (if_neg (by omega : ¬(h + -1 = h))).trans (by simpa [hn] using h1)
  have hf : rawStep m (applyMove c a) = some (applyMove (applyMove c a) f) := by
    simp only [rawStep,readSlot,hread]
    have hs : (applyMove c a).state = F := rfl
    rw [hs, hmF]
    rfl
  change (rawStep m c).bind (rawStep m) = _
  rw [ha]
  simp only [Option.bind_some,hf]
  apply congrArg some
  dsimp [applyMove,c,a,f]
  congr 1
  · omega
  · funext x
    by_cases hx : x = h-1
    · subst x
      have hn : h-1 ≠ h := by omega
      simp [hn,h1]
    · have hn : x ≠ h+(-1) := by omega
      simp [hn]

theorem AF_sweep (m : Machine) (h : Int) (t : Int → Bool) (k : Nat)
    (hmA : m (A,true)=some ⟨false,false,F⟩)
    (hmF : m (F,true)=some ⟨true,false,A⟩)
    (hones : ∀ i : Nat, i < 2*k → t (h-(i:Int)) = true) :
    run m (2*k) {state:=A,head:=h,tape:=t} =
      some {state:=A,head:=h-2*(k:Int),tape:=zeroPaint t h k} := by
  induction k with
  | zero => simp [run,zeroPaint_zero]
  | succ k ih =>
    have hprefix : ∀ i : Nat, i < 2*k → t (h-(i:Int)) = true := by
      intro i hi
      exact hones i (by omega)
    have hp := ih hprefix
    have hx0 : zeroPaint t h k (h-2*(k:Int))=true := by
      rw [zeroPaint_outside t h k (h-2*(k:Int)) (by omega)]
      simpa using hones (2*k) (by omega)
    have hx1 : zeroPaint t h k (h-2*(k:Int)-1)=true := by
      rw [zeroPaint_odd]
      have hh := hones (2*k+1) (by omega)
      have ht : h-(↑(2*k+1):Int)=h-2*(k:Int)-1 := by omega
      simpa only [ht] using hh
    have h2 := run_two_AF m (h-2*(k:Int)) (zeroPaint t h k) hmA hmF hx0 hx1
    have hl : 2*(k+1)=2*k+2 := by omega
    rw [hl, run_add', hp]
    simp only [Option.bind_some, h2]
    apply congrArg some
    dsimp
    congr 1
    · omega
    · exact (zeroPaint_next t h k).symm

def oneTest (l x : Int) (k : Nat) : Prop :=
  0 ≤ x-l ∧ x-l < 2*(k:Int) ∧ (x-l)%2=0

instance oneTestDecidable (l x : Int) (k : Nat) : Decidable (oneTest l x k) := by
  unfold oneTest
  infer_instance

def onePaint (t : Int → Bool) (l : Int) (k : Nat) : Int → Bool :=
  fun x => if oneTest l x k then true else t x

theorem oneTest_next (l x : Int) (k : Nat)
    (hne : x ≠ l + 2 * (k : Int)) :
    oneTest l x (k+1) ↔ oneTest l x k := by
  unfold oneTest
  constructor <;> intro hh
  · rcases hh with ⟨a,b,c⟩
    constructor
    · omega
    constructor
    · omega
    · omega
  · rcases hh with ⟨a,b,c⟩
    constructor
    · omega
    constructor
    · omega
    · omega

theorem onePaint_next (t : Int → Bool) (l : Int) (k : Nat) :
    onePaint t l (k+1) = fun x => if x = l+2*(k:Int) then true else onePaint t l k x := by
  funext x
  by_cases hx : x = l+2*(k:Int)
  · have hh : oneTest l x (k+1) := by
      subst x
      unfold oneTest
      omega
    simp only [onePaint, if_pos hh, if_pos hx]
  · have hi := oneTest_next l x k hx
    by_cases test : oneTest l x k
    · have test' : oneTest l x (k+1) := hi.mpr test
      simp only [onePaint, if_pos test, if_pos test', if_neg hx]
    · have test' : ¬oneTest l x (k+1) := fun v => test (hi.mp v)
      simp only [onePaint, if_neg test, if_neg test', if_neg hx]

theorem onePaint_zero (t : Int → Bool) (l : Int) : onePaint t l 0 = t := by
  funext x
  change (if oneTest l x 0 then true else t x) = t x
  have hh : ¬oneTest l x 0 := by unfold oneTest; omega
  simp [hh]

theorem onePaint_outside (t : Int → Bool) (l : Int) (k : Nat) (x : Int)
    (hbelow : l+2*(k:Int) ≤ x) : onePaint t l k x = t x := by
  change (if oneTest l x k then true else t x) = t x
  have hh : ¬oneTest l x k := by unfold oneTest; omega
  simp [hh]

theorem onePaint_odd (t : Int → Bool) (l : Int) (k : Nat) :
    onePaint t l k (l+2*(k:Int)+1) = t (l+2*(k:Int)+1) := by
  apply onePaint_outside
  omega

theorem run_two_AB (m : Machine) (h : Int) (t : Int → Bool)
    (hmA : m (A,false)=some ⟨true,true,B⟩)
    (hmB : m (B,true)=some ⟨true,true,A⟩)
    (h0 : t h=false) (h1 : t (h+1)=true) :
    run m 2 {state:=A,head:=h,tape:=t} =
      some {state:=A,head:=h+2,tape:=fun x => if x=h then true else t x} := by
  let c : Config := {state:=A,head:=h,tape:=t}
  let a : Move := ⟨true,true,B⟩
  let b : Move := ⟨true,true,A⟩
  have ha : rawStep m c = some (applyMove c a) := by
    simp [rawStep,readSlot,hmA,h0,c,a]
  have hread : (applyMove c a).tape ((applyMove c a).head) = true := by
    have hn : h + 1 = h+1 := by omega
    simp only [applyMove,c,a,ite_true]
    exact (if_neg (by omega : ¬(h + 1 = h))).trans (by simpa [hn] using h1)
  have hb : rawStep m (applyMove c a) = some (applyMove (applyMove c a) b) := by
    simp only [rawStep,readSlot,hread]
    have hs : (applyMove c a).state = B := rfl
    rw [hs, hmB]
    rfl
  change (rawStep m c).bind (rawStep m) = _
  rw [ha]
  simp only [Option.bind_some,hb]
  apply congrArg some
  dsimp [applyMove,c,a,b]
  congr 1
  · omega
  · funext x
    by_cases hx : x = h+1
    · subst x
      have hn : h+1 ≠ h := by omega
      simp [hn,h1]
    · have hn : x ≠ h+1 := by omega
      simp [hn]

theorem AB_sweep (m : Machine) (l : Int) (t : Int → Bool) (k : Nat)
    (hmA : m (A,false)=some ⟨true,true,B⟩)
    (hmB : m (B,true)=some ⟨true,true,A⟩)
    (heven : ∀ i : Nat, i < k → t (l+2*(i:Int)) = false)
    (hodd : ∀ i : Nat, i < k → t (l+2*(i:Int)+1) = true) :
    run m (2*k) {state:=A,head:=l,tape:=t} =
      some {state:=A,head:=l+2*(k:Int),tape:=onePaint t l k} := by
  induction k with
  | zero => simp [run,onePaint_zero]
  | succ k ih =>
    have hprefix : ∀ i : Nat, i < k → t (l+2*(i:Int)) = false := by
      intro i hi
      exact heven i (by omega)
    have hprefix' : ∀ i : Nat, i < k → t (l+2*(i:Int)+1) = true := by
      intro i hi
      exact hodd i (by omega)
    have hp := ih hprefix hprefix'
    have hx0 : onePaint t l k (l+2*(k:Int))=false := by
      rw [onePaint_outside t l k (l+2*(k:Int)) (by omega)]
      exact heven k (by omega)
    have hx1 : onePaint t l k (l+2*(k:Int)+1)=true := by
      rw [onePaint_odd]
      exact hodd k (by omega)
    have h2 := run_two_AB m (l+2*(k:Int)) (onePaint t l k) hmA hmB hx0 hx1
    have hl : 2*(k+1)=2*k+2 := by omega
    rw [hl, run_add', hp]
    simp only [Option.bind_some, h2]
    apply congrArg some
    dsimp
    congr 1
    · omega
    · exact (onePaint_next t l k).symm

/-- Rightward repaint restores the matching preceding leftward erase,
    apart from the initially empty cell. -/
theorem paint_merge (t : Int → Bool) (h l : Int) (q : Nat)
    (hl : l = h-2*(q:Int))
    (hones : ∀ x : Int, l < x → x ≤ h+1 → t x=true) :
    onePaint (zeroPaint t h q) l (q+1) =
      fun x => if x=l then true else t x := by
  funext x
  by_cases hx : x=l
  · subst x
    have h1 : oneTest l l (q+1) := by unfold oneTest; omega
    simp only [onePaint, if_pos h1, ↓reduceIte]
  · have heq : oneTest l x (q+1) ↔ zeroTest h x q := by
      unfold oneTest zeroTest
      omega
    by_cases htest : oneTest l x (q+1)
    · have hzero : zeroTest h x q := heq.mp htest
      have hone : t x = true := hones x (by unfold oneTest at htest; omega) (by unfold oneTest at htest; omega)
      simp only [onePaint, if_pos htest, if_neg hx, hone]
    · have hzero : ¬zeroTest h x q := fun v => htest (heq.mpr v)
      simp only [onePaint, zeroPaint, if_neg htest, if_neg hzero, if_neg hx]

/-- One exact A/F left sweep and A/B right sweep removes an isolated zero.
    For any six-state machine with these four literal rules, the total
    primitive runtime is exactly 4*q+2. -/
theorem bubble_exact (m : Machine) (h l : Int) (q : Nat) (t : Int → Bool)
    (hmA1 : m (A,true)=some ⟨false,false,F⟩)
    (hmF1 : m (F,true)=some ⟨true,false,A⟩)
    (hmA0 : m (A,false)=some ⟨true,true,B⟩)
    (hmB1 : m (B,true)=some ⟨true,true,A⟩)
    (hl : l = h-2*(q:Int))
    (hzero : t l=false)
    (hones : ∀ x : Int, l < x → x ≤ h+1 → t x=true) :
    run m (4*q+2) {state:=A,head:=h,tape:=t} =
      some {state:=A,head:=h+2,tape:=fun x => if x=l then true else t x} := by
  have hp : ∀ i : Nat, i < 2*q → t (h-(i:Int))=true := by
    intro i hi
    apply hones
    · omega
    · omega
  have hAF := AF_sweep m h t q hmA1 hmF1 hp
  have hEven : ∀ i : Nat, i < q+1 → zeroPaint t h q (l+2*(i:Int))=false := by
    intro i hi
    by_cases hiz : i=0
    · subst i
      have hf : zeroPaint t h q l = t l := zeroPaint_outside t h q l (by omega)
      simpa using hf.trans hzero
    · have hz : zeroTest h (l+2*(i:Int)) q := by
        unfold zeroTest
        omega
      simp [zeroPaint,hz]
  have hOdd : ∀ i : Nat, i < q+1 → zeroPaint t h q (l+2*(i:Int)+1)=true := by
    intro i hi
    have hz : ¬zeroTest h (l+2*(i:Int)+1) q := by
      unfold zeroTest
      omega
    rw [show zeroPaint t h q (l+2*(i:Int)+1) = t (l+2*(i:Int)+1) from by simp [zeroPaint,hz]]
    apply hones
    · omega
    · omega
  have hAB := AB_sweep m l (zeroPaint t h q) (q+1) hmA0 hmB1 hEven hOdd
  have hn : 4*q+2 = 2*q+2*(q+1) := by omega
  rw [hn,run_add',hAF]
  simp only [Option.bind_some]
  have hh : h-2*(q:Int)=l := hl.symm
  have hAB' :
      run m (2*(q+1)) {state:=A,head:=h-2*(q:Int),tape:=zeroPaint t h q} =
        some {state:=A,head:=l+2*((q+1 : Nat):Int),tape:=onePaint (zeroPaint t h q) l (q+1)} := by
    simpa only [hh] using hAB
  rw [hAB']
  apply congrArg some
  dsimp
  congr 1
  · omega
  · exact paint_merge t h l q hl hones

#print axioms AF_sweep
#print axioms AB_sweep
#print axioms paint_merge
#print axioms bubble_exact
end BB6Bubble
