import Raw13DrainCore

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13CoupledDrain
open BB6.Agent46Raw13RightCounter
open BB6.Agent46Raw13CounterBudget
open BB6.Agent46Raw13DrainCore
open BB6.Agent46Raw13TapeValue (F Reach reach_trans)

theorem ones_add (n m : Nat) : ones (n+m) = ones n ++ ones m :=
  BB6.Agent46Raw13Frames.ones_add n m

theorem drainOdd (h : Nat) (bs P V : List Bool) (b : Nat) (hb : enough P b) :
    Reach (D h (true::bs) (P++V)) (D 0 bs ((true::zeros (3*h)++true::P)++V)) ∧
      enough (true::zeros (3*h)++true::P) b := by
  have h1 := special0Step (3*h) ([false,false,false]++encBits bs) (P++V)
  have h2 := mainPos 0 0 ([false,false]++encBits bs) (zeros (3*h)++true::(P++V))
  rw [show 2*(3*h)=6*h by omega] at h1
  have hr := reach_trans h1 h2
  constructor
  · simpa only [D,encBits,ones,zeros,Nat.mul_zero,Nat.zero_mul,Nat.add_zero,
      List.replicate_zero,List.replicate_succ,List.cons_append,List.singleton_append,List.nil_append,List.append_assoc] using hr
  · have h := enough_prepend (true::zeros (3*h)++[true]) P b hb
    simpa only [List.cons_append,List.singleton_append,List.append_assoc,List.nil_append] using h

theorem U0_cons (bs : List Bool) : U0 bs = false::[false,false,true,false,false,false]++encBits bs := rfl
theorem U1_cons (bs : List Bool) : U1 bs = true::[false,false,true,false,false,false]++encBits bs := rfl

theorem overflowFirst (s : Nat) (bs P V : List Bool) (b : Nat) (hb : enough P (b+1)) :
    ∃ P', Reach (F (encode (s+1) (2^(s+1)-1)++U0 bs) (P++V))
      (F (encode (s+1) 1++U1 bs) (P'++V)) ∧ enough P' b := by
  let X := [false,false,true,false,false,false]++encBits bs
  obtain ⟨j,T,P',h1,hP,hb'⟩ := mainFirst (s+1) X P V b hb
  have h2 := mainPos (3*j+2) 0 (zeros (4*s+3)++U1 bs) (T++V)
  have hz : zeros (4*(s+1)) = false::zeros (4*s+3) := by
    rw [show 4*(s+1)=4*s+3+1 by omega]; rfl
  have ho : encode (s+1) 1 = true::zeros (4*s+3) := by
    rw [encode_one,show 4*s+3=3+4*s by omega,zeros_add 3 (4*s)]
    rfl
  have hlen : 2*(3*j+2+1)=6*(j+1) := by omega
  rw [hlen] at h2
  rw [hz,List.append_assoc] at h1
  change Reach (F (oneBlocks (s+1)++U0 bs) (P++V))
    (F (ones (6*(j+1))++false::(zeros (4*s+3)++U1 bs)) (T++V)) at h1
  simp only [oneBlocks,List.append_nil,Nat.mul_zero] at h2
  change Reach (F (ones (6*(j+1))++false::(zeros (4*s+3)++U1 bs)) (T++V))
    (F (true::(zeros (4*s+3)++U1 bs)) (zeros (3*j+2)++true::(T++V))) at h2
  rw [← encode_max] at h1
  have hr := reach_trans h1 h2
  have hl : true::(zeros (4*s+3)++U1 bs) = encode (s+1) 1++U1 bs := by rw [ho]; rfl
  have hrw : zeros (3*j+2)++true::(T++V) = P'++V := by rw [hP,List.append_assoc]; rfl
  rw [hl,hrw] at hr
  exact ⟨P',hr,hb'⟩

theorem overflowSecond (s : Nat) (bs P V : List Bool) (b : Nat) (hb : enough P (b+1)) :
    ∃ P', Reach (F (encode (s+1) (2^(s+1)-2)++U0 bs) (P++V))
      (F (encode (s+1) 0++U1 bs) (P'++V)) ∧ enough P' b := by
  have hp : 0<2^s := Nat.two_pow_pos s
  have ht : 2^(s+1)-2+1 = 2^(s+1)-1 := by rw [Nat.pow_succ]; omega
  obtain ⟨j,T,P',h1,hP,hb'⟩ := firstCarry (s+1) (2^(s+1)-2) (U0 bs) P V b (by omega) hb
  rw [ht,encode_max] at h1
  have h2 := mainPos (3*j+2) (s+1) ([false,false,true,false,false,false]++encBits bs) (T++V)
  rw [show 2*(3*j+2+1)=6*(j+1) by omega,List.append_assoc] at h2
  change Reach (F (ones (6*(j+1))++(oneBlocks (s+1)++U0 bs)) (T++V))
    (F (zeros (4*(s+1))++U1 bs) (zeros (3*j+2)++true::(T++V))) at h2
  have hrw : zeros (3*j+2)++true::(T++V) = P'++V := by rw [hP,List.append_assoc]; rfl
  rw [← encode_zero,hrw] at h2
  exact ⟨P',reach_trans h1 h2,hb'⟩

theorem scan_prefix (H δ : Nat) (hH : 0<H) (hd : δ≤2) (W : List Bool) :
    scan (ones (3*H-δ)++zeros δ++W) = (6*H+(scan W).1,(scan W).2) := by
  induction H with
  | zero => omega
  | succ H ih =>
    by_cases hz : H=0
    · subst H
      have hδ : δ=0 ∨ δ=1 ∨ δ=2 := by omega
      rcases hδ with rfl|rfl|rfl <;> rfl
    · have he : 3*(H+1)-δ = 3+(3*H-δ) := by omega
      rw [he,ones_add 3 (3*H-δ),List.append_assoc,List.append_assoc]
      change scan (true::true::true::(ones (3*H-δ)++(zeros δ++W))) = _
      rw [scan,← List.append_assoc,ih (by omega)]
      congr 1 <;> omega

theorem scan_mixed (s k : Nat) (W : List Bool) :
    let H := (2*s+3)/3
    let δ := 3*H-(2*s+1)
    scan (ones (2*s+1)++zeros (k+2)++true::W) =
      (6*H+(scan (zeros (k+2-δ)++true::W)).1,(scan (zeros (k+2-δ)++true::W)).2) := by
  dsimp only
  let H := (2*s+3)/3
  let δ := 3*H-(2*s+1)
  have hH : 0<H := by dsimp [H]; omega
  have hd : δ≤2 := by dsimp [δ,H]; omega
  have h1 : 2*s+1 = 3*H-δ := by dsimp [δ,H]; omega
  have h2 : k+2 = δ+(k+2-δ) := by omega
  have he : ones (2*s+1)++zeros (k+2)++true::W =
      ones (3*H-δ)++zeros δ++(zeros (k+2-δ)++true::W) := by
    rw [← h1]
    have hz : zeros (k+2) = zeros δ++zeros (k+2-δ) := by rw [← zeros_add,← h2]
    rw [hz]
    simp only [List.append_assoc]
  rw [he]
  exact scan_prefix H δ hH hd (zeros (k+2-δ)++true::W)

def H (s : Nat) := (2*s+3)/3
def delta (s : Nat) := 3*H s-(2*s+1)

theorem delta_le (s : Nat) : delta s ≤ 2 := by unfold delta H; omega

theorem scan_mixed_stop (s k : Nat) (W : List Bool) (hd : delta s < k+2) :
    scan (ones (2*s+1)++zeros (k+2)++true::W) = (6*H s, zeros (k+1-delta s)++true::W) := by
  have h := scan_mixed s k W
  change scan (ones (2*s+1)++zeros (k+2)++true::W) =
    (6*H s+(scan (zeros (k+2-delta s)++true::W)).1,(scan (zeros (k+2-delta s)++true::W)).2) at h
  have hz : zeros (k+2-delta s) = false::zeros (k+1-delta s) := by
    rw [show k+2-delta s=k+1-delta s+1 by omega]; rfl
  rw [hz] at h
  simpa only [List.cons_append,scan,Nat.add_zero] using h

theorem scan_mixed_continue (s : Nat) (W : List Bool) (hd : delta s = 2) :
    scan (ones (2*s+1)++zeros 2++true::W) =
      (6*H s+(scan (true::W)).1,(scan (true::W)).2) := by
  have h := scan_mixed s 0 W
  change scan (ones (2*s+1)++zeros 2++true::W) =
    (6*H s+(scan (zeros (2-delta s)++true::W)).1,(scan (zeros (2-delta s)++true::W)).2) at h
  rw [hd] at h
  exact h

theorem finish (h : Nat) (bs W : List Bool) :
    Reach (F (ones (6*h)++true::true::false::false::false::encBits bs) W)
      (D 0 bs (zeros (3*h)++true::W)) := by
  have hr := mainPos (3*h) 0 ([false,false]++encBits bs) W
  rw [show 2*(3*h+1)=6*h+2 by omega,ones_add] at hr
  simpa only [D,oneBlocks,Nat.mul_zero,zeros,ones,Nat.zero_mul,List.replicate_zero,List.nil_append,
    List.append_nil,List.append_assoc,List.replicate_succ,List.cons_append,List.singleton_append] using hr

theorem specialFinish (s k h : Nat) (bs W T : List Bool)
    (hs : scan (ones (2*s+1)++zeros (k+2)++true::W) = (6*h,T)) :
    Reach (F (ones (2*k)++oneBlocks (s+1)++U1 bs) W)
      (D 0 bs (zeros (3*h)++true::T)) := by
  have h1 := specialStep k s ([false,false,false]++encBits bs) W
  rw [hs] at h1
  exact reach_trans h1 (finish h bs T)

theorem finishZero (s : Nat) (bs P V : List Bool) (b : Nat) (hb : enough P (b+1)) :
    ∃ P', Reach (F (encode (s+1) (2^(s+1)-1)++U1 bs) (P++V)) (D 0 bs (P'++V)) ∧ enough P' b := by
  rw [encode_max]
  by_cases hd : delta s=2
  · obtain ⟨j,T,P',hscan,hP,hb'⟩ := scan_spend P V b hb
    have hs := scan_mixed_continue s (P++V) hd
    rw [hscan] at hs
    have he : 6*H s+6*(j+1)=6*(H s+j+1) := by omega
    rw [he] at hs
    have hr := specialFinish s 0 (H s+j+1) bs (P++V) (T++V) hs
    have hrw : zeros (3*(H s+j+1))++true::(T++V) = (zeros (3*H s+1)++P')++V := by
      rw [hP,show 3*(H s+j+1)=3*H s+1+(3*j+2) by omega,zeros_add (3*H s+1) (3*j+2)]
      simp only [List.append_assoc,List.cons_append]
    rw [hrw] at hr
    exact ⟨zeros (3*H s+1)++P',hr,enough_prepend _ _ _ hb'⟩
  · have hδ := delta_le s
    have hs := scan_mixed_stop s 0 (P++V) (by omega)
    have hr := specialFinish s 0 (H s) bs (P++V) (zeros (1-delta s)++true::(P++V)) hs
    let Q := zeros (3*H s)++true::(zeros (1-delta s)++[true])
    have hrw : zeros (3*H s)++true::(zeros (1-delta s)++true::(P++V)) = (Q++P)++V := by
      simp only [Q,List.append_assoc,List.cons_append,List.nil_append]
    rw [hrw] at hr
    exact ⟨Q++P,hr,enough_prepend _ _ _ (enough_mono hb (by omega))⟩

theorem finishAfterCarry (s j : Nat) (bs T P V : List Bool) (b : Nat)
    (hP : P=zeros (3*j+2)++true::T) (hb : enough P b) :
    ∃ P', Reach (F (ones (6*(j+1))++(oneBlocks (s+1)++U1 bs)) (T++V))
      (D 0 bs (P'++V)) ∧ enough P' b := by
  have hδ := delta_le s
  have hs := scan_mixed_stop s (3*(j+1)) (T++V) (by omega)
  have hr := specialFinish s (3*(j+1)) (H s) bs (T++V)
    (zeros (3*(j+1)+1-delta s)++true::(T++V)) hs
  rw [show 2*(3*(j+1))=6*(j+1) by omega,List.append_assoc] at hr
  let Q := zeros (3*H s)++true::zeros (2-delta s)
  have hrw : zeros (3*H s)++true::(zeros (3*(j+1)+1-delta s)++true::(T++V)) = (Q++P)++V := by
    rw [hP,show 3*(j+1)+1-delta s=(2-delta s)+(3*j+2) by omega,zeros_add (2-delta s) (3*j+2)]
    simp only [Q,List.append_assoc,List.cons_append]
  rw [hrw] at hr
  exact ⟨Q++P,hr,enough_prepend _ _ _ hb⟩

theorem drainEvenZero (s : Nat) (bs P V : List Bool) (b : Nat) (hb : enough P (b+2^(s+1))) :
    ∃ P', Reach (D 0 (zeros (s+1)++true::bs) (P++V)) (D 0 bs (P'++V)) ∧ enough P' b := by
  let N := 2^s
  have hp : 0<N := Nat.two_pow_pos s
  have hm : 2^(s+1)=2*N := by simp [N,Nat.pow_succ,Nat.mul_comm]
  have hmax : 1+2*(N-1)=2^(s+1)-1 := by omega
  have hbound : 1+2*(N-1)<2^(s+1) := by omega
  have hd := D_even 0 (s+1) bs (P++V) (by omega)
  simp only [Nat.mul_zero,ones,List.replicate_zero,List.nil_append] at hd
  rw [hd]
  obtain ⟨P1,h1,b1⟩ := jumpBudget (s+1) 1 (N-1) (U0 bs) P V (b+N+1) hbound
    (enough_mono hb (by omega))
  rw [hmax] at h1
  obtain ⟨P2,h2,b2⟩ := overflowFirst s bs P1 V (b+N) b1
  obtain ⟨P3,h3,b3⟩ := jumpBudget (s+1) 1 (N-1) (U1 bs) P2 V (b+1) hbound
    (enough_mono b2 (by omega))
  rw [hmax] at h3
  obtain ⟨P4,h4,b4⟩ := finishZero s bs P3 V b b3
  exact ⟨P4,reach_trans (reach_steps (steps_reach h1 h2) h3) h4,b4⟩

theorem initialEvenPositive (h s : Nat) (bs P V : List Bool) (b : Nat) (hh : 0<h)
    (hb : enough P (b+(2^s-1))) :
    ∃ P', Reach (D h (zeros (s+1)++true::bs) (P++V))
      (F (encode (s+1) 0++U1 bs) (P'++V)) ∧ enough P' b := by
  rw [D_even h (s+1) bs (P++V) (by omega)]
  let Q := zeros (3*h-1)++[true]
  have hQ : zeros (3*h-1)++true::(P++V) = (Q++P)++V := by
    simp only [Q,List.append_assoc,List.cons_append,List.nil_append]
  have hbQ := enough_prepend Q P _ hb
  cases s with
  | zero =>
    have hr := mainPos (3*h-1) 1 ([false,false,true,false,false,false]++encBits bs) (P++V)
    rw [show 2*(3*h-1+1)=6*h by omega,List.append_assoc,hQ] at hr
    change Reach (F (ones (6*h)++(encode 1 1++U0 bs)) (P++V))
      (F (encode 1 0++U1 bs) ((Q++P)++V)) at hr
    exact ⟨Q++P,hr,by simpa using hbQ⟩
  | succ s =>
    let N := 2^(s+1)
    have hp : 0<2^s := Nat.two_pow_pos s
    have hn : 2≤N := by unfold N; rw [Nat.pow_succ]; omega
    have hm : 2^(s+1+1)=2*N := by simp [N,Nat.pow_succ,Nat.mul_comm]
    have h2 := positiveCarry h (s+1+1) 1 (U0 bs) (P++V) hh (by omega)
    rw [hQ] at h2
    have hbound : 2+2*(N-2)<2^(s+1+1) := by omega
    obtain ⟨P2,hr,b2⟩ := jumpBudget (s+1+1) 2 (N-2) (U0 bs) (Q++P) V (b+1) hbound
      (enough_mono hbQ (by omega))
    rw [show 2+2*(N-2)=2^(s+1+1)-2 by omega] at hr
    obtain ⟨P3,h3,b3⟩ := overflowSecond (s+1) bs P2 V b b2
    exact ⟨P3,reach_trans (reach_steps h2 hr) h3,b3⟩

theorem finalEvenPositive (s : Nat) (bs P V : List Bool) (b : Nat) (hb : enough P (b+2^s)) :
    ∃ P', Reach (F (encode (s+1) 0++U1 bs) (P++V)) (D 0 bs (P'++V)) ∧ enough P' b := by
  let N := 2^s
  have hp : 0<N := Nat.two_pow_pos s
  have hm : 2^(s+1)=2*N := by simp [N,Nat.pow_succ,Nat.mul_comm]
  have hbound : 0+2*(N-1)<2^(s+1) := by omega
  obtain ⟨P1,h1,b1⟩ := jumpBudget (s+1) 0 (N-1) (U1 bs) P V (b+1) hbound
    (enough_mono hb (by omega))
  rw [show 0+2*(N-1)=2^(s+1)-2 by omega] at h1
  obtain ⟨j,T,P2,h2,hP,b2⟩ := firstCarry (s+1) (2^(s+1)-2) (U1 bs) P1 V b (by omega) b1
  rw [show 2^(s+1)-2+1=2^(s+1)-1 by omega,encode_max] at h2
  obtain ⟨P3,h3,b3⟩ := finishAfterCarry s j bs T P2 V b hP b2
  exact ⟨P3,reach_trans (steps_reach h1 h2) h3,b3⟩

theorem drainEven (h s : Nat) (bs P V : List Bool) (b : Nat) (hb : enough P (b+2^(s+1))) :
    ∃ P', Reach (D h (zeros (s+1)++true::bs) (P++V)) (D 0 bs (P'++V)) ∧ enough P' b := by
  by_cases hh : h=0
  · subst h; exact drainEvenZero s bs P V b hb
  · have hp : 0<2^s := Nat.two_pow_pos s
    have hm : 2^(s+1)=2*2^s := by rw [Nat.pow_succ,Nat.mul_comm]
    obtain ⟨P1,h1,b1⟩ := initialEvenPositive h s bs P V (b+2^s) (by omega)
      (enough_mono hb (by omega))
    obtain ⟨P2,h2,b2⟩ := finalEvenPositive s bs P1 V b b1
    exact ⟨P2,reach_trans h1 h2,b2⟩

#print axioms drainOdd
#print axioms overflowFirst
#print axioms overflowSecond
#print axioms scan_mixed
#print axioms finishZero
#print axioms finishAfterCarry
#print axioms drainEven
end BB6.Agent46Raw13CoupledDrain
