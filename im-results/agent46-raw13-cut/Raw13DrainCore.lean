import Raw13CounterBudget
import Raw13CoupledJump
import Raw13TapeValue

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13DrainCore
open BB6.Agent46Raw13RightCounter
open BB6.Agent46Raw13CounterBudget
open BB6.Agent46Raw13CoupledJump (jump blocks_eq scan_eq firstRule secondRule)
open BB6.Agent46Raw13TapeValue (F Reach reach_trans path_reach)

def Steps (x y : BB6.Agent46Raw13TapeValue.NConf) : Prop := x=y ∨ Reach x y

theorem steps_trans {a b c} (h : Steps a b) (g : Steps b c) : Steps a c := by
  rcases h with rfl|h
  · exact g
  rcases g with rfl|g
  · exact Or.inr h
  · exact Or.inr (reach_trans h g)

theorem steps_reach {a b c} (h : Steps a b) (g : Reach b c) : Reach a c := by
  rcases h with rfl|h
  · exact g
  · exact reach_trans h g

theorem reach_steps {a b c} (h : Reach a b) (g : Steps b c) : Reach a c := by
  rcases g with rfl|g
  · exact h
  · exact reach_trans h g

theorem jumpBudget (m x d : Nat) (L P V : List Bool) (b : Nat)
    (hx : x+2*d < 2^m) (hb : enough P (b+d)) :
    ∃ P', Steps (F (encode m x++L) (P++V)) (F (encode m (x+2*d)++L) (P'++V)) ∧ enough P' b := by
  cases d with
  | zero => exact ⟨P,Or.inl (by simp),by simpa using hb⟩
  | succ d =>
    obtain ⟨ts,us,R,hp,ha,he⟩ := spend P (b+(d+1)) (d+1) hb (by omega)
    have hr := path_reach (jump m x (d+1) L (R++V) ts us (by omega) hx ha)
    change Reach (F _ (word ts (R++V))) (F _ (word us (R++V))) at hr
    rw [word_append,word_append,hp] at hr
    exact ⟨word us R,Or.inr hr,by simpa using he⟩

theorem mainFirst (n : Nat) (L P V : List Bool) (b : Nat) (hb : enough P (b+1)) :
    ∃ j T P', Reach (F (oneBlocks n++false::L) (P++V))
      (F (ones (6*(j+1))++zeros (4*n)++true::L) (T++V)) ∧
      P'=zeros (3*j+2)++true::T ∧ enough P' b := by
  obtain ⟨j,T,P',hs,he,hb'⟩ := scan_spend P V b hb
  have h := path_reach (firstRule n L (P++V))
  change Reach (F _ _) (F (ones (scan (true::(P++V))).1++zeros (4*n)++true::L)
    (scan (true::(P++V))).2) at h
  rw [hs] at h
  exact ⟨j,T,P',h,he,hb'⟩

theorem mainPos (k n : Nat) (L W : List Bool) :
    Reach (F (ones (2*(k+1))++oneBlocks n++false::L) W)
      (F (zeros (4*n)++true::L) (zeros k++true::W)) := path_reach (secondRule k n L W)

theorem firstCarry (m x : Nat) (L P V : List Bool) (b : Nat)
    (hx : x+1<2^m) (hb : enough P (b+1)) :
    ∃ j T P', Reach (F (encode m x++L) (P++V))
      (F (ones (6*(j+1))++(encode m (x+1)++L)) (T++V)) ∧
      P'=zeros (3*j+2)++true::T ∧ enough P' b := by
  obtain ⟨n,X,h1,h2⟩ := left_carry m x L hx
  obtain ⟨j,T,P',hr,he,hb'⟩ := mainFirst n X P V b hb
  rw [← h1,List.append_assoc,← h2] at hr
  exact ⟨j,T,P',hr,he,hb'⟩

theorem positiveCarry (h m x : Nat) (L W : List Bool) (hh : 0<h) (hx : x+1<2^m) :
    Reach (F (ones (6*h)++(encode m x++L)) W)
      (F (encode m (x+1)++L) (zeros (3*h-1)++true::W)) := by
  obtain ⟨n,X,h1,h2⟩ := left_carry m x L hx
  have hr := mainPos (3*h-1) n X W
  rw [List.append_assoc,← h1,← h2,show 2*(3*h-1+1)=6*h by omega] at hr
  exact hr

theorem specialStep (k n : Nat) (L W : List Bool) :
    Reach (F (ones (2*k)++oneBlocks (n+1)++true::false::false::true::L) W)
      (F (ones (scan (ones (2*n+1)++zeros (k+2)++true::W)).1++true::true::L)
        (scan (ones (2*n+1)++zeros (k+2)++true::W)).2) := by
  rw [blocks_eq,scan_eq]
  exact path_reach (BB6.Agent46Raw13Frames.special k n L W)

theorem special0Step (k : Nat) (L W : List Bool) :
    Reach (F (ones (2*k)++true::false::false::true::L) W)
      (F (true::true::L) (zeros k++true::W)) := path_reach (BB6.Agent46Raw13Frames.special0 k L W)

theorem mixedStep (k n : Nat) (L W : List Bool) :
    Reach (F (ones (2*k)++oneBlocks (n+1)++true::true::false::L) W)
      (F (ones (scan (ones (2*n+1)++zeros (k+2)++true::W)).1++true::L)
        (scan (ones (2*n+1)++zeros (k+2)++true::W)).2) := by
  rw [blocks_eq,scan_eq]
  exact path_reach (BB6.Agent46Raw13Frames.mixed11 k n L W)

theorem encode_zero (m : Nat) : encode m 0 = zeros (4*m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [encode_even _ _ rfl]
    simp only [Nat.zero_div,ih]
    rw [show 4*(m+1)=4+4*m by omega,zeros_add 4 (4*m)]
    rfl

theorem encode_one (m : Nat) : encode (m+1) 1 = true::false::false::false::zeros (4*m) := by
  rw [encode_odd _ _ rfl]
  exact congrArg (fun X => true::false::false::false::X) (encode_zero m)

theorem encode_max (m : Nat) : encode m (2^m-1) = oneBlocks m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hp : 0<2^m := Nat.two_pow_pos m
    rw [Nat.pow_succ,encode_odd _ _ (by omega)]
    rw [show (2^m*2-1)/2=2^m-1 by omega,ih]
    rfl

def encBits : List Bool → List Bool
  | [] => []
  | b::bs => b::false::false::false::encBits bs

theorem encBits_zeros (s : Nat) (bs : List Bool) :
    encBits (zeros s++bs) = zeros (4*s)++encBits bs := by
  induction s with
  | zero => rfl
  | succ s ih =>
    simp only [zeros,List.replicate_succ,List.cons_append,encBits]
    change false::false::false::false::encBits (zeros s++bs) = zeros (4*(s+1))++encBits bs
    rw [ih,show 4*(s+1)=4+4*s by omega,zeros_add 4 (4*s),List.append_assoc]
    rfl

def D (h : Nat) (bs W : List Bool) := F (ones (6*h)++[true,false,false]++encBits bs) W

def U0 (bs : List Bool) := [false,false,false,true,false,false,false]++encBits bs
def U1 (bs : List Bool) := [true,false,false,true,false,false,false]++encBits bs

theorem D_even (h s : Nat) (bs W : List Bool) (hs : 0<s) :
    D h (zeros s++true::bs) W = F (ones (6*h)++(encode s 1++U0 bs)) W := by
  cases s with
  | zero => omega
  | succ s =>
    unfold D U0
    rw [encBits_zeros,encode_one]
    simp only [encBits,List.append_assoc,List.cons_append,List.nil_append]
    have he : zeros (4*(s+1)) = zeros (4*s)++zeros 4 := by
      rw [show 4*(s+1)=4*s+4 by omega,zeros_add]
    rw [he]
    have hz : zeros (4*s)++zeros 4 = zeros 1++zeros (4*s)++zeros 3 := by
      rw [← zeros_add,← zeros_add,← zeros_add]
      congr 1 <;> omega
    have eq : zeros (4*s)++(zeros 4++true::false::false::false::encBits bs) =
        false::(zeros (4*s)++false::false::false::true::false::false::false::encBits bs) := by
      rw [← List.append_assoc,hz]
      simp only [List.append_assoc]
      rfl
    simp only [List.append_assoc]
    rw [eq]

#print axioms jumpBudget
#print axioms positiveCarry
end BB6.Agent46Raw13DrainCore
