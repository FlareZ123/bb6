import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.CarryCore
open BB6Coverage BB6Coverage.Agent31Pump

def U (n : Nat) := rep [true] n
def Z (n : Nat) := rep [false] n
def z (e : Nat) := Z (e+1)
def o (e : Nat) := Z e ++ [true]
def input (e : Nat) := true :: Z e

def cfg (a : Nat) (S R : List Bool) : Z0 := ⟨2,U a++S,[true,true]++R⟩
def scanning (a : Nat) (S R : List Bool) : Z0 := ⟨2,false::(U a++S),R⟩
def large (a e k : Nat) (S : List Bool) : Z0 := cfg (a+(e+1)*(k+1)) S []

structure Core (p : PartialMachine) (a e t r u v : Nat) (S : List Bool) : Prop where
  prep : ∀ R, run0 p t (cfg a S R) = some (scanning a S (true::R))
  scan : ∀ L R, run0 p r ⟨2,false::L,input e++R⟩ = some ⟨2,false::(U (e+1)++L),R⟩
  scanEnd : ∀ L, run0 p r ⟨2,false::L,[true]⟩ = some ⟨2,false::(U (e+1)++L),[]⟩
  turn : ∀ L R, run0 p u ⟨2,false::(U (e+1)++L),false::R⟩ = some ⟨2,U (e+1)++L,[true,true]++R⟩
  turnEnd : ∀ L, run0 p u ⟨2,false::(U (e+1)++L),[]⟩ = some ⟨2,U (e+1)++L,[true,true]⟩
  resetStart : ∀ L R, run0 p 1 ⟨2,true::L,[true,true]++R⟩ = some ⟨4,true::true::L,true::R⟩
  left : ∀ L R, run0 p 1 ⟨4,true::L,R⟩ = some ⟨4,L,false::R⟩
  resetTail : ∀ R, run0 p v ⟨4,S,Z (a+2)++R⟩ = some (cfg a S R)

private theorem repAdd (P : List Bool) (a b : Nat) : rep P (a+b) = rep P a ++ rep P b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [show a+1+b=(a+b)+1 by omega,rep,ih,rep,List.append_assoc]
private theorem repMul (P : List Bool) (d k : Nat) : rep (rep P d) k = rep P (d*k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [rep,ih,Nat.mul_succ,Nat.add_comm (d*k) d,repAdd]
private theorem rotate (e k : Nat) : true::rep (o e) k = rep (input e) k ++ [true] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rep,o,input,List.cons_append,List.append_assoc]
    have H : true::rep (Z e++[true]) k = rep (true::Z e) k ++ [true] := ih
    rw [← H]
    rfl

theorem scanAll (p : PartialMachine) (a e t r u v : Nat) (S : List Bool) (h : Core p a e t r u v S) (k : Nat) (R : List Bool) :
    run0 p (t+r*k) (cfg a S (rep (o e) k++R)) = some (scanning (a+(e+1)*k) S (true::R)) := by
  have h1 := h.prep (rep (o e) k++R)
  have h2 := sweepR p 2 [false] [] (input e) (U (e+1)) r (by simpa using h.scan) k (U a++S) (true::R)
  simp only [List.nil_append,List.singleton_append] at h2
  rw [show true::(rep (o e) k++R) = rep (input e) k++true::R by rw [← List.cons_append,rotate,List.append_assoc]; rfl] at h1
  have H := join0 h1 h2
  have hl : rep (U (e+1)) k ++ (U a ++ S) = U (a+(e+1)*k) ++ S := by
    simp only [U,repMul]; rw [← List.append_assoc,← repAdd,Nat.add_comm ((e+1)*k) a]
  simpa only [scanning,List.cons_append,hl] using H

def scanCost (t r u k : Nat) := t+r*k+r+u

theorem scanZero (p : PartialMachine) (a e t r u v : Nat) (S : List Bool) (h : Core p a e t r u v S) (k : Nat) (R : List Bool) :
    run0 p (scanCost t r u k) (cfg a S (rep (o e) k++z e++R)) = some (cfg (a+(e+1)*(k+1)) S R) := by
  have h1 := scanAll p a e t r u v S h k (z e++R)
  have h2 := h.scan (U (a+(e+1)*k)++S) (false::R)
  have h3 := h.turn (U (a+(e+1)*k)++S) R
  have h1' : run0 p (t+r*k) (cfg a S (rep (o e) k++z e++R)) =
      some ⟨2,false::(U (a+(e+1)*k)++S),input e++false::R⟩ := by
    simp only [List.append_assoc] at h1 ⊢
    have hz : z e = Z e ++ [false] := by
      unfold z Z; rw [rep_snoc]; rfl
    rw [hz] at h1 ⊢
    simpa only [scanning,input,List.cons_append,List.append_assoc,List.singleton_append,List.nil_append] using h1
  have H := join0 (join0 h1' h2) h3
  change _ = some (cfg (a+(e+1)*(k+1)) S R)
  have hl : U (e+1)++(U (a+(e+1)*k)++S) = U (a+(e+1)*(k+1))++S := by
    change rep [true] (e+1) ++ (rep [true] (a+(e+1)*k)++S) = rep [true] (a+(e+1)*(k+1))++S
    simp only [← List.append_assoc,← repAdd]
    rw [show e+1+(a+(e+1)*k)=a+(e+1)*(k+1) by rw [Nat.mul_succ]; omega]
  rw [hl] at H
  exact H

theorem scanOverflow (p : PartialMachine) (a e t r u v : Nat) (S : List Bool) (h : Core p a e t r u v S) (k : Nat) :
    run0 p (scanCost t r u k) (cfg a S (rep (o e) k)) = some (large a e k S) := by
  have h1 := scanAll p a e t r u v S h k []
  have h2 := h.scanEnd (U (a+(e+1)*k)++S)
  have h3 := h.turnEnd (U (a+(e+1)*k)++S)
  simp only [List.append_nil] at h1
  have H := join0 (join0 h1 h2) h3
  have hl : U (e+1)++(U (a+(e+1)*k)++S) = U (a+(e+1)*(k+1))++S := by
    change rep [true] (e+1) ++ (rep [true] (a+(e+1)*k)++S) = rep [true] (a+(e+1)*(k+1))++S
    simp only [← List.append_assoc,← repAdd]
    rw [show e+1+(a+(e+1)*k)=a+(e+1)*(k+1) by rw [Nat.mul_succ]; omega]
  rw [hl] at H
  exact H

def resetCost (a e v k : Nat) := 1+(a+(e+1)*(k+1)+1)+v

theorem reset (p : PartialMachine) (a e t r u v : Nat) (S : List Bool) (h : Core p a e t r u v S) (k : Nat) (R : List Bool) :
    run0 p (resetCost a e v k) (cfg (a+(e+1)*(k+1)) S R) = some (cfg a S (rep (z e) k++o e++R)) := by
  let n := a+(e+1)*(k+1)
  have hn : n = 1+(a+(e+1)*k+e) := by dsimp [n]; rw [Nat.mul_succ]; omega
  have h1 : run0 p 1 (cfg n S R) = some ⟨4,U (n+1)++S,true::R⟩ := by
    rw [hn,show 1+(a+(e+1)*k+e)+1=2+(a+(e+1)*k+e) by omega]
    simpa only [cfg,U,repAdd,show rep [true] 1=[true] by rfl,show rep [true] 2=[true,true] by rfl,List.append_assoc,List.cons_append,List.nil_append] using h.resetStart (U (a+(e+1)*k+e)++S) R
  have h2 := sweepL p 4 [] [] [true] [false] 1 (by simpa using h.left) (n+1) S (true::R)
  simp only [List.nil_append,Nat.one_mul] at h2
  have h3 := h.resetTail (rep (z e) k++o e++R)
  have hr : Z (n+1)++true::R = Z (a+2)++(rep (z e) k++o e++R) := by
    simp only [z,o,Z,repMul,← List.append_assoc,← repAdd]
    rw [show n+1=a+2+((e+1)*k+e) by omega,List.append_assoc]
    rfl
  rw [show rep [false] (n+1)++true::R=Z (n+1)++true::R by rfl,hr] at h2
  exact join0 (join0 h1 h2) h3

def carryCost (a e t r u v k : Nat) := scanCost t r u k+resetCost a e v k

theorem carry (p : PartialMachine) (a e t r u v : Nat) (S : List Bool) (h : Core p a e t r u v S) (k : Nat) (R : List Bool) :
    run0 p (carryCost a e t r u v k) (cfg a S (rep (o e) k++z e++R)) = some (cfg a S (rep (z e) k++o e++R)) :=
  join0 (scanZero p a e t r u v S h k R) (reset p a e t r u v S h k R)

def fillCost (a e t r u v : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => fillCost a e t r u v k+carryCost a e t r u v k+fillCost a e t r u v k

theorem fill (p : PartialMachine) (a e t r u v : Nat) (S : List Bool) (h : Core p a e t r u v S) (k : Nat) (R : List Bool) :
    run0 p (fillCost a e t r u v k) (cfg a S (rep (z e) k++R)) = some (cfg a S (rep (o e) k++R)) := by
  induction k generalizing R with
  | zero => simp [fillCost,rep,run0]
  | succ k ih =>
    have h1 := ih (z e++R)
    have h2 := carry p a e t r u v S h k R
    have h3 := ih (o e++R)
    simp only [List.append_assoc] at h1 h2 h3
    have H := join0 (join0 h1 h2) h3
    rw [fillCost,show rep (z e) (k+1)=rep (z e) k++z e by rw [rep_snoc]; rfl,show rep (o e) (k+1)=rep (o e) k++o e by rw [rep_snoc]; rfl]
    simpa only [List.append_assoc] using H

def outerCost (a e t r u v k : Nat) := resetCost a e v k+fillCost a e t r u v k+scanCost t r u (k+1)

theorem grow (p : PartialMachine) (a e t r u v : Nat) (S : List Bool) (h : Core p a e t r u v S) (k : Nat) :
    run0 p (outerCost a e t r u v k) (large a e k S) = some (large a e (k+1) S) := by
  have h1 := reset p a e t r u v S h k []
  have h2 := fill p a e t r u v S h k (o e)
  have h3 := scanOverflow p a e t r u v S h (k+1)
  simp only [List.append_nil] at h1
  rw [rep_snoc (o e) k,← show rep (o e) (k+1)=o e++rep (o e) k by rfl] at h2
  exact join0 (join0 h1 h2) h3

theorem never (p : PartialMachine) (a e t r u v : Nat) (S : List Bool) (h : Core p a e t r u v S) (entry : Nat)
    (first : run0 p entry ⟨0,[],[]⟩ = some (large a e 0 S)) (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p (large a e · S) entry (outerCost a e t r u v) first _ (grow p a e t r u v S h) m hm
  intro k; unfold outerCost resetCost; omega
#print axioms never
end BB6.Agent19Raw40.CarryCore
