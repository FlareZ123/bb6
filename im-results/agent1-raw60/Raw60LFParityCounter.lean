import Raw60LFUnaryCore
namespace BB6.Agent1Raw60LFParityCounter
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1Raw60LFUnaryCore
set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
abbrev B := Q 1

theorem umerge (a b : Nat) (R : List Bool) : U a++(U b++R)=U (a+b)++R := by
  rw [← List.append_assoc,List.replicate_append_replicate]

theorem pairSweep (k : Nat) (L R : List Bool) :
    run0 table (4*k) (B (false::L) (U (2*k)++R)) = some (B (false::(U (2*k)++L)) R) := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have h1 : run0 table 4 (B (false::L) (U (2*(k+1))++R)) = some (B (false::true::true::L) (U (2*k)++R)) := by rfl
    have h2 := ih (true::true::L)
    have he : U (2*k)++true::true::L = U (2*(k+1))++L := by
      change U (2*k)++(U 2++L)=_
      rw [umerge]
      rfl
    rw [he] at h2
    have H := join0 h1 h2
    rw [show 4+4*k=4*(k+1) by omega] at H
    exact H

inductive Word where
  | stop
  | even (k : Nat) (s : Word)
  | odd (k : Nat) (s : Word)

def enc : Word → List Bool
  | .stop => []
  | .even k s => U (2*k+2)++false::false::enc s
  | .odd k s => U (2*k+3)++false::enc s

def next : Word → Word
  | .stop => .odd 0 .stop
  | .even k s => .odd (k+1) s
  | .odd k s => .even k (next s)

theorem scan (s : Word) (L : List Bool) : ∃ R, Reach table (B (false::L) (enc s)) (F L R) ∧ true::R=enc (next s) := by
  induction s generalizing L with
  | stop => exact ⟨[true,true,false],⟨9,by rfl⟩,rfl⟩
  | even k s ih =>
    have h1 := pairSweep (k+1) L (false::false::enc s)
    have h2 : run0 table 9 (B (false::(U (2*(k+1))++L)) (false::false::enc s)) = some (F (U (2*(k+1))++L) (true::true::false::enc s)) := by rfl
    have h3 := sweep table (by rfl) (2*(k+1)) L (true::true::false::enc s)
    refine ⟨_,⟨_,join0 (join0 h1 h2) h3⟩,?_⟩
    change true::(U (2*(k+1))++(U 2++false::enc s))=U (2*(k+1)+3)++false::enc s
    rw [umerge]
    rfl
  | odd k s ih =>
    have h1 := pairSweep (k+1) L (true::false::enc s)
    have hR : U (2*(k+1))++true::false::enc s = enc (.odd k s) := by
      change U (2*(k+1))++(U 1++false::enc s)=_
      rw [umerge]
      rfl
    rw [hR] at h1
    have h2 : run0 table 2 (B (false::(U (2*(k+1))++L)) (true::false::enc s)) = some (B (false::false::true::(U (2*(k+1))++L)) (enc s)) := by rfl
    obtain ⟨R,h3,he⟩ := ih (false::true::(U (2*(k+1))++L))
    have h4 : run0 table 3 (F (false::true::(U (2*(k+1))++L)) R) = some (F (U (2*k+1)++L) (false::false::true::R)) := by rfl
    have h5 := sweep table (by rfl) (2*k+1) L (false::false::true::R)
    refine ⟨_,reachTrans ⟨_,join0 h1 h2⟩ (reachTrans h3 ⟨_,join0 h4 h5⟩),?_⟩
    rw [he]
    rfl

theorem bFirst (R : List Bool) : step0 table (B [] R)=step0 table (B [false] R) := by rfl

theorem bTransfer (R : List Bool) (t : Nat) (h : 0<t) (c : Z0)
    (hr : run0 table t (B [false] R)=some c) : run0 table t (B [] R)=some c := by
  cases t with
  | zero => omega
  | succ t => simpa only [run0,bFirst] using hr

def cfg (n : Nat) (s : Word) := F [] (U (2*n+5)++false::false::enc s)

theorem advance (n : Nat) (s : Word) : ∃ t, 0<t ∧ run0 table t (cfg n s) = some (cfg (n+1) (next s)) := by
  have h1 : run0 table 1 (cfg n s) = some (B [] (U (2*(n+3))++false::false::enc s)) := by rfl
  have h2 := pairSweep (n+3) [] (false::false::enc s)
  have h2' := bTransfer _ _ (by omega) _ h2
  have h3 : run0 table 9 (B (false::U (2*(n+3))) (false::false::enc s)) = some (F (U (2*(n+3))) (true::true::false::enc s)) := by rfl
  have h4 := sweep table (by rfl) (2*(n+3)) [] (true::true::false::enc s)
  have h5 : run0 table 1 (F [] (U (2*(n+3))++true::true::false::enc s)) = some (B [] (U (2*(n+4))++true::false::enc s)) := by
    have he : U (2*(n+3))++true::true::false::enc s=U (2*(n+4))++false::enc s := by
      change U (2*(n+3))++(U 2++false::enc s)=_
      rw [umerge]
      rfl
    rw [he]
    have he2 : U (2*(n+4))++true::false::enc s = true::(U (2*(n+4))++false::enc s) := by
      change U (2*(n+4))++(U 1++false::enc s) = _
      rw [umerge]
      rfl
    rw [he2]
    rfl
  have h6 := pairSweep (n+4) [] (true::false::enc s)
  have h6' := bTransfer _ _ (by omega) _ h6
  have h7 : run0 table 2 (B (false::U (2*(n+4))) (true::false::enc s)) = some (B (false::false::true::U (2*(n+4))) (enc s)) := by rfl
  obtain ⟨R,h8,he⟩ := scan s (false::true::U (2*(n+4)))
  obtain ⟨a,ha⟩ := h8
  have h9 : run0 table 3 (F (false::true::U (2*(n+4))) R) = some (F (U (2*n+7)) (false::false::true::R)) := by rfl
  have h10 := sweep table (by rfl) (2*n+7) [] (false::false::true::R)
  simp only [List.append_nil] at h2' h4 h6' h10
  have H := join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 h1 h2') h3) h4) h5) h6') h7) ha) h9) h10
  rw [he] at H
  exact ⟨_,by omega,H⟩

def words : Nat → Word
  | 0 => .odd 0 .stop
  | n+1 => next (words n)
def family (n : Nat) := cfg n (words n)
theorem entry : run0 table 65 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth_exists (n : Nat) : ∃ t, 0<t ∧ run0 table t (family n) = some (family (n+1)) := advance n (words n)
noncomputable def cost (n : Nat) : Nat := Classical.choose (growth_exists n)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 65 cost entry (fun n => (Classical.choose_spec (growth_exists n)).1)
    (fun n => (Classical.choose_spec (growth_exists n)).2) m hm
#print axioms never
end BB6.Agent1Raw60LFParityCounter
