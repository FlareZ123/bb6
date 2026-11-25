import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw60LBQuadratic
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,true,5⟩)
  | _,_ => none

def o (n : Nat) := rep [true] n
def B (L R : List Bool) : Z0 := ⟨1,L,R⟩
def F (L R : List Bool) : Z0 := ⟨5,L,R⟩
def Reach (c d : Z0) : Prop := ∃ t, run0 table t c = some d

theorem trans {a b c : Z0} (h : Reach a b) (g : Reach b c) : Reach a c := by
  obtain ⟨i,hi⟩ := h
  obtain ⟨j,hj⟩ := g
  exact ⟨i+j,join0 hi hj⟩

theorem o_add (a b : Nat) : o (a+b) = o a ++ o b := by
  induction a with
  | zero => simp [o,rep]
  | succ a ih =>
    rw [show a+1+b=(a+b)+1 by omega]
    change true::o (a+b) = true::(o a ++ o b)
    rw [ih]

theorem b_sweep (n : Nat) (L R : List Bool) : run0 table n (B (o n++L) R) = some (B L (o n++R)) := by
  simpa [B,o] using sweepL table 1 [] [] [true] [true] 1 (by intro l r; rfl) n L R

theorem f_sweep (n : Nat) (L R : List Bool) : run0 table n (F (true::L) (o n++R)) = some (F (true::(o n++L)) R) := by
  simpa [F,o,List.append_assoc] using sweepR table 5 [true] [] [true] [true] 1 (by intro l r; rfl) n L R

theorem transfer (m : Nat) (L R : List Bool) :
    Reach (F (false::(o (m+2)++false::L)) R) (F (false::(o m++false::true::L)) (true::R)) := by
  have h1 : run0 table 2 (F (false::(o (m+2)++false::L)) R) = some (B (o (m+1)++false::L) (false::true::R)) := by rfl
  have h2 := b_sweep (m+1) (false::L) (false::true::R)
  have h3 : run0 table 1 (B (false::L) (o (m+1)++false::true::R)) = some (⟨2,true::true::L,o m++false::true::R⟩ : Z0) := by rfl
  have h4 : Reach (⟨2,true::true::L,o m++false::true::R⟩ : Z0) (F (false::(o m++false::true::L)) (true::R)) := by
    cases m with
    | zero => exact ⟨1,rfl⟩
    | succ k =>
      have hc : run0 table 1 (⟨2,true::true::L,o (k+1)++false::true::R⟩ : Z0) = some (F (true::false::true::L) (o k++false::true::R)) := by rfl
      have hs := f_sweep k (false::true::L) (false::true::R)
      have he : run0 table 1 (F (true::(o k++false::true::L)) (false::true::R)) = some (F (false::(o (k+1)++false::true::L)) (true::R)) := by rfl
      exact trans ⟨1,hc⟩ (trans ⟨k,hs⟩ ⟨1,he⟩)
  exact trans ⟨2,h1⟩ (trans ⟨m+1,h2⟩ (trans ⟨1,h3⟩ h4))

theorem drain (n : Nat) (L R : List Bool) :
    Reach (F (false::(o (2*n)++false::L)) R) (B (o (n+2)++L) (o n++R)) := by
  induction n generalizing L R with
  | zero => exact ⟨2,rfl⟩
  | succ n ih =>
    have h := transfer (2*n) L R
    have h' := ih (true::L) (true::R)
    rw [show 2*(n+1)=2*n+2 by omega]
    have H := trans h h'
    rw [show n+1+2=n+3 by omega]
    rw [show n+3=(n+2)+1 by omega,o_add (n+2) 1,show n+1=n+1 by rfl,o_add n 1]
    simpa only [show o 1=[true] by rfl,List.append_assoc,List.singleton_append] using H

theorem begin (n : Nat) : Reach (B [] (o (2*n+3))) (F (false::(o (2*n+2)++[false,true])) []) := by
  have h1 : run0 table 2 (B [] (o (2*n+3))) = some (F [true,false,true] (o (2*n+1))) := by
    rw [show 2*n+3=(2*n+1)+1+1 by omega]; rfl
  have h2 := f_sweep (2*n+1) [false,true] []
  have h3 : run0 table 1 (F (true::(o (2*n+1)++[false,true])) []) = some (F (false::(o (2*n+2)++[false,true])) []) := by rfl
  exact trans ⟨2,h1⟩ (trans ⟨2*n+1,by simpa only [List.append_nil] using h2⟩ ⟨1,h3⟩)

theorem grow (n : Nat) : Reach (B [] (o (2*n+3))) (B [] (o (2*n+5))) := by
  have h1 := begin n
  have h2 := drain (n+1) [true] []
  have h2' : Reach (F (false::(o (2*n+2)++[false,true])) []) (B (o (n+4)) (o (n+1))) := by
    rw [show 2*n+2=2*(n+1) by omega,show n+4=(n+1+2)+1 by omega,o_add]
    simpa only [List.append_nil,show o 1=[true] by rfl] using h2
  have h3 := b_sweep (n+4) [] (o (n+1))
  rw [List.append_nil,← o_add,show n+4+(n+1)=2*n+5 by omega] at h3
  exact trans h1 (trans h2' ⟨n+4,h3⟩)

def family (n : Nat) := B [] (o (2*n+5))
noncomputable def cost (n : Nat) : Nat := Classical.choose (grow (n+1))
theorem entry : run0 table 26 ⟨0,[],[]⟩ = some (family 0) := rfl
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h := Classical.choose_spec (grow (n+1))
  simpa only [family,cost,show 2*(n+1)+3=2*n+5 by omega,show 2*(n+1)+5=2*(n+1)+5 by rfl] using h

theorem olen (n : Nat) : (o n).length = n := by induction n with
  | zero => rfl
  | succ n ih =>
    change (true::o n).length = n+1
    rw [List.length_cons,ih]

theorem positive (n : Nat) : 0 < cost n := by
  by_cases h : cost n = 0
  · have H := growth n
    rw [h,run0] at H
    have E := congrArg (fun c : Z0 => c.r.length) (Option.some.inj H)
    simp [family,B,olen] at E
    omega
  · omega

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 26 cost entry positive growth m hm
#print axioms never
end BB6.Agent1Raw60LBQuadratic
