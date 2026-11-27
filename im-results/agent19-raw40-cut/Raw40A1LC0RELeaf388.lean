import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.A1LC0RE.Leaf388
open BB6Coverage BB6Coverage.Agent31Pump
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem inner0m0 (R : List Bool) : run0 table 7 ⟨0, [true,true,false,false,false] ++ R, []⟩ = some ⟨3, R, [true,true,true,true,false]⟩ := by rfl
theorem inner0m1 (L R : List Bool) : run0 table 2 ⟨3, [false,false] ++ L, [true,true,true,true] ++ R⟩ = some ⟨3, L, [true,true,true,true] ++ [true,true] ++ R⟩ := by rfl
theorem inner0m2 (Z : List Bool) (R : List Bool) : run0 table 6 ⟨3, [true,false] ++ Z, [true,true,true,true] ++ R⟩ = some ⟨1, [true,false,false,false,false,true] ++ Z, R⟩ := by rfl
theorem inner0m3 (L R : List Bool) : run0 table 2 ⟨1, [true] ++ L, [true,true] ++ R⟩ = some ⟨1, [true] ++ [false,false] ++ L, R⟩ := by rfl
theorem inner0m4 (R : List Bool) : run0 table 8 ⟨1, [true] ++ R, [false]⟩ = some ⟨0, [true,true,false] ++ R, [true,true,true]⟩ := by rfl
theorem inner0 (n : Nat) (Z : List Bool) : run0 table (21+4*n) ⟨0, [true,true,false,false,false] ++ rep [false,false] n ++ [true,false] ++ Z, []⟩ = some ⟨0, [true,true,false] ++ rep [false,false] n ++ [false,false,false,false,true] ++ Z, [true,true,true]⟩ := by
  have h0 := inner0m0 (rep [false,false] n ++ [true,false] ++ Z)
  have h1 := sweepL table 3 [] [true,true,true,true] [false,false] [true,true] 2 inner0m1 n ([true,false] ++ Z) ([false])
  have h2 := inner0m2 Z (rep [true,true] n ++ [false])
  have h3 := sweepR table 1 [true] [] [true,true] [false,false] 2 inner0m3 n ([false,false,false,false,true] ++ Z) ([false])
  have h4 := inner0m4 (rep [false,false] n ++ [false,false,false,false,true] ++ Z)
  try simp only [List.append_assoc,List.nil_append,List.append_nil] at h0 h1 h2 h3 h4
  have H := (join0 (join0 (join0 (join0 h0 h1) h2) h3) h4)
  simpa only [List.append_assoc,show 7+2*n+6+2*n+8 = 21+4*n by omega] using H
theorem inner1m0 (R : List Bool) : run0 table 7 ⟨0, [true,true,false,false,false] ++ R, [true]⟩ = some ⟨3, R, [true,true,true,true,false,true]⟩ := by rfl
theorem inner1m1 (L R : List Bool) : run0 table 2 ⟨3, [false,false] ++ L, [true,true,true,true] ++ R⟩ = some ⟨3, L, [true,true,true,true] ++ [true,true] ++ R⟩ := by rfl
theorem inner1m2 (Z : List Bool) (R : List Bool) : run0 table 6 ⟨3, [true,false] ++ Z, [true,true,true,true] ++ R⟩ = some ⟨1, [true,false,false,false,false,true] ++ Z, R⟩ := by rfl
theorem inner1m3 (L R : List Bool) : run0 table 2 ⟨1, [true] ++ L, [true,true] ++ R⟩ = some ⟨1, [true] ++ [false,false] ++ L, R⟩ := by rfl
theorem inner1m4 (R : List Bool) : run0 table 2 ⟨1, [true] ++ R, [false,true]⟩ = some ⟨0, [true,true,false] ++ R, []⟩ := by rfl
theorem inner1 (n : Nat) (Z : List Bool) : run0 table (15+4*n) ⟨0, [true,true,false,false,false] ++ rep [false,false] n ++ [true,false] ++ Z, [true]⟩ = some ⟨0, [true,true,false] ++ rep [false,false] n ++ [false,false,false,false,true] ++ Z, []⟩ := by
  have h0 := inner1m0 (rep [false,false] n ++ [true,false] ++ Z)
  have h1 := sweepL table 3 [] [true,true,true,true] [false,false] [true,true] 2 inner1m1 n ([true,false] ++ Z) ([false,true])
  have h2 := inner1m2 Z (rep [true,true] n ++ [false,true])
  have h3 := sweepR table 1 [true] [] [true,true] [false,false] 2 inner1m3 n ([false,false,false,false,true] ++ Z) ([false,true])
  have h4 := inner1m4 (rep [false,false] n ++ [false,false,false,false,true] ++ Z)
  try simp only [List.append_assoc,List.nil_append,List.append_nil] at h0 h1 h2 h3 h4
  have H := (join0 (join0 (join0 (join0 h0 h1) h2) h3) h4)
  simpa only [List.append_assoc,show 7+2*n+6+2*n+2 = 15+4*n by omega] using H
theorem inner2m0 (R : List Bool) : run0 table 7 ⟨0, [true,true,false,false,false] ++ R, [true,true]⟩ = some ⟨3, R, [true,true,true,true,false,true,true]⟩ := by rfl
theorem inner2m1 (L R : List Bool) : run0 table 2 ⟨3, [false,false] ++ L, [true,true,true,true] ++ R⟩ = some ⟨3, L, [true,true,true,true] ++ [true,true] ++ R⟩ := by rfl
theorem inner2m2 (Z : List Bool) (R : List Bool) : run0 table 6 ⟨3, [true,false] ++ Z, [true,true,true,true] ++ R⟩ = some ⟨1, [true,false,false,false,false,true] ++ Z, R⟩ := by rfl
theorem inner2m3 (L R : List Bool) : run0 table 2 ⟨1, [true] ++ L, [true,true] ++ R⟩ = some ⟨1, [true] ++ [false,false] ++ L, R⟩ := by rfl
theorem inner2m4 (R : List Bool) : run0 table 2 ⟨1, [true] ++ R, [false,true,true]⟩ = some ⟨0, [true,true,false] ++ R, [true]⟩ := by rfl
theorem inner2 (n : Nat) (Z : List Bool) : run0 table (15+4*n) ⟨0, [true,true,false,false,false] ++ rep [false,false] n ++ [true,false] ++ Z, [true,true]⟩ = some ⟨0, [true,true,false] ++ rep [false,false] n ++ [false,false,false,false,true] ++ Z, [true]⟩ := by
  have h0 := inner2m0 (rep [false,false] n ++ [true,false] ++ Z)
  have h1 := sweepL table 3 [] [true,true,true,true] [false,false] [true,true] 2 inner2m1 n ([true,false] ++ Z) ([false,true,true])
  have h2 := inner2m2 Z (rep [true,true] n ++ [false,true,true])
  have h3 := sweepR table 1 [true] [] [true,true] [false,false] 2 inner2m3 n ([false,false,false,false,true] ++ Z) ([false,true,true])
  have h4 := inner2m4 (rep [false,false] n ++ [false,false,false,false,true] ++ Z)
  try simp only [List.append_assoc,List.nil_append,List.append_nil] at h0 h1 h2 h3 h4
  have H := (join0 (join0 (join0 (join0 h0 h1) h2) h3) h4)
  simpa only [List.append_assoc,show 7+2*n+6+2*n+2 = 15+4*n by omega] using H
theorem inner3m0 (R : List Bool) : run0 table 7 ⟨0, [true,true,false,false,false] ++ R, [true,true,true]⟩ = some ⟨3, R, [true,true,true,true,false,true,true,true]⟩ := by rfl
theorem inner3m1 (L R : List Bool) : run0 table 2 ⟨3, [false,false] ++ L, [true,true,true,true] ++ R⟩ = some ⟨3, L, [true,true,true,true] ++ [true,true] ++ R⟩ := by rfl
theorem inner3m2 (Z : List Bool) (R : List Bool) : run0 table 6 ⟨3, [true,false] ++ Z, [true,true,true,true] ++ R⟩ = some ⟨1, [true,false,false,false,false,true] ++ Z, R⟩ := by rfl
theorem inner3m3 (L R : List Bool) : run0 table 2 ⟨1, [true] ++ L, [true,true] ++ R⟩ = some ⟨1, [true] ++ [false,false] ++ L, R⟩ := by rfl
theorem inner3m4 (R : List Bool) : run0 table 2 ⟨1, [true] ++ R, [false,true,true,true]⟩ = some ⟨0, [true,true,false] ++ R, [true,true]⟩ := by rfl
theorem inner3 (n : Nat) (Z : List Bool) : run0 table (15+4*n) ⟨0, [true,true,false,false,false] ++ rep [false,false] n ++ [true,false] ++ Z, [true,true,true]⟩ = some ⟨0, [true,true,false] ++ rep [false,false] n ++ [false,false,false,false,true] ++ Z, [true,true]⟩ := by
  have h0 := inner3m0 (rep [false,false] n ++ [true,false] ++ Z)
  have h1 := sweepL table 3 [] [true,true,true,true] [false,false] [true,true] 2 inner3m1 n ([true,false] ++ Z) ([false,true,true,true])
  have h2 := inner3m2 Z (rep [true,true] n ++ [false,true,true,true])
  have h3 := sweepR table 1 [true] [] [true,true] [false,false] 2 inner3m3 n ([false,false,false,false,true] ++ Z) ([false,true,true,true])
  have h4 := inner3m4 (rep [false,false] n ++ [false,false,false,false,true] ++ Z)
  try simp only [List.append_assoc,List.nil_append,List.append_nil] at h0 h1 h2 h3 h4
  have H := (join0 (join0 (join0 (join0 h0 h1) h2) h3) h4)
  simpa only [List.append_assoc,show 7+2*n+6+2*n+2 = 15+4*n by omega] using H
theorem finishm0 (R : List Bool) : run0 table 7 ⟨0, [true,true,false,false,false] ++ R, []⟩ = some ⟨3, R, [true,true,true,true,false]⟩ := by rfl
theorem finishm1 (L R : List Bool) : run0 table 2 ⟨3, [false,false] ++ L, R⟩ = some ⟨3, L, [true,true] ++ R⟩ := by rfl
theorem finishm2 (R : List Bool) : run0 table 1 ⟨3, [true,true], R⟩ = some ⟨0, [true], [true] ++ R⟩ := by rfl
theorem finish (n : Nat) : run0 table (8+2*n) ⟨0, [true,true,false,false,false] ++ rep [false,false] n ++ [true,true], []⟩ = some ⟨0, [true], [true] ++ rep [true,true] n ++ [true,true,true,true,false]⟩ := by
  have h0 := finishm0 (rep [false,false] n ++ [true,true])
  have h1 := sweepL table 3 [] [] [false,false] [true,true] 2 finishm1 n ([true,true]) ([true,true,true,true,false])
  have h2 := finishm2 (rep [true,true] n ++ [true,true,true,true,false])
  try simp only [List.append_assoc,List.nil_append,List.append_nil] at h0 h1 h2
  have H := (join0 (join0 h0 h1) h2)
  simpa only [List.append_assoc,show 7+2*n+1 = 8+2*n by omega] using H
theorem beginm0 (R : List Bool) : run0 table 4 ⟨0, [false], [true,true,true,true] ++ R⟩ = some ⟨4, [true,false,false,false,true], R⟩ := by rfl
theorem beginm1 (L R : List Bool) : run0 table 4 ⟨4, [true] ++ L, [true,true,true,true] ++ R⟩ = some ⟨4, [true] ++ [false,false,false,false] ++ L, R⟩ := by rfl
theorem beginm2 (R : List Bool) : run0 table 17 ⟨4, [true] ++ R, [false]⟩ = some ⟨0, [true,true,false,false,false,true] ++ R, [true,true,true]⟩ := by rfl
theorem begin (n : Nat) : run0 table (21+4*n) ⟨0, [false], [true,true,true,true] ++ rep [true,true,true,true] n ++ [false]⟩ = some ⟨0, [true,true,false,false,false,true] ++ rep [false,false,false,false] n ++ [false,false,false,true], [true,true,true]⟩ := by
  have h0 := beginm0 (rep [true,true,true,true] n ++ [false])
  have h1 := sweepR table 4 [true] [] [true,true,true,true] [false,false,false,false] 4 beginm1 n ([false,false,false,true]) ([false])
  have h2 := beginm2 (rep [false,false,false,false] n ++ [false,false,false,true])
  try simp only [List.append_assoc,List.nil_append,List.append_nil] at h0 h1 h2
  have H := (join0 (join0 h0 h1) h2)
  simpa only [List.append_assoc,show 4+4*n+17 = 21+4*n by omega] using H
theorem resetm0 (R : List Bool) : run0 table 3 ⟨0, [true], R⟩ = some ⟨0, [false], [true] ++ R⟩ := by rfl

abbrev V (b : Bool) (n : Nat) := List.replicate n b
theorem vAdd (b : Bool) (a c : Nat) : V b (a+c) = V b a ++ V b c := List.replicate_append_replicate.symm
theorem repV (b : Bool) (k n : Nat) : rep (V b k) n = V b (k*n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep,ih,show k*(n+1)=k+k*n by rw [Nat.mul_succ,Nat.add_comm],vAdd]

def C (n b : Nat) : Z0 := ⟨0,[true,true] ++ V false (2*n+3) ++ [true] ++ V false b ++ [true],V true (b%4)⟩
def outer (k : Nat) : Z0 := ⟨0,[false],V true (4*k+4) ++ [false]⟩

theorem innerInput (n b : Nat) : [true,true,false,false,false] ++ rep [false,false] n ++ [true,false] ++ (V false b ++ [true]) = (C n (b+1)).l := by
  simp only [List.append_assoc,C]
  change [true,true] ++ (V false 3 ++ (rep (V false 2) n ++ ([true] ++ (V false 1 ++ (V false b ++ [true]))))) = _
  rw [repV,←List.append_assoc (V false 1) (V false b),←vAdd,←List.append_assoc (V false 3) (V false (2*n)),←vAdd]
  rw [show 3+2*n=2*n+3 by omega,show 1+b=b+1 by omega]

theorem innerOutput (n b : Nat) : [true,true,false] ++ rep [false,false] n ++ [false,false,false,false,true] ++ (V false b ++ [true]) = (C (n+1) b).l := by
  simp only [List.append_assoc,C]
  change [true,true] ++ (V false 1 ++ (rep (V false 2) n ++ (V false 4 ++ ([true] ++ (V false b ++ [true]))))) = _
  rw [repV,←List.append_assoc (V false (2*n)) (V false 4),←vAdd,←List.append_assoc (V false 1) (V false (2*n+4)),←vAdd]
  rw [show 1+(2*n+4)=2*(n+1)+3 by omega]

theorem innerStep (n b : Nat) : ∃ t, 0<t ∧ run0 table t (C n (b+1)) = some (C (n+1) b) := by
  have hi := innerInput n b
  have ho := innerOutput n b
  have hm : b%4=0 ∨ b%4=1 ∨ b%4=2 ∨ b%4=3 := by omega
  rcases hm with h|h|h|h
  · have h' : (b+1)%4=1 := by omega
    refine ⟨15+4*n,by omega,?_⟩
    have H := inner1 n (V false b ++ [true])
    rw [hi,ho] at H
    simpa only [C,h,h',show V true 0 = [] by rfl,show V true 1 = [true] by rfl,show V true 2 = [true,true] by rfl,show V true 3 = [true,true,true] by rfl] using H
  · have h' : (b+1)%4=2 := by omega
    refine ⟨15+4*n,by omega,?_⟩
    have H := inner2 n (V false b ++ [true])
    rw [hi,ho] at H
    simpa only [C,h,h',show V true 0 = [] by rfl,show V true 1 = [true] by rfl,show V true 2 = [true,true] by rfl,show V true 3 = [true,true,true] by rfl] using H
  · have h' : (b+1)%4=3 := by omega
    refine ⟨15+4*n,by omega,?_⟩
    have H := inner3 n (V false b ++ [true])
    rw [hi,ho] at H
    simpa only [C,h,h',show V true 0 = [] by rfl,show V true 1 = [true] by rfl,show V true 2 = [true,true] by rfl,show V true 3 = [true,true,true] by rfl] using H
  · have h' : (b+1)%4=0 := by omega
    refine ⟨21+4*n,by omega,?_⟩
    have H := inner0 n (V false b ++ [true])
    rw [hi,ho] at H
    simpa only [C,h,h',show V true 0 = [] by rfl,show V true 1 = [true] by rfl,show V true 2 = [true,true] by rfl,show V true 3 = [true,true,true] by rfl] using H

theorem drain (b n : Nat) : ∃ t, run0 table t (C n b) = some (C (n+b) 0) := by
  induction b generalizing n with
  | zero => exact ⟨0,by simp [run0]⟩
  | succ b ih =>
    obtain ⟨t,_,h⟩ := innerStep n b
    obtain ⟨u,hu⟩ := ih (n+1)
    exact ⟨t+u,by simpa only [show n+1+b=n+(b+1) by omega] using join0 h hu⟩

theorem enterOuter (k : Nat) : run0 table (21+4*k) (outer k) = some (C 0 (4*k+3)) := by
  have H := begin k
  have h1 : [true,true,true,true] ++ rep [true,true,true,true] k ++ [false] = V true (4*k+4) ++ [false] := by
    change V true 4 ++ rep (V true 4) k ++ [false] = _
    rw [repV,←vAdd]
    congr 2 <;> omega
  have h2 : [true,true,false,false,false,true] ++ rep [false,false,false,false] k ++ [false,false,false,true] = (C 0 (4*k+3)).l := by
    simp only [List.append_assoc,C]
    change [true,true,false,false,false,true] ++ (rep (V false 4) k ++ (V false 3 ++ [true])) = _
    rw [repV]
    rw [←List.append_assoc (V false (4*k)) (V false 3),←vAdd]
    rfl
  rw [h1,h2] at H
  simpa only [outer,C,show (4*k+3)%4=3 by omega,show V true 3=[true,true,true] by rfl] using H

theorem finishOuter (n : Nat) : run0 table (11+2*n) (C n 0) = some ⟨0,[false],V true (2*n+6) ++ [false]⟩ := by
  have h1 := finish n
  have h2 := resetm0 ([true] ++ rep [true,true] n ++ [true,true,true,true,false])
  have H := join0 h1 h2
  have h3 : [true,true,false,false,false] ++ rep [false,false] n ++ [true,true] = (C n 0).l := by
    change [true,true] ++ V false 3 ++ rep (V false 2) n ++ [true,true] = _
    rw [repV]
    simp only [List.append_assoc]
    rw [←List.append_assoc (V false 3) (V false (2*n)),←vAdd]
    have he : 3+2*n=2*n+3 := by omega
    rw [he]
    simp only [C, List.append_assoc,show V false 0=[] by rfl,List.nil_append]
    rfl
  have h4 : [true] ++ ([true] ++ rep [true,true] n ++ [true,true,true,true,false]) = V true (2*n+6) ++ [false] := by
    simp only [List.append_assoc]
    change V true 2 ++ (rep (V true 2) n ++ (V true 4 ++ [false])) = _
    rw [repV,←List.append_assoc (V true (2*n)) (V true 4),←vAdd,←List.append_assoc (V true 2) (V true (2*n+4)),←vAdd]
    rw [show 2+(2*n+4)=2*n+6 by omega]
  rw [h3,h4] at H
  simpa only [C,show V true (0%4)=[] by rfl,show 8+2*n+3=11+2*n by omega] using H

theorem epoch (k : Nat) : ∃ t, 0<t ∧ run0 table t (outer k) = some (outer (2*k+2)) := by
  obtain ⟨t,h⟩ := drain (4*k+3) 0
  rw [Nat.zero_add] at h
  have H := join0 (join0 (enterOuter k) h) (finishOuter (4*k+3))
  refine ⟨21+4*k+t+(11+2*(4*k+3)),by omega,?_⟩
  simpa only [Nat.zero_add,outer,show 2*(4*k+3)+6=4*(2*k+2)+4 by omega] using H

def ks : Nat → Nat
  | 0 => 2
  | n+1 => 2*ks n+2

theorem entry : run0 table 104 ⟨0,[],[]⟩ = some (outer (ks 0)) := by rfl
open BB6Coverage.Agent50Zipper

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  have arbitrary : ∀ n, ∃ t k, n≤t ∧ run0 table t ⟨0,[],[]⟩ = some (outer k) := by
    intro n
    induction n with
    | zero => exact ⟨104,2,by omega,entry⟩
    | succ n ih =>
      obtain ⟨t,k,ht,hr⟩ := ih
      obtain ⟨t',ht',hr'⟩ := epoch k
      exact ⟨t+t',2*k+2,by omega,join0 hr hr'⟩
  intro n
  obtain ⟨t,k,ht,hr⟩ := arbitrary n
  have hz : (zrun table t start).map project = some (outer k) := (run_project table t start).trans hr
  cases h : zrun table t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound table m hm t start z h
    rw [start_embed,show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some _ => rfl
#print axioms never
end BB6.Agent19Raw40.A1LC0RE.Leaf388
