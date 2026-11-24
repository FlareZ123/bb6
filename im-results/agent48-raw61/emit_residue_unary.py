"""Generate two three-residue unary invariant proofs."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent
shared=ROOT.parent/"agent48-raw63-counter"/"emit_counter.py"
scope={"__file__":str(shared)}
exec(shared.read_text().split("\nTABLES=",1)[0],scope)
globals().update({k:v for k,v in scope.items() if not k.startswith("__") and k!="ROOT"})
tables={401:"1RB0LF_1RC0LA_0RD---_1LD1RE_0RC0LB_1LC1LE",481:"1RB0LF_1RC0LA_0RD---_1LD1RE_0RC0LB_1RE1LE"}
out=["import Agent48CounterCore","namespace BB6.Agent48ResidueUnary","open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent48Counter","set_option maxRecDepth 100000","set_option maxHeartbeats 0","set_option linter.unusedVariables false"]
for i,s in tables.items():
    p=tuple(parse(s));out += [f"namespace M{i}",table(p)]
    v=26 if i==401 else 24
    for j,src,dst,a in [(0,"001111","101",10),(1,"0011111","1011",12),(2,"0011","101111",v)]:
        st=cfg(3,lit(src)+repeat("1111","n"),())
        tg=cfg(3,lit(dst),(lit("0001") if j!=2 else ())+repeat("0001","n"))
        out.append(macro(p,f"start{j}",st,tg,("n",),(a,4,0))[0])
    out.append(f"""
def ones := [true,true,true,true]
def token := [false,false,false,true]
def F (r n : Nat) : Z0 := ⟨3,[false,false] ++ List.replicate r true ++ rep ones n,[]⟩
def G (L R : List Bool) : Z0 := ⟨3,[true,false] ++ L,R⟩
theorem transfer (L R : List Bool) : run0 table 18 (G L (token++R)) = some (G (ones++L) R) := by rfl
theorem extend (L : List Bool) : run0 table 18 (G L []) = some ⟨3,[false,false]++ones++L,[]⟩ := by rfl
theorem drain (n : Nat) (L R : List Bool) : run0 table (18*n) (G L (rep token n++R)) = some (G (rep ones n++L) R) := by
  induction n generalizing L with
  | zero => simp [rep,run0]
  | succ n ih =>
    have h1 := transfer L (rep token n++R)
    have h2 := ih (ones++L)
    have h := join0 h1 h2
    rw [Nat.mul_succ,Nat.add_comm (18*n) 18]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep ones n) ones L,rep_snoc ones n] using h
theorem onesComm (r n : Nat) : rep ones n ++ List.replicate r true = List.replicate r true ++ rep ones n := by
  induction r with
  | zero => simp
  | succ r ih =>
    change rep ones n ++ ([true] ++ List.replicate r true) =
      [true] ++ (List.replicate r true ++ rep ones n)
    have hh : rep ones n ++ [true] = [true] ++ rep ones n := by
      simpa [ones] using (rotate true [true,true,true] n).symm
    rw [← List.append_assoc, hh, List.append_assoc, ih]
theorem return0 (n : Nat) : ∃ t, 0<t ∧ run0 table t (F 4 n) = some (F 5 (n+1)) := by
  have h1 : run0 table (10+4*n) (F 4 n) = some (G [true] (rep token (n+1))) := by
    simpa only [F,G,token,ones,rep,List.replicate_succ,List.replicate_zero,List.append_assoc,List.cons_append,List.nil_append] using start0 n
  have h2 := drain (n+1) [true] []
  simp only [List.append_nil] at h2
  have h3 := extend (rep ones (n+1)++[true])
  have h := join0 (join0 h1 h2) h3
  refine ⟨(10+4*n)+18*(n+1)+18,by omega,?_⟩
  have hh := onesComm 1 (n+1)
  simp only [List.replicate_succ,List.replicate_zero] at hh
  rw [hh] at h
  simpa only [F,ones,List.replicate_succ,List.replicate_zero,List.append_assoc,List.cons_append,List.nil_append] using h
theorem return1 (n : Nat) : ∃ t, 0<t ∧ run0 table t (F 5 n) = some (F 2 (n+2)) := by
  have h1 : run0 table (12+4*n) (F 5 n) = some (G [true,true] (rep token (n+1))) := by
    simpa only [F,G,token,ones,rep,List.replicate_succ,List.replicate_zero,List.append_assoc,List.cons_append,List.nil_append] using start1 n
  have h2 := drain (n+1) [true,true] []
  simp only [List.append_nil] at h2
  have h3 := extend (rep ones (n+1)++[true,true])
  have h := join0 (join0 h1 h2) h3
  refine ⟨(12+4*n)+18*(n+1)+18,by omega,?_⟩
  have hh := onesComm 2 (n+1)
  simp only [List.replicate_succ,List.replicate_zero] at hh
  rw [hh] at h
  simpa only [F,ones,rep,List.replicate_succ,List.replicate_zero,List.append_assoc,List.cons_append,List.nil_append] using h
theorem return2 (n : Nat) : ∃ t, 0<t ∧ run0 table t (F 2 n) = some (F 4 (n+1)) := by
  have h1 : run0 table ({v}+4*n) (F 2 n) = some (G ones (rep token n)) := by
    simpa only [F,G,token,ones,rep,List.replicate_succ,List.replicate_zero,List.append_assoc,List.cons_append,List.nil_append] using start2 n
  have h2 := drain n ones []
  simp only [List.append_nil] at h2
  have h3 := extend (rep ones n++ones)
  have h := join0 (join0 h1 h2) h3
  refine ⟨({v}+4*n)+18*n+18,by omega,?_⟩
  rw [rep_snoc] at h
  simpa only [F,ones,rep,List.replicate_succ,List.replicate_zero,List.append_assoc,List.cons_append,List.nil_append] using h
def invariant (z : Z0) : Prop := ∃ n, z = F 4 n ∨ z = F 5 n ∨ z = F 2 n
theorem entry : run0 table 3 ⟨0,[],[]⟩ = some (F 2 0) := by rfl
theorem progress (z : Z0) (hz : invariant z) : ∃ t d, 0<t ∧ run0 table t z = some d ∧ invariant d := by
  obtain ⟨n,h|h|h⟩ := hz
  · subst z
    obtain ⟨t,hp,ht⟩ := return0 n
    exact ⟨t,_,hp,ht,n+1,Or.inr (Or.inl rfl)⟩
  · subst z
    obtain ⟨t,hp,ht⟩ := return1 n
    exact ⟨t,_,hp,ht,n+2,Or.inr (Or.inr rfl)⟩
  · subst z
    obtain ⟨t,hp,ht⟩ := return2 n
    exact ⟨t,_,hp,ht,n+1,Or.inl rfl⟩
theorem live (n : Nat) : ∃ t z, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z ∧ invariant z :=
  arbitraryLive_of_progress table invariant 3 (F 2 0) entry ⟨0,Or.inr (Or.inr rfl)⟩ progress n
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_progress table invariant 3 (F 2 0) entry ⟨0,Or.inr (Or.inr rfl)⟩ progress m hm
#print axioms never
end M{i}""")
out.append("end BB6.Agent48ResidueUnary")
(ROOT/"Agent48Raw61ResidueUnary.lean").write_text("\n\n".join(out)+"\n")
