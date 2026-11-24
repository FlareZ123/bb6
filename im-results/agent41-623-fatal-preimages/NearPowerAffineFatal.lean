import NearPowerSymbolicSource
import NearPowerExamples

namespace BB6.Agent41NearPower
open BB6.Agent41FatalInverse BB6.Agent49ParitySource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

def affineFatal (k : Aff) : SymState := ⟨1,13,k,ac (-5),ac 7-(4:Int)*k⟩

theorem affineFatal_atN (k : Aff) (n : Nat) (hp : 8≤(k.eval n).toNat) :
    (affineFatal k).atN n=fatalState (k.eval n).toNat := by
  have hc : 0≤k.eval n := by omega
  have h := Int.toNat_of_nonneg hc
  unfold SymState.atN fatalState
  change NearState.mk 1 13 (k.eval n).toNat ((ac (-5)).eval n) ((ac 7-(4:Int)*k).eval n) = _
  simp only [eval_ac,eval_sub,eval_scale,h]

/-- Any accepted symbolic certificate proves nonreachability for its affine
exponent. Failure of the checker makes no claim. -/
theorem affineFatal_excluded (k : Aff) (cert : SymCert) (h : symCheck (affineFatal k) cert=true) (n i : Nat) :
    run i≠some (.D (targetX ((k.eval n).toNat-1)) (targetY ((k.eval n).toNat-1))) := by
  have hg : symGuard (affineFatal k)=true := by
    cases cert with
    | stop => simp [symCheck] at h
    | fork wl wr l r =>
      simp only [symCheck,Bool.and_eq_true] at h
      exact h.1.1.1
  simp only [symGuard,Bool.and_eq_true] at hg
  have hh := ge_sound hg.1.1.2 n
  change 8+(Nat.log2 (13+1):Int)+1 ≤ k.eval n at hh
  let p := (k.eval n).toNat
  have hp : 8≤p := by dsimp [p]; omega
  have he : p-1+1=p := by omega
  have hr := fatalState_rep (p-1) (by omega)
  rw [he,←affineFatal_atN k n hp] at hr
  exact symCheck_excludes cert _ n _ _ hr h i

#print axioms affineFatal_excluded
end BB6.Agent41NearPower
