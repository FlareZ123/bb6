import RayThirdNoRoot
import PacketSelector
set_option maxHeartbeats 0
namespace CascadeRayTwoTierSelector
open CascadeResetInverse CascadeSweep CascadeOddRay CascadeFiveForced
open CascadeRayOddStrip CascadeRayThirdNoRoot

private theorem odd_band_scale_unique (u k l:Nat)
  (hk:6*2^k+1≤u ∧ u≤8*2^k-1)
  (hl:6*2^l+1≤u ∧ u≤8*2^l-1):k=l:=by
  by_cases he:k=l
  · exact he
  by_cases hklt:k<l
  · have hp:2^(k+1)≤2^l:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) (by omega)
    rw[Nat.pow_succ] at hp
    omega
  · have hp:2^(l+1)≤2^k:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) (by omega)
    rw[Nat.pow_succ] at hp
    omega

private theorem tone_scale (n j k d:Nat) (hn:20≤n)
  (hm:2048*deficit n j+16384*n+16384≤2^n)
  (hz:2*ray n j+5=9*d)
  (hb:6*2^k+1≤2*d ∧ 2*d≤8*2^k-1):k=n-2:=by
  have hp:2^n=4*2^(n-2):=by
    have he:n=(n-2)+2:=by omega
    calc
      2^n=2^((n-2)+2):=congrArg (fun x:Nat=>2^x) he
      _=4*2^(n-2):=by rw[Nat.pow_add];omega
  have hr:ray n j+deficit n j=4*2^n:=by
    dsimp[ray]
    omega
  have hbb:6*2^(n-2)+1≤2*d ∧ 2*d≤8*2^(n-2)-1:=by
    constructor <;> omega
  exact odd_band_scale_unique (2*d) k (n-2) hb hbb

/-- Source-exact classification of every genuine blank-root odd fork along
    an arbitrary high-margin canonical even ray. Under the strong margin,
    the complete t=1 valuation-one ancestry cannot reach the blank root;
    only high valuation at the first or second t=1 fork may survive. -/
theorem exact_odd_fork_two_tier_gate (n j:Nat) (hn:20≤n)
  (hsector:n%6=4 ∨ n%6=5)
  (hm:2048*deficit n j+16384*n+16384≤2^n):
  oddRootAt n j ↔
    ∃(q k t d:Nat), ReachC (2,0) (q,0) ∧
      (d%2=1 ∧
        (6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1) ∧
        2*ray n j+5=3^(t+1)*d ∧
        2*(2^t*d)=8*2^k+q+k+5) ∧
      (2≤t ∨ (t=1 ∧
        ((2*q+5)%27=0 ∨
         (2*(2*q-(2*2^n+(n-2)))+5)%27=0))) :=by
  constructor
  · rintro ⟨q,hroot,⟨k,t,d,hd,hband,hz,heq⟩⟩
    refine ⟨q,k,t,d,hroot,⟨hd,hband,hz,heq⟩,?_⟩
    by_cases ht0:t=0
    · subst t
      have hm0:32*deficit n j+64*n+128≤2^n:=by omega
      have hr:3*2^n≤ray n j ∧ ray n j≤4*2^n:=by
        have hdef:ray n j+deficit n j=4*2^n:=by dsimp[ray];omega
        omega
      have hbad:=CascadeAgent10Four.near_top_no_odd_tzero (ray n j) n
        (by omega) hr.1 hr.2
        ⟨k,d,by simpa using hband,by simpa using hz⟩
      exact False.elim hbad
    · by_cases ht1:t=1
      · subst t
        right
        constructor
        · rfl
        by_cases hqdiv:(2*q+5)%27=0
        · exact Or.inl hqdiv
        · right
          have hz9:2*ray n j+5=9*d:=by simpa using hz
          have heven:4*d=8*2^k+q+k+5:=by omega
          have hk:k=n-2:=tone_scale n j k d hn hm hz9 (by simpa using hband)
          have heven2:4*d=8*2^(n-2)+q+(n-2)+5:=by rw[hk] at heven;exact heven
          have hl:=tone_linear n j q d (by omega)
            (by omega:32*deficit n j+64*n+128≤2^n) hz9 heven2
          let w:=2*q-(2*2^n+(n-2))
          have hpos:2*2^n+(n-2)≤2*q:=by omega
          have hw:2*q=2*2^n+w+(n-2):=by dsimp[w];omega
          by_cases hwdiv:(2*w+5)%27=0
          · exact hwdiv
          · exact False.elim ((offray_fork_dead_both_valuation_one
              n (deficit n j) q w hn hsector hm hl hw hqdiv hwdiv) hroot)
      · left
        omega
  · rintro ⟨q,k,t,d,hroot,⟨hd,hband,hz,heq⟩,hgate⟩
    exact ⟨q,hroot,⟨k,t,d,hd,hband,hz,heq⟩⟩

#print axioms exact_odd_fork_two_tier_gate
end CascadeRayTwoTierSelector
