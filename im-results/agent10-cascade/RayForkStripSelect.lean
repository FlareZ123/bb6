import PacketSelector
import RayOddForkExtended
set_option maxHeartbeats 0
namespace CascadeRayForkStripSelect
open CascadeResetInverse CascadeSweep CascadeOddRay CascadeFiveForced
open CascadeRayOddStrip

/-- Exact odd dyadic image bands have a unique dyadic scale. -/
private theorem odd_band_scale_unique (u k l:Nat)
  (hk:6*2^k+1≤u ∧ u≤8*2^k-1)
  (hl:6*2^l+1≤u ∧ u≤8*2^l-1):k=l:=by
  by_cases he:k=l
  · exact he
  by_cases hkl:k<l
  · have hp:2^(k+1)≤2^l:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) (by omega)
    rw[Nat.pow_succ] at hp
    omega
  · have hp:2^(l+1)≤2^k:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) (by omega)
    rw[Nat.pow_succ] at hp
    omega

/-- All t=1 odd source parent witnesses of any high-margin fatal-ray node
    automatically use dyadic odd-band exponent n-2, no source cases missed. -/
private theorem tone_scale (n j k d:Nat) (hn:13≤n)
  (hm:32*deficit n j+64*n+128≤2^n)
  (hout:2*ray n j+5=9*d)
  (hb:6*2^k+1≤2*d ∧ 2*d≤8*2^k-1):k=n-2:=by
  have hr:ray n j+deficit n j=4*2^n:=by
    dsimp[ray];omega
  have hp:2^n=4*2^(n-2):=by
    have he:n=(n-2)+2:=by omega
    calc
      2^n=2^((n-2)+2):=congrArg (fun x:Nat=>2^x) he
      _=4*2^(n-2):=by rw[Nat.pow_add];omega
  have hband:6*2^(n-2)+1≤2*d ∧ 2*d≤8*2^(n-2)-1:=by
    constructor <;> omega
  exact odd_band_scale_unique (2*d) k (n-2) hb hband

/-- Lossless rooted classification of every odd inverse branch at any
    high-margin even-ray depth. Original 3-adic t=1 forks can survive
    only through one of the two explicitly exceptional double gates. -/
theorem odd_root_exact_high_gate (n j:Nat) (hn:13≤n)
  (hsector:n%6=4 ∨ n%6=5)
  (hm:32*deficit n j+64*n+128≤2^n):
  oddRootAt n j ↔
    ∃(q k t d:Nat), ReachC (2,0) (q,0) ∧
      (d%2=1 ∧
        (6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1) ∧
        2*ray n j+5=3^(t+1)*d ∧
        2*(2^t*d)=8*2^k+q+k+5) ∧
      (2≤t ∨ (t=1 ∧
        ((2*q+5)%27=0 ∨
         (q%3=0 ∧ (2*(2*q-(2*2^n+(n-2)))+5)%9=0)))) :=by
  constructor
  · rintro ⟨q,hroot,hodd⟩
    obtain ⟨k,t,d,hd,hb,hout,heq⟩:=hodd
    refine ⟨q,k,t,d,hroot,⟨hd,hb,hout,heq⟩,?_⟩
    by_cases ht0:t=0
    · subst t
      have hray:3*2^n≤ray n j ∧ ray n j≤4*2^n:=by
        have hdef:ray n j+deficit n j=4*2^n:=by dsimp[ray];omega
        omega
      have hbad:=CascadeAgent10Four.near_top_no_odd_tzero (ray n j) n
        (by omega) hray.1 hray.2
        ⟨k,d,by simpa using hb,by simpa using hout⟩
      exact False.elim hbad
    · by_cases ht1:t=1
      · subst t
        right
        constructor
        · rfl
        by_cases hdiv:(2*q+5)%27=0
        · exact Or.inl hdiv
        · right
          have h9:2*ray n j+5=9*d:=by simpa using hout
          have hscale:k=n-2:=tone_scale n j k d hn hm h9 (by simpa using hb)
          have heq':4*d=8*2^(n-2)+q+(n-2)+5:=by rw[hscale] at heq; omega
          by_cases hmod:q%3=0
          · by_cases hzmod:(2*(2*q-(2*2^n+(n-2)))+5)%9=0
            · exact ⟨hmod,hzmod⟩
            · exact False.elim ((source_tone_ray_fork_dead_either n j q d
                hn hsector hm h9 heq' hdiv (Or.inr hzmod)) hroot)
          · exact False.elim ((source_tone_ray_fork_dead_either n j q d
              hn hsector hm h9 heq' hdiv (Or.inl hmod)) hroot)
      · left
        omega
  · rintro ⟨q,k,t,d,hroot,⟨hd,hb,hout,heq⟩,hgate⟩
    exact ⟨q,hroot,⟨k,t,d,hd,hb,hout,heq⟩⟩

#print axioms odd_root_exact_high_gate
end CascadeRayForkStripSelect
