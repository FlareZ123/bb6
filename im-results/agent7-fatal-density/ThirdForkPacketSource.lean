import RayDepthResidue
import RayTThreeGap
set_option maxHeartbeats 0

namespace CascadeThirdForkPacketSource

open CascadeRayDepthResidue CascadeRayDepthHensel CascadeRayPeriod
open CascadeOddRay CascadeFiveForced CascadeResetInverse CascadeSweep
open CascadeRayTThreeGap CascadeForkOddDead

/-- The three 3-adic lifts in a canonical 162-index ray packet. -/
def packetIndex (n b t : Nat) : Nat :=
  depthResidue n 3 + (3*b+t)*54

/-- The exact quotient and third-valuation source predecessor at a packet index. -/
def packetD (n b t : Nat) : Nat :=
  (2*ray n (packetIndex n b t)+5)/81

def packetQ (n b t : Nat) : Nat :=
  16*packetD n b t-(2^n+n+2)

private def thirdPacketCoeff (n j : Nat) : Int :=
  (2*n+3:Int)*(2:Int)^(j+1)*depthCoeff 3

private theorem shifted_linear_pow (m:Nat) : m+21≤2^(m+5):=by
  induction m with
  | zero=>norm_num
  | succ m ih=>
    have he:m+1+5=(m+5)+1:=by omega
    rw [he,Nat.pow_succ]
    omega

private theorem n_add_one_le_pow (n:Nat) (hn:20≤n):
    n+1≤2^(n-15):=by
  calc
    n+1=(n-20)+21:=by omega
    _≤2^((n-20)+5):=shifted_linear_pow (n-20)
    _=2^(n-15):=by congr 1 <;> omega

private theorem linear_term_le (n:Nat) (hn:20≤n):
    16384*(n+1)≤2^(n-1):=by
  have h:=n_add_one_le_pow n hn
  have hc:16384=2^14:=by norm_num
  rw [hc]
  calc
    2^14*(n+1)≤2^14*2^(n-15):=Nat.mul_le_mul_left (2^14) h
    _=2^(n-1):=by
      rw [←Nat.pow_add]
      congr 1
      omega

private theorem depth_residue_even (n:Nat)
    (hn:n%6=4 ∨ n%6=5):
    depthResidue n 3%2=0:=by
  have hlt:=depthResidue_lt n 3
  have hdiv:(3:Int)^4∣signedZ n (depthResidue n 3):=by
    apply (depthResidue_iff n 3 (depthResidue n 3) hn).2
    exact Nat.mod_eq_of_lt hlt
  have h3:(3:Int)∣signedZ n (depthResidue n 3):=by
    apply dvd_trans ?_ hdiv
    refine ⟨(3:Int)^3,?_⟩
    ring
  have hz:=Int.dvd_iff_emod_eq_zero.mp h3
  exact (signedZ_mod_three_even_iff n (depthResidue n 3) hn).mp hz

private theorem packet_index_mod (n b t:Nat):
    packetIndex n b t%depthPeriod 3=depthResidue n 3:=by
  have hp:depthPeriod 3=54:=by norm_num [depthPeriod]
  have hlt:=depthResidue_lt n 3
  rw [hp]
  unfold packetIndex
  omega

private theorem packet_index_even (n b t:Nat)
    (hn:n%6=4 ∨ n%6=5):
    packetIndex n b t%2=0:=by
  have he:=depth_residue_even n hn
  unfold packetIndex
  omega

private theorem packet_index_le (n a b t:Nat)
    (hn:257≤n)
    (hsector:n%6=4 ∨ n%6=5)
    (hpacket:a+162*(b+1)+13≤n)
    (ht:t<3):
    a+packetIndex n b t+15≤n:=by
  have hlt:=depthResidue_lt n 3
  have he:=depth_residue_even n hsector
  have hbase:depthResidue n 3≤52:=by
    omega
  unfold packetIndex
  omega

private theorem ray_margin_of_index (n a j:Nat)
    (hn:257≤n)
    (ha:2*n+3<2^(a+1))
    (hindex:a+j+15≤n):
    2048*deficit n j+16384*n+16384≤2^n:=by
  have hn20:20≤n:=by omega
  have hlin:=linear_term_le n hn20
  have hclosed:=deficit_closed n j (by omega:1≤n)
  have hc:2*n+3≤2^(a+1):=by omega
  have hprod:2^j*(2*n+3)≤2^(j+a+1):=by
    calc
      2^j*(2*n+3)≤2^j*2^(a+1):=Nat.mul_le_mul_left (2^j) hc
      _=2^(j+a+1):=by
        rw [←Nat.pow_add]
        congr 1
        omega
  have hpow:2^(j+a+1)≤2^(n-14):=
    Nat.pow_le_pow_right (by decide:0<(2:Nat)) (by omega)
  have hD: deficit n j≤2^(n-14):=by omega
  have hDmul:2048*deficit n j≤2^(n-3):=by
    calc
      2048*deficit n j≤2048*2^(n-14):=Nat.mul_le_mul_left 2048 hD
      _=2^(n-3):=by
        have h2048:2048=2^11:=by norm_num
        rw [h2048,←Nat.pow_add]
        congr 1
        omega
  have hp1:2^n=8*2^(n-3):=by
    have he:n=(n-3)+3:=by omega
    rw [he,Nat.pow_add]
    norm_num
  have hp2:2^(n-1)=4*2^(n-3):=by
    have he:n-1=(n-3)+2:=by omega
    rw [he,Nat.pow_add]
    norm_num
  have hsum:2^(n-3)+2^(n-1)≤2^n:=by
    rw [hp1,hp2]
    omega
  calc
    2048*deficit n j+16384*n+16384
        =2048*deficit n j+16384*(n+1):=by ring
    _≤2^(n-3)+2^(n-1):=Nat.add_le_add hDmul hlin
    _≤2^n:=hsum

private theorem source_band_of_margin (n j d:Nat)
    (hn:257≤n)
    (hm:2048*deficit n j+16384*n+16384≤2^n)
    (hz:2*ray n j+5=81*d):
    6*2^(n-3)+1≤8*d ∧ 8*d≤8*2^(n-3)-1:=by
  have hp:2^n=8*2^(n-3):=by
    have he:n=(n-3)+3:=by omega
    rw [he,Nat.pow_add]
    norm_num
  have hr:ray n j+deficit n j=4*2^n:=by
    dsimp [ray]
    omega
  have hx:8*(2*ray n j+5)+16*deficit n j=64*2^n+40:=by omega
  have hsmall:64*deficit n j≤2^n:=by omega
  have hp256:256≤2^n:=by
    have hpow:2^8≤2^n:=
      Nat.pow_le_pow_right (by decide:0<(2:Nat)) (by omega)
    norm_num at hpow
  have hlow:81*(6*2^(n-3)+1)≤8*(2*ray n j+5):=by
    rw [hp] at hx
    omega
  have hxsmall:2*ray n j+5+2*deficit n j=8*2^n+5:=by omega
  have hupper:8*(2*ray n j+5)≤81*(8*2^(n-3)-1):=by
    rw [hp] at hxsmall
    omega
  constructor
  · rw [hz] at hlow
    omega
  · rw [hz] at hupper
    omega

/-- Every one of the three lifts in a complete physical packet is a genuine
    t=3 first-reset parent, with the source-certified high-margin hypotheses. -/
private theorem packet_feeder_data (n a b t:Nat)
    (hn:257≤n)
    (hsector:n%6=4 ∨ n%6=5)
    (ha:2^a≤2*n+3 ∧ 2*n+3<2^(a+1))
    (hpacket:a+162*(b+1)+13≤n)
    (ht:t<3):
    packetD n b t%2=1 ∧
    2048*deficit n (packetIndex n b t)+16384*n+16384≤2^n ∧
    6*2^(n-3)+1≤8*packetD n b t ∧
    8*packetD n b t≤8*2^(n-3)-1 ∧
    2*ray n (packetIndex n b t)+5=81*packetD n b t ∧
    16*packetD n b t=2^n+packetQ n b t+n+2 ∧
    16*packetD n b t=8*2^(n-3)+packetQ n b t+(n-3)+5 ∧
    ResetParent (packetQ n b t) (ray n (packetIndex n b t)) ∧
    signedZ n (packetIndex n b t)=(81*(packetD n b t:Int)):=by
  let j:=packetIndex n b t
  have hjmod: j%depthPeriod 3=depthResidue n 3:=packet_index_mod n b t
  have hdivZ:(3:Int)^4∣signedZ n j:=
    (depthResidue_iff n 3 j hsector).mp hjmod
  have hindex:a+j+15≤n:=packet_index_le n a b t hn hsector hpacket ht
  have hm:=ray_margin_of_index n a j hn ha.2 hindex
  have hmargin: deficit n j≤2^n:=by omega
  have hnum:=signed_ray_eq_numerator n j (by omega:4≤n) hmargin
  have hdivX:(81:Int)∣(2*ray n j+5:Int):=by
    have hp:(3:Int)^4=81:=by norm_num
    rw [←hnum,←hp]
    exact hdivZ
  have hdivNat:81∣2*ray n j+5:=by exact_mod_cast hdivX
  let d:Nat:=(2*ray n j+5)/81
  have hmod:(2*ray n j+5)%81=0:=Nat.dvd_iff_mod_eq_zero.mp hdivNat
  have hz:2*ray n j+5=81*d:=by
    dsimp [d]
    omega
  have hd:d%2=1:=by
    have hxodd:(2*ray n j+5)%2=1:=by omega
    rw [hz] at hxodd
    norm_num at hxodd
    omega
  have hb:=source_band_of_margin n j d hn hm hz
  have hp:2^n=8*2^(n-3):=by
    have he:n=(n-3)+3:=by omega
    rw [he,Nat.pow_add]
    norm_num
  have hp2:2^(n-1)=4*2^(n-3):=by
    have he:n-1=(n-3)+2:=by omega
    rw [he,Nat.pow_add]
    norm_num
  have hlin:=linear_term_le n (by omega)
  have hsmall:n+2≤4*2^(n-3):=by
    rw [←hp2]
    omega
  have hlow:12*2^(n-3)+2≤16*d:=by omega
  have hqnon:2^n+n+2≤16*d:=by
    rw [hp]
    omega
  let q:Nat:=16*d-(2^n+n+2)
  have hqeq:16*d=2^n+q+n+2:=by
    dsimp [q]
    omega
  have heOdd:16*d=8*2^(n-3)+q+(n-3)+5:=by
    rw [hp]
    omega
  have hparent:ResetParent q (ray n j):=by
    apply Or.inr
    refine ⟨n-3,3,d,hd,?_,?_,?_⟩
    · simpa using hb
    · simpa using hz
    · calc
        2*(2^3*d)=16*d:=by norm_num
        _=8*2^(n-3)+q+(n-3)+5:=heOdd
  have hphys:signedZ n j=(81*(d:Int)):=by
    rw [hnum]
    exact_mod_cast hz
  simpa [j,d,q,packetD,packetQ] using
    (show d%2=1 ∧
      2048*deficit n j+16384*n+16384≤2^n ∧
      6*2^(n-3)+1≤8*d ∧
      8*d≤8*2^(n-3)-1 ∧
      2*ray n j+5=81*d ∧
      16*d=2^n+q+n+2 ∧
      16*d=8*2^(n-3)+q+(n-3)+5 ∧
      ResetParent q (ray n j) ∧
      signedZ n j=(81*(d:Int)) from
      ⟨hd,hm,hb.1,hb.2,hz,hqeq,heOdd,hparent,hphys⟩)


private theorem ray_strict_decreasing_on_margin (n j1 j2:Nat)
    (hn:4≤n)
    (hm1:deficit n j1≤2^n)
    (hm2:deficit n j2≤2^n)
    (hindex:j1<j2):
    ray n j2<ray n j1:=by
  have hpowle:2^j1≤2^(j2-1):=
    Nat.pow_le_pow_right (by decide:0<(2:Nat)) (by omega)
  have hpbase:1≤2^(j2-1):=Nat.one_le_pow (j2-1) 2 (by decide)
  have hstep:j2=(j2-1)+1:=by omega
  have hpowlt:2^(j2-1)<2^j2:=by
    rw [hstep,Nat.pow_succ]
    omega
  have hpow:2^j1<2^j2:=lt_of_le_of_lt hpowle hpowlt
  have hc:0<2*n+3:=by omega
  have hclosed1:=deficit_closed n j1 (by omega)
  have hclosed2:=deficit_closed n j2 (by omega)
  have hprod:2^j1*(2*n+3)<2^j2*(2*n+3):=
    Nat.mul_lt_mul_of_pos_right hpow hc
  have hdef: deficit n j1<deficit n j2:=by omega
  have hr1:ray n j1+deficit n j1=4*2^n:=by
    dsimp [ray]
    omega
  have hr2:ray n j2+deficit n j2=4*2^n:=by
    dsimp [ray]
    omega
  omega

private theorem packet_index_lex (n b1 t1 b2 t2:Nat)
    (ht1:t1<3) (ht2:t2<3)
    (hlex:b1<b2 ∨ (b1=b2 ∧ t1<t2)):
    packetIndex n b1 t1<packetIndex n b2 t2:=by
  unfold packetIndex
  rcases hlex with h|⟨rfl,h⟩ <;> omega

/-- The predecessor heights are strictly ordered by packet and lift index.
    This certifies disjointness of the per-packet parentless families. -/
theorem packetQ_strict_lex (n a b1 t1 b2 t2:Nat)
    (hn:257≤n)
    (hsector:n%6=4 ∨ n%6=5)
    (ha:2^a≤2*n+3 ∧ 2*n+3<2^(a+1))
    (hpacket1:a+162*(b1+1)+13≤n)
    (hpacket2:a+162*(b2+1)+13≤n)
    (ht1:t1<3) (ht2:t2<3)
    (hlex:b1<b2 ∨ (b1=b2 ∧ t1<t2)):
    packetQ n b2 t2<packetQ n b1 t1:=by
  obtain ⟨hd1,hm1,hb1L,hb1U,hz1,hqeq1,he1,hp1,hphys1⟩ :=
    packet_feeder_data n a b1 t1 hn hsector ha hpacket1 ht1
  obtain ⟨hd2,hm2,hb2L,hb2U,hz2,hqeq2,he2,hp2,hphys2⟩ :=
    packet_feeder_data n a b2 t2 hn hsector ha hpacket2 ht2
  have hmargin1:deficit n (packetIndex n b1 t1)≤2^n:=by omega
  have hmargin2:deficit n (packetIndex n b2 t2)≤2^n:=by omega
  have hj:=packet_index_lex n b1 t1 b2 t2 ht1 ht2 hlex
  have hr:=ray_strict_decreasing_on_margin n
    (packetIndex n b1 t1) (packetIndex n b2 t2) (by omega)
    hmargin1 hmargin2 hj
  have hX:2*ray n (packetIndex n b2 t2)+5<
      2*ray n (packetIndex n b1 t1)+5:=by omega
  have hd:packetD n b2 t2<packetD n b1 t1:=by
    rw [hz1,hz2] at hX
    omega
  rw [hqeq1,hqeq2]
  omega

/-- Modulo 243, the quotient of the three packet lifts is an affine
    progression with a nonzero 3-adic step. -/
private theorem packet_quotient_mod (n b t dBase dt:Nat)
    (ht:t<3)
    (hphysBase:signedZ n (depthResidue n 3)=(81*(dBase:Int)))
    (hphysT:signedZ n (packetIndex n b t)=(81*(dt:Int))):
    (dt:Int)%3=
      ((dBase:Int)-thirdPacketCoeff n (depthResidue n 3)*t)%3:=by
  let base:=depthResidue n 3
  let A:=thirdPacketCoeff n base
  have hp3:depthPeriod 3=54:=by norm_num [depthPeriod]
  have hp4:depthPeriod 4=162:=by norm_num [depthPeriod]
  have hpow4:(3:Int)^(3+1)=81:=by norm_num
  have hpow5:(3:Int)^(3+2)=243:=by norm_num
  have hpow5a:(3:Int)^(4+1)=243:=by norm_num
  have hidx:packetIndex n b t=base+t*54+b*162:=by
    unfold packetIndex
    dsimp [base]
    omega
  have hper:=signedZ_period_mul n (base+t*54) 4 b
  have hper':
      signedZ n (packetIndex n b t)%243=
      signedZ n (base+t*54)%243:=by
    simpa [hidx,hp4,hpow5a] using hper
  have hshift:=signedZ_shift_digit_mod n base 3 t ht
  have hshift':
      signedZ n (base+t*54)%243=
      (signedZ n base-81*A*t)%243:=by
    simpa [hp3,hpow4,hpow5,A,thirdPacketCoeff] using hshift
  have hmod:
      signedZ n (packetIndex n b t)%243=
      (81*(dBase:Int)-81*A*t)%243:=by
    calc
      _=signedZ n (base+t*54)%243:=hper'
      _=(signedZ n base-81*A*t)%243:=hshift'
      _=(81*(dBase:Int)-81*A*t)%243:=by rw [hphysBase]
  have hsub:
      (81*(dt:Int)-(81*(dBase:Int)-81*A*t))%243=0:=by
    have hh: (signedZ n (packetIndex n b t)-
      (81*(dBase:Int)-81*A*t))%243=0:=
      (Int.emod_eq_emod_iff_emod_sub_eq_zero).mp hmod
    simpa [hphysT] using hh
  have hfactor:
      (81:Int)*((dt:Int)-(dBase:Int)+A*t)=
      81*(dt:Int)-(81*(dBase:Int)-81*A*t):=by ring
  rw [hfactor] at hsub
  have hdiv:(243:Int)∣81*((dt:Int)-(dBase:Int)+A*t):=
    Int.dvd_iff_emod_eq_zero.mpr hsub
  have h243:(243:Int)=81*3:=by norm_num
  rw [h243] at hdiv
  have hquot:(3:Int)∣((dt:Int)-(dBase:Int)+A*t):=
    (Int.mul_dvd_mul_iff_left (by norm_num:(81:Int)≠0)).mp hdiv
  have hzero:(((dt:Int)-(dBase:Int)+A*t)%3)=0:=
    Int.dvd_iff_emod_eq_zero.mp hquot
  omega

private theorem packet_q_mod (n d q:Nat)
    (hsector:n%6=4 ∨ n%6=5)
    (hqeq:16*d=2^n+q+n+2):
    q%3=if n%6=4 then (d+2)%3 else d%3:=by
  rcases hsector with h4|h5
  · have hn3:n%3=1:=by omega
    have hp:=pow_sector_mod_three n (Or.inl h4)
    have hp3:2^n%3=1:=by omega
    simp [h4]
    omega
  · have hn3:n%3=2:=by omega
    have hp:=pow_sector_mod_three n (Or.inr h5)
    have hp3:2^n%3=2:=by omega
    simp [h5]
    omega


/-- The exact two-arm ResetParent grammar has no parent in the t=3 gap:
    the even arm misses every band, while the odd arm forces q=2 mod 3. -/
private theorem no_reset_parent_in_ray_gap (n q:Nat)
    (hn:3≤n)
    (hmod:q%3≠2)
    (hgap:2^(n-1)<q ∧ 2*q+2<3*2^(n-1)):
    ¬∃w, ResetParent w q:=by
  rintro ⟨w,hp⟩
  rcases hp with ⟨k,hband,heq⟩ | ⟨k,t,d,hd,hband,hout,heq⟩
  · exact (gap_avoids_even_images (n-1) q (by omega) hgap.1 hgap.2 k hband)
  · have hdiv:3∣2*q+5:=by
      refine ⟨3^t*d,?_⟩
      rw [hout,Nat.pow_succ]
      ring
    have hzero:(2*q+5)%3=0:=Nat.dvd_iff_mod_eq_zero.mp hdiv
    have hqmod:q%3=2:=by omega
    exact hmod hqmod

/-- Every complete 162-index physical packet on either surviving #746 gate
    ray contains two distinct genuine t=3 ResetParent feeders that themselves
    have no predecessor in the complete original source reset grammar. -/
theorem packet_has_two_parentless_third_feeders (n a b:Nat)
    (hn:257≤n)
    (hsector:n%6=4 ∨ n%6=5)
    (ha:2^a≤2*n+3 ∧ 2*n+3<2^(a+1))
    (hpacket:a+162*(b+1)+13≤n):
    ∃ t0 t1:Nat,
      t0<3 ∧ t1<3 ∧ t0≠t1 ∧
      packetQ n b t0≠packetQ n b t1 ∧
      ResetParent (packetQ n b t0) (ray n (packetIndex n b t0)) ∧
      ResetParent (packetQ n b t1) (ray n (packetIndex n b t1)) ∧
      (¬∃w, ResetParent w (packetQ n b t0)) ∧
      (¬∃w, ResetParent w (packetQ n b t1)) ∧
      ¬ReachC (2,0) (packetQ n b t0,0) ∧
      ¬ReachC (2,0) (packetQ n b t1,0):=by
  have hpacket0:a+162*(0+1)+13≤n:=by omega
  obtain ⟨hdBase,hmBase,hbBaseL,hbBaseU,hzBase,hqBase,heBase,hpBase,hphysBase⟩ :=
    packet_feeder_data n a 0 0 hn hsector ha hpacket0 (by decide)
  obtain ⟨hd0,hm0,hb0L,hb0U,hz0,hq0,he0,hp0,hphys0⟩ :=
    packet_feeder_data n a b 0 hn hsector ha hpacket (by decide)
  obtain ⟨hd1,hm1,hb1L,hb1U,hz1,hq1,he1,hp1,hphys1⟩ :=
    packet_feeder_data n a b 1 hn hsector ha hpacket (by decide)
  obtain ⟨hd2,hm2,hb2L,hb2U,hz2,hq2,he2,hp2,hphys2⟩ :=
    packet_feeder_data n a b 2 hn hsector ha hpacket (by decide)
  have hphysBase' : signedZ n (depthResidue n 3)=
      (81*(packetD n 0 0:Int)):=by
    simpa [packetIndex] using hphysBase
  have hD0:=packet_quotient_mod n b 0 (packetD n 0 0) (packetD n b 0)
    (by decide) hphysBase' hphys0
  have hD1:=packet_quotient_mod n b 1 (packetD n 0 0) (packetD n b 1)
    (by decide) hphysBase' hphys1
  have hD2:=packet_quotient_mod n b 2 (packetD n 0 0) (packetD n b 2)
    (by decide) hphysBase' hphys2
  have hAunit:thirdPacketCoeff n (depthResidue n 3)%3≠0:=by
    simpa [thirdPacketCoeff] using
      (rayCoeff_unit n (depthResidue n 3) 3 hsector)
  have hArem:thirdPacketCoeff n (depthResidue n 3)%3=1 ∨
      thirdPacketCoeff n (depthResidue n 3)%3=2:=by
    have hnon:=Int.emod_nonneg
      (thirdPacketCoeff n (depthResidue n 3)) (by decide:(0:Int)<3)
    have hlt:=Int.emod_lt_of_pos
      (thirdPacketCoeff n (depthResidue n 3)) (by decide:(0:Int)<3)
    omega
  have hD01:(packetD n b 0:Int)%3≠(packetD n b 1:Int)%3:=by
    intro h
    rcases hArem with hA|hA <;> omega
  have hD02:(packetD n b 0:Int)%3≠(packetD n b 2:Int)%3:=by
    intro h
    rcases hArem with hA|hA <;> omega
  have hD12:(packetD n b 1:Int)%3≠(packetD n b 2:Int)%3:=by
    intro h
    rcases hArem with hA|hA <;> omega
  have hD01Nat:packetD n b 0%3≠packetD n b 1%3:=by
    intro h
    apply hD01
    exact_mod_cast h
  have hD02Nat:packetD n b 0%3≠packetD n b 2%3:=by
    intro h
    apply hD02
    exact_mod_cast h
  have hD12Nat:packetD n b 1%3≠packetD n b 2%3:=by
    intro h
    apply hD12
    exact_mod_cast h
  have hQ0:=packet_q_mod n (packetD n b 0) (packetQ n b 0) hsector hq0
  have hQ1:=packet_q_mod n (packetD n b 1) (packetQ n b 1) hsector hq1
  have hQ2:=packet_q_mod n (packetD n b 2) (packetQ n b 2) hsector hq2
  have hQ01:packetQ n b 0%3≠packetQ n b 1%3:=by
    rw [hQ0,hQ1]
    rcases hsector with h4|h5
    · simp [h4] at *
      omega
    · simp [h5] at *
      omega
  have hQ02:packetQ n b 0%3≠packetQ n b 2%3:=by
    rw [hQ0,hQ2]
    rcases hsector with h4|h5
    · simp [h4] at *
      omega
    · simp [h5] at *
      omega
  have hQ12:packetQ n b 1%3≠packetQ n b 2%3:=by
    rw [hQ1,hQ2]
    rcases hsector with h4|h5
    · simp [h4] at *
      omega
    · simp [h5] at *
      omega
  have hgap0:=ray_tthree_parent_gap n (packetIndex n b 0) (n-3)
    (packetD n b 0) (packetQ n b 0) (by omega) hm0 hz0 ⟨hb0L,hb0U⟩ he0
  have hgap1:=ray_tthree_parent_gap n (packetIndex n b 1) (n-3)
    (packetD n b 1) (packetQ n b 1) (by omega) hm1 hz1 ⟨hb1L,hb1U⟩ he1
  have hgap2:=ray_tthree_parent_gap n (packetIndex n b 2) (n-3)
    (packetD n b 2) (packetQ n b 2) (by omega) hm2 hz2 ⟨hb2L,hb2U⟩ he2
  have hnoParent0:packetQ n b 0%3≠2→¬∃w,ResetParent w (packetQ n b 0):=by
    intro hmod
    exact no_reset_parent_in_ray_gap n (packetQ n b 0) (by omega) hmod hgap0
  have hnoParent1:packetQ n b 1%3≠2→¬∃w,ResetParent w (packetQ n b 1):=by
    intro hmod
    exact no_reset_parent_in_ray_gap n (packetQ n b 1) (by omega) hmod hgap1
  have hnoParent2:packetQ n b 2%3≠2→¬∃w,ResetParent w (packetQ n b 2):=by
    intro hmod
    exact no_reset_parent_in_ray_gap n (packetQ n b 2) (by omega) hmod hgap2
  have hdead0:packetQ n b 0%3≠2→
      ¬ReachC (2,0) (packetQ n b 0,0):=by
    intro hmod
    exact ray_tthree_parent_dead n (packetIndex n b 0) (n-3)
      (packetD n b 0) (packetQ n b 0) (by omega) hm0 hz0
      ⟨hb0L,hb0U⟩ he0 hmod
  have hdead1:packetQ n b 1%3≠2→
      ¬ReachC (2,0) (packetQ n b 1,0):=by
    intro hmod
    exact ray_tthree_parent_dead n (packetIndex n b 1) (n-3)
      (packetD n b 1) (packetQ n b 1) (by omega) hm1 hz1
      ⟨hb1L,hb1U⟩ he1 hmod
  have hdead2:packetQ n b 2%3≠2→
      ¬ReachC (2,0) (packetQ n b 2,0):=by
    intro hmod
    exact ray_tthree_parent_dead n (packetIndex n b 2) (n-3)
      (packetD n b 2) (packetQ n b 2) (by omega) hm2 hz2
      ⟨hb2L,hb2U⟩ he2 hmod
  by_cases hbad0:packetQ n b 0%3=2
  · have hgood1:packetQ n b 1%3≠2:=by
      intro hbad1
      exact hQ01 (by omega)
    have hgood2:packetQ n b 2%3≠2:=by
      intro hbad2
      exact hQ02 (by omega)
    refine ⟨1,2,by decide,by decide,by decide,?_,hp1,hp2,?_,?_,?_,?_⟩
    · exact fun h=>hQ12 (by omega)
    · exact hnoParent1 hgood1
    · exact hnoParent2 hgood2
    · exact hdead1 hgood1
    · exact hdead2 hgood2
  · by_cases hbad1:packetQ n b 1%3=2
    · have hgood2:packetQ n b 2%3≠2:=by
        intro hbad2
        exact hQ12 (by omega)
      refine ⟨0,2,by decide,by decide,by decide,?_,hp0,hp2,?_,?_,?_,?_⟩
      · exact fun h=>hQ02 (by omega)
      · exact hnoParent0 hbad0
      · exact hnoParent2 hgood2
      · exact hdead0 hbad0
      · exact hdead2 hgood2
    · refine ⟨0,1,by decide,by decide,by decide,?_,hp0,hp1,?_,?_,?_,?_⟩
      · exact fun h=>hQ01 (by omega)
      · exact hnoParent0 hbad0
      · exact hnoParent1 hbad1
      · exact hdead0 hbad0
      · exact hdead1 hbad1

#print axioms packet_has_two_parentless_third_feeders

end CascadeThirdForkPacketSource
