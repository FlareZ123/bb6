import NeedleWord
namespace NeedleSubexp
open NeedleWord

def Edge (x y : Nat) : Prop := ∃ q v, x = 2^v*(2*q+3) ∧ y=x+v+3*(q+1)
def Prefix (f : Nat → Nat) (n : Nat) : Prop := ∀ i<n, Edge (f i) (f (i+1))

theorem edge_strict {x y : Nat} (h : Edge x y) : x<y := by
  obtain ⟨q,v,hx,hy⟩ := h
  omega

theorem prefix_path (f : Nat → Nat) (n : Nat) (h : Prefix f n) (i l : Nat) (hil : i+l≤n) :
    ∃ w, w.length=l ∧ Path w (f i) (f (i+l)) := by
  induction l generalizing i with
  | zero => exact ⟨[], rfl, by simpa using Path.nil (f i)⟩
  | succ l ih =>
    obtain ⟨q,v,hx,hy⟩ := h i (by omega)
    obtain ⟨w,hw,hp⟩ := ih (i+1) (by omega)
    exact ⟨v::w, by simp [hw], by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Path.cons v q hx hy hp⟩

theorem prefix_strict (f : Nat → Nat) (n : Nat) (h : Prefix f n) {i j : Nat} (hij : i<j) (hjn : j≤n) : f i < f j := by
  obtain ⟨w,hw,hp⟩ := prefix_path f n h i (j-i) (by omega)
  rw [show i+(j-i)=j by omega] at hp
  apply path_increasing hp
  intro he
  simp [he] at hw
  omega

theorem prefix_mono (f : Nat → Nat) (n : Nat) (h : Prefix f n) {i j : Nat} (hij : i≤j) (hjn : j≤n) : f i≤f j := by
  rcases Nat.lt_or_eq_of_le hij with hlt|he
  · exact Nat.le_of_lt (prefix_strict f n h hlt hjn)
  · simp [he]

theorem pow_pos (v : Nat) : 0 < 2^v := Nat.pow_pos (by decide)

theorem pow_mono {a b : Nat} (h : a≤b) : 2^a≤2^b := Nat.pow_le_pow_right (by decide) h

theorem val_bound {v q x K : Nat} (hx : x=2^v*(2*q+3)) (hK : x<2^(K+1)) : v≤K := by
  by_cases hn : v≤K
  · exact hn
  ·
    have hpow := pow_mono (show K+1≤v by omega)
    have hm := Nat.mul_le_mul_left (2^v) (show 1≤2*q+3 by omega)
    simp only [Nat.mul_one] at hm
    omega

theorem path_val_bound {w : List Nat} {p c K : Nat} (h : Path w p c) (hK : c<2^(K+1)) : ∀ v∈w, v≤K := by
  induction h with
  | nil => simp
  | @cons w p b c v q hp hb rest ih =>
    intro u hu
    rcases List.mem_cons.mp hu with he|hm
    · subst u
      have hbc := path_nondecreasing rest
      exact val_bound hp (by omega)
    · exact ih hK u hm

theorem weight_lower {w : List Nat} {V : Nat} (h : ∀ v∈w, V≤v) : w.length*(V+1)≤S w := by
  induction w with
  | nil => simp [S]
  | cons v w ih =>
    have hv := h v (by simp)
    have hw := ih (fun u hu => h u (by simp [hu]))
    simp only [List.length_cons,S,Nat.succ_mul]
    omega

def encode (base : Nat) : List Nat → Nat
  | [] => 0
  | v::w => v+base*encode base w

theorem encode_bound {base : Nat} {w : List Nat} (hb : 0<base) (h : ∀ v∈w, v<base) : encode base w<base^w.length := by
  induction w with
  | nil => simp [encode]
  | cons v w ih =>
    have hv := h v (by simp)
    have hw := ih (fun u hu => h u (by simp [hu]))
    have hm := Nat.mul_le_mul_left base (show encode base w+1≤base^w.length by omega)
    simp only [encode,List.length_cons,Nat.pow_succ,Nat.mul_add,Nat.mul_one] at *
    rw [Nat.mul_comm (base^w.length) base]
    omega

theorem encode_inj {base : Nat} {w z : List Nat} (hb : 0<base) (hl : w.length=z.length)
    (hw : ∀ v∈w, v<base) (hz : ∀ v∈z, v<base) (he : encode base w=encode base z) : w=z := by
  induction w generalizing z with
  | nil => cases z <;> simp_all
  | cons v w ih =>
    cases z with
    | nil => simp at hl
    | cons u z =>
      have hv := hw v (by simp)
      have hu := hz u (by simp)
      have hemod := congrArg (fun n => n % base) he
      simp [encode,Nat.add_mod,Nat.mul_mod, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hu] at hemod
      subst u
      simp only [encode] at he
      have hm : base*encode base w = base*encode base z := by omega
      have ht := Nat.mul_left_cancel hb hm
      have hez := ih (by simpa using hl) (fun u hu => hw u (by simp [hu])) (fun u hu => hz u (by simp [hu])) ht
      simp [hez]

theorem same_word_separation {w : List Nat} {p c p' c' K : Nat} (h : Path w p c) (h' : Path w p' c')
    (hS : K≤S w) (hpos : p<p') : 2^K≤p'-p := by
  have hd := Int.natAbs_dvd_natAbs.mpr (cylinder_unique h h')
  rw [Int.natAbs_pow] at hd
  have he : ((p':Int)-(p:Int)).natAbs=p'-p := by omega
  rw [he] at hd
  simp at hd
  exact Nat.le_trans (pow_mono hS) (Nat.le_of_dvd (by omega) hd)

theorem low_edge_from_path {w : List Nat} {p c V : Nat} (h : Path w p c) (hl : ∃ v∈w, v<V) :
    ∃ x y q v, p≤x ∧ y≤c ∧ v<V ∧ x=2^v*(2*q+3) ∧ y=x+v+3*(q+1) := by
  induction h with
  | nil => simp at hl
  | @cons w p b c v q hp hb rest ih =>
    obtain ⟨u,hu,huv⟩ := hl
    rcases List.mem_cons.mp hu with he|hm
    · subst u
      exact ⟨p,b,q,v, Nat.le_refl _, path_nondecreasing rest, huv,hp,hb⟩
    · obtain ⟨x,y,q',v',hpx,hyc,hv',hx,hy⟩ := ih ⟨u,hm,huv⟩
      exact ⟨x,y,q',v',by omega,hyc,hv',hx,hy⟩

def bucket (V x : Nat) : Nat := (x-2^(Nat.log2 x))/2^(Nat.log2 x-V)
def lowCode (V x : Nat) : Nat := Nat.log2 x * 2^V + bucket V x

theorem log_band {x : Nat} (hx : 0<x) : 2^(Nat.log2 x)≤x ∧ x<2^(Nat.log2 x+1) :=
  (Nat.log2_eq_iff (by omega)).mp rfl

theorem bucket_bound {V x : Nat} (hx : 0<x) : bucket V x<2^V := by
  have hband := log_band hx
  have hp : 2^(Nat.log2 x)≤2^V*2^(Nat.log2 x-V) := by
    rw [←Nat.pow_add]
    exact pow_mono (by omega)
  unfold bucket
  apply (Nat.div_lt_iff_lt_mul (pow_pos _)).mpr
  rw [Nat.pow_succ] at hband
  omega

theorem low_code_bound {V x K : Nat} (hx : 0<x) (hK : x<2^(K+1)) : lowCode V x < (K+1)*2^V := by
  have hk : Nat.log2 x≤K := by
    by_cases hn : Nat.log2 x≤K
    · exact hn
    · have hp := pow_mono (show K+1≤Nat.log2 x by omega)
      have hl := (log_band hx).1
      omega
  have hm := Nat.mul_le_mul_right (2^V) (show Nat.log2 x+1≤K+1 by omega)
  unfold lowCode
  rw [Nat.add_mul,Nat.one_mul] at hm
  have hb := bucket_bound (V:=V) hx
  omega

theorem low_gain {V x y q v : Nat} (hv : v<V) (hx : x=2^v*(2*q+3)) (hy : y=x+v+3*(q+1)) :
    x+2^(Nat.log2 x-V)≤y := by
  have hxpos : 0<x := by rw [hx]; exact Nat.mul_pos (pow_pos _) (by omega)
  have hp := (log_band hxpos).1
  have hpow : 2^v*2^(Nat.log2 x-V)≤x := by
    rw [←Nat.pow_add]
    by_cases h : V≤Nat.log2 x
    · exact Nat.le_trans (pow_mono (by omega)) hp
    · rw [show Nat.log2 x-V=0 by omega, Nat.add_zero]
      calc
        2^v ≤ 2^v*(2*q+3) := by
          have hm := Nat.mul_le_mul_left (2^v) (show 1≤2*q+3 by omega)
          simpa using hm
        _ = x := hx.symm
  have hpow' : 2^v*2^(Nat.log2 x-V)≤2^v*(2*q+3) := by
    calc
      _ ≤ x := hpow
      _ = _ := hx
  have hr := Nat.le_of_mul_le_mul_left hpow' (pow_pos v)
  omega

theorem low_code_ne {V x y : Nat} (hx : 0<x) (hy : 0<y) (hgap : x+2^(Nat.log2 x-V)≤y) : lowCode V x≠lowCode V y := by
  intro he
  have hbx := bucket_bound (V:=V) hx
  have hby := bucket_bound (V:=V) hy
  have hdiv := congrArg (fun n => n / 2^V) he
  simp only [lowCode] at hdiv
  rw [Nat.mul_comm (Nat.log2 x), Nat.add_comm, Nat.add_mul_div_left _ _ (pow_pos V),
      Nat.mul_comm (Nat.log2 y), Nat.add_comm (2^V*Nat.log2 y), Nat.add_mul_div_left _ _ (pow_pos V),
      Nat.div_eq_of_lt hbx, Nat.div_eq_of_lt hby, Nat.zero_add, Nat.zero_add] at hdiv
  have hbeq : bucket V x=bucket V y := by simp [lowCode,hdiv] at he; exact he
  unfold bucket at hbeq
  rw [←hdiv] at hbeq
  have hband := (log_band hx).1
  have hle : x-2^(Nat.log2 x)+2^(Nat.log2 x-V)≤y-2^(Nat.log2 x) := by omega
  have hquot := Nat.div_le_div_right (c:=2^(Nat.log2 x-V)) hle
  rw [show x-2^(Nat.log2 x)+2^(Nat.log2 x-V)=x-2^(Nat.log2 x)+2^(Nat.log2 x-V)*1 by simp,
      Nat.add_mul_div_left _ _ (pow_pos _)] at hquot
  omega

theorem finite_count (n M : Nat) (f : Fin n → Nat) (hb : ∀ i, f i<M)
    (hne : ∀ i j : Fin n, i.val<j.val → f i≠f j) : n≤M := by
  have hn : (List.ofFn f).Nodup := by
    rw [List.nodup_iff_pairwise_ne,List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.getElem_ofFn]
    exact hne ⟨i,by simpa using hi⟩ ⟨j,by simpa using hj⟩ hij
  have hs : List.ofFn f ⊆ List.range M := by
    intro x hx
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hx
    rw [←hi,List.mem_range]
    exact hb i
  simpa using List.Nodup.length_le_of_subset hn hs


def BlockCode (K V l p c z : Nat) : Prop :=
  (∃ x y q v, p≤x ∧ y≤c ∧ v<V ∧ x=2^v*(2*q+3) ∧ y=x+v+3*(q+1) ∧ z=lowCode V x) ∨
  (∃ w, w.length=l ∧ Path w p c ∧ (∀ v∈w, V≤v) ∧ z=(K+1)*2^V+encode (K+1) w)

theorem block_code_exists {K V l p c : Nat} {w : List Nat} (hw : w.length=l) (hp : Path w p c) :
    ∃ z, BlockCode K V l p c z := by
  classical
  by_cases hlow : ∃ v∈w, v<V
  · obtain ⟨x,y,q,v,hpx,hyc,hv,hx,hy⟩ := low_edge_from_path hp hlow
    exact ⟨lowCode V x, Or.inl ⟨x,y,q,v,hpx,hyc,hv,hx,hy,rfl⟩⟩
  · have hh : ∀ v∈w, V≤v := by
      intro v hv
      by_cases h : V≤v
      · exact h
      · exact False.elim (hlow ⟨v,hv,by omega⟩)
    exact ⟨(K+1)*2^V+encode (K+1) w, Or.inr ⟨w,hw,hp,hh,rfl⟩⟩

theorem block_code_bound {K V l p c z : Nat} (h : BlockCode K V l p c z) (hc : c<2^(K+1)) :
    z<(K+1)*2^V+(K+1)^l := by
  rcases h with ⟨x,y,q,v,hpx,hyc,hv,hx,hy,hz⟩|⟨w,hw,hp,hh,hz⟩
  · have hpos : 0<x := by rw [hx]; exact Nat.mul_pos (pow_pos _) (by omega)
    have hxb := low_code_bound (V:=V) (K:=K) hpos (by omega)
    omega
  · have hb := encode_bound (base:=K+1) (by omega) (fun v hv => Nat.lt_succ_of_le (path_val_bound hp hc v hv))
    rw [hw] at hb
    omega

theorem block_code_ne {K V l p c p' c' z z' : Nat}
    (h : BlockCode K V l p c z) (h' : BlockCode K V l p' c' z')
    (hp : p<p') (horder : c≤p') (hc : c<2^(K+1)) (hc' : c'<2^(K+1))
    (hweight : K+1≤l*(V+1)) : z≠z' := by
  rcases h with ⟨x,y,q,v,hpx,hyc,hv,hx,hy,hz⟩|⟨w,hw,hpath,hh,hz⟩
  · have hpos : 0<x := by rw [hx]; exact Nat.mul_pos (pow_pos _) (by omega)
    have hxb := low_code_bound (V:=V) (K:=K) hpos (by omega)
    rcases h' with ⟨x',y',q',v',hpx',hyc',hv',hx',hy',hz'⟩|⟨w',hw',hpath',hh',hz'⟩
    · have hpos' : 0<x' := by rw [hx']; exact Nat.mul_pos (pow_pos _) (by omega)
      have hg := low_gain hv hx hy
      rw [hz,hz']
      exact low_code_ne hpos hpos' (by omega)
    · omega
  · rcases h' with ⟨x',y',q',v',hpx',hyc',hv',hx',hy',hz'⟩|⟨w',hw',hpath',hh',hz'⟩
    · have hpos' : 0<x' := by rw [hx']; exact Nat.mul_pos (pow_pos _) (by omega)
      have hxb' := low_code_bound (V:=V) (K:=K) hpos' (by omega)
      omega
    · intro he
      have henc : encode (K+1) w=encode (K+1) w' := by omega
      have hword := encode_inj (by omega) (hw.trans hw'.symm)
        (fun v hv => Nat.lt_succ_of_le (path_val_bound hpath hc v hv))
        (fun v hv => Nat.lt_succ_of_le (path_val_bound hpath' hc' v hv)) henc
      subst w'
      have hS := weight_lower hh
      rw [hw] at hS
      have hsep := same_word_separation hpath hpath' (show K+1≤S w by omega) hp
      have hpp := path_nondecreasing hpath'
      omega

theorem finite_prefix_bound (f : Nat → Nat) (n K V l : Nat) (h : Prefix f n)
    (hT : f n<2^(K+1)) (hl : 0<l) (hweight : K+1≤l*(V+1)) :
    n < l*((K+1)*2^V+(K+1)^l+1) := by
  classical
  let m := n/l
  let M := (K+1)*2^V+(K+1)^l
  have hmn : l*m≤n := Nat.mul_div_le n l
  have hend : ∀ i : Fin m, l*i.val+l≤n := by
    intro i
    have hm := Nat.mul_le_mul_left l (show i.val+1≤m by omega)
    rw [Nat.mul_add,Nat.mul_one] at hm
    omega
  have hex : ∀ i : Fin m, ∃ z, BlockCode K V l (f (l*i.val)) (f (l*i.val+l)) z := by
    intro i
    obtain ⟨w,hw,hp⟩ := prefix_path f n h (l*i.val) l (hend i)
    exact block_code_exists hw hp
  let code : Fin m → Nat := fun i => Classical.choose (hex i)
  have hcode : ∀ i : Fin m, BlockCode K V l (f (l*i.val)) (f (l*i.val+l)) (code i) := fun i => Classical.choose_spec (hex i)
  have hcb : ∀ i : Fin m, f (l*i.val+l)<2^(K+1) := fun i => Nat.lt_of_le_of_lt (prefix_mono f n h (hend i) (Nat.le_refl n)) hT
  have hb : ∀ i, code i<M := fun i => block_code_bound (hcode i) (hcb i)
  have hne : ∀ i j : Fin m, i.val<j.val → code i≠code j := by
    intro i j hij
    have hstart := Nat.mul_lt_mul_of_pos_left hij hl
    have horder := Nat.mul_le_mul_left l (show i.val+1≤j.val by omega)
    rw [Nat.mul_add,Nat.mul_one] at horder
    have hjend := hend j
    exact block_code_ne (hcode i) (hcode j)
      (prefix_strict f n h hstart (by omega))
      (prefix_mono f n h horder (by omega)) (hcb i) (hcb j) hweight
  have hcnt := finite_count m M code hb hne
  have hdiv : n/l < M+1 := by omega
  have ht := (Nat.div_lt_iff_lt_mul hl).mp hdiv
  simpa [M,Nat.mul_comm] using ht

def threshold (K : Nat) : Nat := Nat.sqrt ((K+1)*(Nat.log2 (K+1)+1))+1
def blockLen (K V : Nat) : Nat := (K+1+V)/(V+1)
def targetFuel (T : Nat) : Nat :=
  let K := Nat.log2 T
  let V := threshold K
  let l := blockLen K V
  l*((K+1)*2^V+(K+1)^l+1)

theorem blockLen_pos (K V : Nat) : 0<blockLen K V := by
  unfold blockLen
  have h := (Nat.le_div_iff_mul_le (show 0<V+1 by omega)).mpr
    (show 1*(V+1)≤K+1+V by omega)
  omega

theorem blockLen_weight (K V : Nat) : K+1≤blockLen K V*(V+1) := by
  unfold blockLen
  have hd := Nat.div_add_mod (K+1+V) (V+1)
  have hm := Nat.mod_lt (K+1+V) (show 0<V+1 by omega)
  rw [Nat.mul_comm (V+1)] at hd
  omega

theorem target_fuel_bound (f : Nat → Nat) (n T : Nat) (h : Prefix f n)
    (hpos : 0<T) (hT : f n≤T) : n<targetFuel T := by
  unfold targetFuel
  let K := Nat.log2 T
  let V := threshold K
  exact finite_prefix_bound f n K V (blockLen K V) h
    (Nat.lt_of_le_of_lt hT (log_band hpos).2) (blockLen_pos K V) (blockLen_weight K V)

#print axioms finite_prefix_bound
#print axioms target_fuel_bound
end NeedleSubexp
