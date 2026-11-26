import Raw11ExtraSweep
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
namespace Raw11ExtraSweep
open Root56 (Side z push hd tl c right left alt10)

def side : List Bool → Side
  | [] => z
  | b::bs => b ::: side bs

@[simp] theorem hd_side (xs : List Bool) : hd (side xs) = xs.headD false := by cases xs <;> rfl
@[simp] theorem tl_side (xs : List Bool) : tl (side xs) = side xs.tail := by cases xs <;> rfl

abbrev FC := Nat × List Bool × Bool × List Bool

def embed : FC → Config
  | (q,l,b,r) => c q (side l) b (side r)

def fr (q : Nat) (l : List Bool) (w : Bool) (r : List Bool) : FC := (q,w::l,r.headD false,r.tail)
def fl (q : Nat) (l : List Bool) (w : Bool) (r : List Bool) : FC := (q,l.tail,l.headD false,w::r)

@[simp] theorem embed_fr (q : Nat) (l : List Bool) (w : Bool) (r : List Bool) : embed (fr q l w r) = right q (side l) w (side r) := by simp [embed,fr,right,side]
@[simp] theorem embed_fl (q : Nat) (l : List Bool) (w : Bool) (r : List Bool) : embed (fl q l w r) = left q (side l) w (side r) := by simp [embed,fl,left,side]

def fstep (v : Bool) : FC → Option FC
  | (0,l,false,r) => some (fr 1 l true r)
  | (0,l,true,r) => some (fr 3 l true r)
  | (1,l,false,r) => some (fr 2 l true r)
  | (1,l,true,r) => some (fl 3 l false r)
  | (2,l,false,r) => some (fl 0 l false r)
  | (2,l,true,r) => some (fr 4 l v r)
  | (3,l,false,r) => some (fl 0 l true r)
  | (3,l,true,r) => some (fl 1 l true r)
  | (4,l,false,r) => some (if v then fl 4 l false r else fr 0 l false r)
  | (4,l,true,r) => some (fr 5 l false r)
  | (5,l,false,r) => some (if v then fr 0 l false r else fl 0 l true r)
  | _ => none

theorem fstep_sound (v : Bool) (s : FC) : (fstep v s).map embed = step v (embed s) := by
  rcases s with ⟨q,l,b,r⟩
  rcases q with _|_|_|_|_|_|q <;> cases b <;> cases v <;> simp [fstep,step,embed,Root56.c,fr,fl,right,left,side]

def frun (v : Bool) : Nat → FC → Option FC
  | 0,s => some s
  | n+1,s => (fstep v s).bind (frun v n)

theorem frun_sound (v : Bool) (n : Nat) (s : FC) : (frun v n s).map embed = run v n (embed s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [frun,run,← fstep_sound]
    cases h : fstep v s with
    | none => rfl
    | some t => exact ih t

def fblank : FC := (0,[],false,[])

def target_no : FC := (0,[],false,[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true])

theorem seed_no : run false 1146 Root56.blank = some (sec 19) := by
  have h : frun false 1146 fblank = some target_no := by decide +kernel
  have hs := frun_sound false 1146 fblank
  rw [h] at hs
  have he : embed target_no = sec 19 := by
    simp only [target_no,embed,side]
    rfl
  rw [Option.map_some,he] at hs
  exact hs.symm

def target_yes : FC := (0,[],false,[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true])

theorem seed_yes : run true 1346 Root56.blank = some (sec 19) := by
  have h : frun true 1346 fblank = some target_yes := by decide +kernel
  have hs := frun_sound true 1346 fblank
  rw [h] at hs
  have he : embed target_yes = sec 19 := by
    simp only [target_yes,embed,side]
    rfl
  rw [Option.map_some,he] at hs
  exact hs.symm

end Raw11ExtraSweep
