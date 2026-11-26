import Raw11ExtraFamilyCycle
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Raw11ExtraFamily
open BB6Coverage
open Root56 (Side z push c right left alt10)
open Raw11ExtraSweep (FC embed fr fl fblank side)

def fstep (e : Bool) (f : Move) : FC → Option FC
  | (4,l,true,r) => some (fr 5 l e r)
  | (5,l,false,r) => some (if f.right then fr f.next.val l f.write r else fl f.next.val l f.write r)
  | s => Raw11ExtraSweep.fstep false s

theorem fstep_sound (e : Bool) (f : Move) (s : FC) : (fstep e f s).map embed = step e f (embed s) := by
  rcases s with ⟨q,l,b,r⟩
  rcases q with _|_|_|_|_|_|q <;> cases b <;> simp [fstep,step,embed,Root56.c,Raw11ExtraSweep.fstep,Raw11ExtraSweep.step,fr,fl,right,left,side]
  split <;> simp [side]

def frun (e : Bool) (f : Move) : Nat → FC → Option FC
  | 0,s => some s
  | n+1,s => (fstep e f s).bind (frun e f n)

theorem frun_sound (e : Bool) (f : Move) (n : Nat) (s : FC) : (frun e f n s).map embed = run e f n (embed s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [frun,run,← fstep_sound]
    cases h : fstep e f s with
    | none => rfl
    | some t => exact ih t

theorem frun_add (e : Bool) (f : Move) (n m : Nat) (s : FC) : frun e f (n+m) s = (frun e f n s).bind (frun e f m) := by
  induction n generalizing s with
  | zero => simp [frun]
  | succ n ih =>
    rw [Nat.succ_add]; simp only [frun]
    cases h : fstep e f s with
    | none => rfl
    | some t => exact ih t

def move_a : Move := ⟨false,true,1⟩
def cfg_a_0 : FC := (1,[false,true,false,true],false,[true,false,false,true,false,true,false,false,true,false,true,false,true,false,true,false,true,false,false,true,true,false,false,true])
def cfg_a_1 : FC := (0,[false,true,false,true,false,true,false,true,false,true],true,[true,false,true,false,true,false,true,false,true,false,false,true,false,true,true,false,true,false,false,true,true,false,false,true])
def cfg_a_2 : FC := (4,[false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],false,[true,false,false,true,true,false,false,true,true,false,false,true])
def cfg_a_3 : FC := (1,[false,true,false,true],false,[true,false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,false,false,true,true,false,false,true])
def cfg_a_4 : FC := (0,[false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],false,[true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,false,true,true,false,false,true])
def cfg_a_5 : FC := (1,[true,false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],true,[false,true,false,true,false,false,true,false,true,true,true,false,false,true])
def cfg_a_6 : FC := (3,[false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],true,[false,false,true,false,false,true,false,true,true,false,false,true])
def cfg_a_7 : FC := (1,[true,false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],true,[false,true,false,true,false,true,false,false,true,false,true,false,false,true])
def cfg_a_8 : FC := (3,[false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],true,[false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,false,true])
def cfg_a_9 : FC := (1,[true,false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],true,[false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true])
def cfg_a_10 : FC := (0,[],false,[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true])
theorem seg_a_0 : frun false move_a 256 fblank = some cfg_a_0 := by decide +kernel
theorem seg_a_1 : frun false move_a 256 cfg_a_0 = some cfg_a_1 := by decide +kernel
theorem join_a_1 : frun false move_a 512 fblank = some cfg_a_1 := by
  rw [show 512 = 256+256 by decide,frun_add, seg_a_0,Option.bind_some,seg_a_1]
theorem seg_a_2 : frun false move_a 256 cfg_a_1 = some cfg_a_2 := by decide +kernel
theorem join_a_2 : frun false move_a 768 fblank = some cfg_a_2 := by
  rw [show 768 = 512+256 by decide,frun_add, join_a_1,Option.bind_some,seg_a_2]
theorem seg_a_3 : frun false move_a 256 cfg_a_2 = some cfg_a_3 := by decide +kernel
theorem join_a_3 : frun false move_a 1024 fblank = some cfg_a_3 := by
  rw [show 1024 = 768+256 by decide,frun_add, join_a_2,Option.bind_some,seg_a_3]
theorem seg_a_4 : frun false move_a 256 cfg_a_3 = some cfg_a_4 := by decide +kernel
theorem join_a_4 : frun false move_a 1280 fblank = some cfg_a_4 := by
  rw [show 1280 = 1024+256 by decide,frun_add, join_a_3,Option.bind_some,seg_a_4]
theorem seg_a_5 : frun false move_a 256 cfg_a_4 = some cfg_a_5 := by decide +kernel
theorem join_a_5 : frun false move_a 1536 fblank = some cfg_a_5 := by
  rw [show 1536 = 1280+256 by decide,frun_add, join_a_4,Option.bind_some,seg_a_5]
theorem seg_a_6 : frun false move_a 256 cfg_a_5 = some cfg_a_6 := by decide +kernel
theorem join_a_6 : frun false move_a 1792 fblank = some cfg_a_6 := by
  rw [show 1792 = 1536+256 by decide,frun_add, join_a_5,Option.bind_some,seg_a_6]
theorem seg_a_7 : frun false move_a 256 cfg_a_6 = some cfg_a_7 := by decide +kernel
theorem join_a_7 : frun false move_a 2048 fblank = some cfg_a_7 := by
  rw [show 2048 = 1792+256 by decide,frun_add, join_a_6,Option.bind_some,seg_a_7]
theorem seg_a_8 : frun false move_a 256 cfg_a_7 = some cfg_a_8 := by decide +kernel
theorem join_a_8 : frun false move_a 2304 fblank = some cfg_a_8 := by
  rw [show 2304 = 2048+256 by decide,frun_add, join_a_7,Option.bind_some,seg_a_8]
theorem seg_a_9 : frun false move_a 256 cfg_a_8 = some cfg_a_9 := by decide +kernel
theorem join_a_9 : frun false move_a 2560 fblank = some cfg_a_9 := by
  rw [show 2560 = 2304+256 by decide,frun_add, join_a_8,Option.bind_some,seg_a_9]
theorem seg_a_10 : frun false move_a 256 cfg_a_9 = some cfg_a_10 := by decide +kernel
theorem join_a_10 : frun false move_a 2816 fblank = some cfg_a_10 := by
  rw [show 2816 = 2560+256 by decide,frun_add, join_a_9,Option.bind_some,seg_a_10]
theorem seed_a : run false move_a 2816 Root56.blank = some (sec 31 Raw11ExtraSweep.tail) := by
  have hs := frun_sound false move_a 2816 fblank
  rw [join_a_10] at hs
  have he : embed cfg_a_10 = sec 31 Raw11ExtraSweep.tail := by rfl
  rw [Option.map_some,he] at hs
  exact hs.symm
theorem never_a : ∀ n, run false move_a n Root56.blank ≠ none := by
  apply never_of_return false move_a Raw11ExtraSweep.tail 30 2 2816 seed_a
  intro n
  exact ⟨10*(n+1)+29,by omega,stableAdvance false move_a n⟩

def move_b : Move := ⟨false,true,4⟩
def cfg_b_0 : FC := (1,[false,false,false,false,false,true,true,false,false,true,false,true,false,true,false,true,false,true,false,true],false,[true,false,false,true])
def cfg_b_1 : FC := (3,[true,false,true,false,true,false,true,false,true],false,[false,true,false,true,false,true,false,true,false,false,true,false,true,true,false,true,false,true,false,true,false,false,true,true,false,false,true])
def cfg_b_2 : FC := (3,[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],false,[false,true,false,true,false,true,false,false,true,false,true,true,false,true,false,true,false,false,true,true,false,false,true])
def cfg_b_3 : FC := (0,[false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],false,[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,false,true,false,true,false,false,true,true,false,false,true])
def cfg_b_4 : FC := (3,[false,true,true,false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],false,[false,true,false,true,false,false,true,true,false,false,true])
def cfg_b_5 : FC := (3,[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],false,[false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true,false,false,true,true,false,false,true])
def cfg_b_6 : FC := (0,[false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],true,[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,false,false,true,true,false,false,true])
def cfg_b_7 : FC := (3,[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],false,[false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,false,true,true,false,false,true])
def cfg_b_8 : FC := (1,[false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],true,[true,false,true,false,false,true,false,true,true,true,false,false,true])
def cfg_b_9 : FC := (2,[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],true,[false,false,true,false,true,false,false,true,false,true,true,true,false,false,true])
def cfg_b_10 : FC := (1,[true,false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],true,[false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true,false,false,true])
def cfg_b_11 : FC := (3,[false,false,true,false,true,false,true,false,true,false,true],true,[false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,false,false,true])
def cfg_b_12 : FC := (3,[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],false,[false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,false,true])
def cfg_b_13 : FC := (1,[false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],false,[true,false,false,true,false,false,true,false,true,false,true])
def cfg_b_14 : FC := (2,[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],true,[false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true])
def cfg_b_15 : FC := (3,[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],false,[false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true])
def cfg_b_16 : FC := (0,[],false,[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true])
theorem seg_b_0 : frun false move_b 256 fblank = some cfg_b_0 := by decide +kernel
theorem seg_b_1 : frun false move_b 256 cfg_b_0 = some cfg_b_1 := by decide +kernel
theorem join_b_1 : frun false move_b 512 fblank = some cfg_b_1 := by
  rw [show 512 = 256+256 by decide,frun_add, seg_b_0,Option.bind_some,seg_b_1]
theorem seg_b_2 : frun false move_b 256 cfg_b_1 = some cfg_b_2 := by decide +kernel
theorem join_b_2 : frun false move_b 768 fblank = some cfg_b_2 := by
  rw [show 768 = 512+256 by decide,frun_add, join_b_1,Option.bind_some,seg_b_2]
theorem seg_b_3 : frun false move_b 256 cfg_b_2 = some cfg_b_3 := by decide +kernel
theorem join_b_3 : frun false move_b 1024 fblank = some cfg_b_3 := by
  rw [show 1024 = 768+256 by decide,frun_add, join_b_2,Option.bind_some,seg_b_3]
theorem seg_b_4 : frun false move_b 256 cfg_b_3 = some cfg_b_4 := by decide +kernel
theorem join_b_4 : frun false move_b 1280 fblank = some cfg_b_4 := by
  rw [show 1280 = 1024+256 by decide,frun_add, join_b_3,Option.bind_some,seg_b_4]
theorem seg_b_5 : frun false move_b 256 cfg_b_4 = some cfg_b_5 := by decide +kernel
theorem join_b_5 : frun false move_b 1536 fblank = some cfg_b_5 := by
  rw [show 1536 = 1280+256 by decide,frun_add, join_b_4,Option.bind_some,seg_b_5]
theorem seg_b_6 : frun false move_b 256 cfg_b_5 = some cfg_b_6 := by decide +kernel
theorem join_b_6 : frun false move_b 1792 fblank = some cfg_b_6 := by
  rw [show 1792 = 1536+256 by decide,frun_add, join_b_5,Option.bind_some,seg_b_6]
theorem seg_b_7 : frun false move_b 256 cfg_b_6 = some cfg_b_7 := by decide +kernel
theorem join_b_7 : frun false move_b 2048 fblank = some cfg_b_7 := by
  rw [show 2048 = 1792+256 by decide,frun_add, join_b_6,Option.bind_some,seg_b_7]
theorem seg_b_8 : frun false move_b 256 cfg_b_7 = some cfg_b_8 := by decide +kernel
theorem join_b_8 : frun false move_b 2304 fblank = some cfg_b_8 := by
  rw [show 2304 = 2048+256 by decide,frun_add, join_b_7,Option.bind_some,seg_b_8]
theorem seg_b_9 : frun false move_b 256 cfg_b_8 = some cfg_b_9 := by decide +kernel
theorem join_b_9 : frun false move_b 2560 fblank = some cfg_b_9 := by
  rw [show 2560 = 2304+256 by decide,frun_add, join_b_8,Option.bind_some,seg_b_9]
theorem seg_b_10 : frun false move_b 256 cfg_b_9 = some cfg_b_10 := by decide +kernel
theorem join_b_10 : frun false move_b 2816 fblank = some cfg_b_10 := by
  rw [show 2816 = 2560+256 by decide,frun_add, join_b_9,Option.bind_some,seg_b_10]
theorem seg_b_11 : frun false move_b 256 cfg_b_10 = some cfg_b_11 := by decide +kernel
theorem join_b_11 : frun false move_b 3072 fblank = some cfg_b_11 := by
  rw [show 3072 = 2816+256 by decide,frun_add, join_b_10,Option.bind_some,seg_b_11]
theorem seg_b_12 : frun false move_b 256 cfg_b_11 = some cfg_b_12 := by decide +kernel
theorem join_b_12 : frun false move_b 3328 fblank = some cfg_b_12 := by
  rw [show 3328 = 3072+256 by decide,frun_add, join_b_11,Option.bind_some,seg_b_12]
theorem seg_b_13 : frun false move_b 256 cfg_b_12 = some cfg_b_13 := by decide +kernel
theorem join_b_13 : frun false move_b 3584 fblank = some cfg_b_13 := by
  rw [show 3584 = 3328+256 by decide,frun_add, join_b_12,Option.bind_some,seg_b_13]
theorem seg_b_14 : frun false move_b 256 cfg_b_13 = some cfg_b_14 := by decide +kernel
theorem join_b_14 : frun false move_b 3840 fblank = some cfg_b_14 := by
  rw [show 3840 = 3584+256 by decide,frun_add, join_b_13,Option.bind_some,seg_b_14]
theorem seg_b_15 : frun false move_b 256 cfg_b_14 = some cfg_b_15 := by decide +kernel
theorem join_b_15 : frun false move_b 4096 fblank = some cfg_b_15 := by
  rw [show 4096 = 3840+256 by decide,frun_add, join_b_14,Option.bind_some,seg_b_15]
theorem seg_b_16 : frun false move_b 49 cfg_b_15 = some cfg_b_16 := by decide +kernel
theorem join_b_16 : frun false move_b 4145 fblank = some cfg_b_16 := by
  rw [show 4145 = 4096+49 by decide,frun_add, join_b_15,Option.bind_some,seg_b_16]
theorem seed_b : run false move_b 4145 Root56.blank = some (sec 38 Raw11ExtraSweep.tail) := by
  have hs := frun_sound false move_b 4145 fblank
  rw [join_b_16] at hs
  have he : embed cfg_b_16 = sec 38 Raw11ExtraSweep.tail := by rfl
  rw [Option.map_some,he] at hs
  exact hs.symm
theorem never_b : ∀ n, run false move_b n Root56.blank ≠ none := by
  apply never_of_return false move_b Raw11ExtraSweep.tail 37 2 4145 seed_b
  intro n
  exact ⟨10*(n+1)+29,by omega,stableAdvance false move_b n⟩

def move_c : Move := ⟨false,true,1⟩
def cfg_c_0 : FC := (0,[],false,[true,false,true,false,true,false,true,false,false,true,true,false,false,true])
theorem seg_c_0 : frun true move_c 88 fblank = some cfg_c_0 := by decide +kernel
theorem seed_c : run true move_c 88 Root56.blank = some (sec 4 s0) := by
  have hs := frun_sound true move_c 88 fblank
  rw [seg_c_0] at hs
  have he : embed cfg_c_0 = sec 4 s0 := by rfl
  rw [Option.map_some,he] at hs
  exact hs.symm
theorem never_c : ∀ n, run true move_c n Root56.blank ≠ none := by
  apply never_of_return true move_c s0 3 18 88 seed_c
  intro n
  refine ⟨90*(n+1)+1065,by omega,?_⟩
  exact cycle false n

def move_d : Move := ⟨true,true,1⟩
def cfg_d_0 : FC := (0,[],false,[true,false,true,false,true,false,true,false,false,true,true,false,false,true])
theorem seg_d_0 : frun true move_d 88 fblank = some cfg_d_0 := by decide +kernel
theorem seed_d : run true move_d 88 Root56.blank = some (sec 4 s0) := by
  have hs := frun_sound true move_d 88 fblank
  rw [seg_d_0] at hs
  have he : embed cfg_d_0 = sec 4 s0 := by rfl
  rw [Option.map_some,he] at hs
  exact hs.symm
theorem never_d : ∀ n, run true move_d n Root56.blank ≠ none := by
  apply never_of_return true move_d s0 3 18 88 seed_d
  intro n
  refine ⟨90*(n+1)+1047,by omega,?_⟩
  exact cycle true n

def move_e : Move := ⟨false,true,2⟩
def cfg_e_0 : FC := (3,[true,true,false,false,true,false,true,false,true,true,false,true,true,false,false,true,false,true,false,true,false,true,false,true,false,true],false,[])
def cfg_e_1 : FC := (1,[false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],true,[true,false,true,false,false,true,false,true,true,true,false,true,false,true,false,false,true])
def cfg_e_2 : FC := (3,[false,true,true,false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],false,[false,true,false,true,false,true,false,false,true])
def cfg_e_3 : FC := (4,[false,true],false,[false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true,false,true,false,false,true])
def cfg_e_4 : FC := (2,[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],true,[false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,false,true,false,false,true])
def cfg_e_5 : FC := (4,[false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],false,[false,true,false,true,false,true,false,true,false,false,true,false,true,true,false,false,true])
def cfg_e_6 : FC := (0,[false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],false,[true,false,true,false,true,false,false,true,false,true,false,false,true])
def cfg_e_7 : FC := (1,[false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],false,[true,false,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,false,true])
def cfg_e_8 : FC := (2,[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],true,[false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true])
def cfg_e_9 : FC := (0,[],false,[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true])
theorem seg_e_0 : frun true move_e 256 fblank = some cfg_e_0 := by decide +kernel
theorem seg_e_1 : frun true move_e 256 cfg_e_0 = some cfg_e_1 := by decide +kernel
theorem join_e_1 : frun true move_e 512 fblank = some cfg_e_1 := by
  rw [show 512 = 256+256 by decide,frun_add, seg_e_0,Option.bind_some,seg_e_1]
theorem seg_e_2 : frun true move_e 256 cfg_e_1 = some cfg_e_2 := by decide +kernel
theorem join_e_2 : frun true move_e 768 fblank = some cfg_e_2 := by
  rw [show 768 = 512+256 by decide,frun_add, join_e_1,Option.bind_some,seg_e_2]
theorem seg_e_3 : frun true move_e 256 cfg_e_2 = some cfg_e_3 := by decide +kernel
theorem join_e_3 : frun true move_e 1024 fblank = some cfg_e_3 := by
  rw [show 1024 = 768+256 by decide,frun_add, join_e_2,Option.bind_some,seg_e_3]
theorem seg_e_4 : frun true move_e 256 cfg_e_3 = some cfg_e_4 := by decide +kernel
theorem join_e_4 : frun true move_e 1280 fblank = some cfg_e_4 := by
  rw [show 1280 = 1024+256 by decide,frun_add, join_e_3,Option.bind_some,seg_e_4]
theorem seg_e_5 : frun true move_e 256 cfg_e_4 = some cfg_e_5 := by decide +kernel
theorem join_e_5 : frun true move_e 1536 fblank = some cfg_e_5 := by
  rw [show 1536 = 1280+256 by decide,frun_add, join_e_4,Option.bind_some,seg_e_5]
theorem seg_e_6 : frun true move_e 256 cfg_e_5 = some cfg_e_6 := by decide +kernel
theorem join_e_6 : frun true move_e 1792 fblank = some cfg_e_6 := by
  rw [show 1792 = 1536+256 by decide,frun_add, join_e_5,Option.bind_some,seg_e_6]
theorem seg_e_7 : frun true move_e 256 cfg_e_6 = some cfg_e_7 := by decide +kernel
theorem join_e_7 : frun true move_e 2048 fblank = some cfg_e_7 := by
  rw [show 2048 = 1792+256 by decide,frun_add, join_e_6,Option.bind_some,seg_e_7]
theorem seg_e_8 : frun true move_e 256 cfg_e_7 = some cfg_e_8 := by decide +kernel
theorem join_e_8 : frun true move_e 2304 fblank = some cfg_e_8 := by
  rw [show 2304 = 2048+256 by decide,frun_add, join_e_7,Option.bind_some,seg_e_8]
theorem seg_e_9 : frun true move_e 203 cfg_e_8 = some cfg_e_9 := by decide +kernel
theorem join_e_9 : frun true move_e 2507 fblank = some cfg_e_9 := by
  rw [show 2507 = 2304+203 by decide,frun_add, join_e_8,Option.bind_some,seg_e_9]
theorem seed_e : run true move_e 2507 Root56.blank = some (sec 29 Raw11ExtraSweep.tail) := by
  have hs := frun_sound true move_e 2507 fblank
  rw [join_e_9] at hs
  have he : embed cfg_e_9 = sec 29 Raw11ExtraSweep.tail := by rfl
  rw [Option.map_some,he] at hs
  exact hs.symm
theorem never_e : ∀ n, run true move_e n Root56.blank ≠ none := by
  apply never_of_return true move_e Raw11ExtraSweep.tail 28 2 2507 seed_e
  intro n
  exact ⟨10*(n+1)+29,by omega,stableAdvance true move_e n⟩

def move_f : Move := ⟨false,false,3⟩
def cfg_f_0 : FC := (0,[],false,[true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,true,false,true,false,false,true])
def cfg_f_1 : FC := (2,[true,false,true,false,true,false,true,false,true,false,true,false,true],true,[false,false,true,false,true,false,true,false,true,false,false,true,false,true,true,false,false,true])
def cfg_f_2 : FC := (0,[],false,[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,false,true])
def cfg_f_3 : FC := (4,[false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true],false,[false,true,false,true,false,true,false,true,false,false,true,false,true,true])
def cfg_f_4 : FC := (0,[],false,[true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true])
theorem seg_f_0 : frun true move_f 256 fblank = some cfg_f_0 := by decide +kernel
theorem seg_f_1 : frun true move_f 256 cfg_f_0 = some cfg_f_1 := by decide +kernel
theorem join_f_1 : frun true move_f 512 fblank = some cfg_f_1 := by
  rw [show 512 = 256+256 by decide,frun_add, seg_f_0,Option.bind_some,seg_f_1]
theorem seg_f_2 : frun true move_f 256 cfg_f_1 = some cfg_f_2 := by decide +kernel
theorem join_f_2 : frun true move_f 768 fblank = some cfg_f_2 := by
  rw [show 768 = 512+256 by decide,frun_add, join_f_1,Option.bind_some,seg_f_2]
theorem seg_f_3 : frun true move_f 256 cfg_f_2 = some cfg_f_3 := by decide +kernel
theorem join_f_3 : frun true move_f 1024 fblank = some cfg_f_3 := by
  rw [show 1024 = 768+256 by decide,frun_add, join_f_2,Option.bind_some,seg_f_3]
theorem seg_f_4 : frun true move_f 120 cfg_f_3 = some cfg_f_4 := by decide +kernel
theorem join_f_4 : frun true move_f 1144 fblank = some cfg_f_4 := by
  rw [show 1144 = 1024+120 by decide,frun_add, join_f_3,Option.bind_some,seg_f_4]
theorem seed_f : run true move_f 1144 Root56.blank = some (sec 19 Raw11ExtraSweep.tail) := by
  have hs := frun_sound true move_f 1144 fblank
  rw [join_f_4] at hs
  have he : embed cfg_f_4 = sec 19 Raw11ExtraSweep.tail := by rfl
  rw [Option.map_some,he] at hs
  exact hs.symm
theorem never_f : ∀ n, run true move_f n Root56.blank ≠ none := by
  apply never_of_return true move_f Raw11ExtraSweep.tail 18 2 1144 seed_f
  intro n
  exact ⟨10*(n+1)+29,by omega,stableAdvance true move_f n⟩

#print axioms never_a
#print axioms never_b
#print axioms never_c
#print axioms never_d
#print axioms never_e
#print axioms never_f
end Raw11ExtraFamily
