import Lean

namespace QPhaseCounterexample

def K : Nat := 26
def j : Nat := 16
def c : Nat := 59
def p : Nat := 2 ^ K
def X : Nat := 2 ^ (j + 4)

def W : Nat := 80 * p - 22 * K - 23 - 2 * c * X
def hIn : Nat := (W - 45) / 18
def q : Nat := 4 * p + (hIn + K) / 2
def B : Nat := 112 * p - 2 * K - 34 - 18 * q

def dIn : Nat := 64752797
def PIn : Nat := 2 * dIn
def L : Nat := 24
def qPrev : Nat := 124793431
def AIn : Nat := 4 * 2 ^ L + (qPrev + L + 5) / 2

def dOut : Nat := 237750051
def AOut : Nat := 4 * p + (q + K + 5) / 2
def u : Nat := (9 * dOut - 5) / 2

def fatal28 : Nat := 4 * 2 ^ 28 - 28 - 4
def deficit27 : Nat := 8 * 2 ^ 27 + 27 - u

def evenStep27 (x : Nat) : Nat := 4 * 2 ^ 27 + (x + 27) / 2

def iterateEven27 : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => iterateEven27 n (evenStep27 x)

def after15 : Nat := iterateEven27 15 u

example : W = 5244976557 := by decide
example : W = 81 * dIn := by decide
example : W % 27 = 0 := by decide
example : W % 54 = 27 := by decide
example : W % 243 = 162 := by decide
example : hIn = 291387584 := by decide
example : hIn % 3 = 2 := by decide
example : (hIn + K) % 4 = 2 := by decide
example : q = 414129261 := by decide
example : (q + K) % 2 = 1 := by decide
example : B = c * 2 ^ (j + 4) := by decide

example : qPrev + L + 4 >= 4 * 2 ^ L := by decide
example : qPrev + L + 5 < 8 * 2 ^ L := by decide
example : AIn = PIn := by decide
example : PIn = 2 * dIn := by decide
example : dIn % 2 = 1 := by decide
example : hIn = (3 ^ 2 * dIn - 5) / 2 := by decide

example : hIn + K + 4 >= 4 * p := by decide
example : hIn + K + 5 < 8 * p := by decide
example : q + K + 4 >= 4 * p := by decide
example : q + K + 5 < 8 * p := by decide

example : AOut = 2 * dOut := by decide
example : dOut % 2 = 1 := by decide
example : u = 1069875227 := by decide
example : u + 27 + 4 >= 4 * 2 ^ 27 := by decide
example : u + 27 + 5 < 8 * 2 ^ 27 := by decide
example : deficit27 = c * 2 ^ j := by decide
example : fatal28 = 1073741792 := by decide
example : 8 * 2 ^ 27 + 27 - after15 = 118 := by decide
example : after15 + 27 + 4 >= 4 * 2 ^ 27 := by decide
example : after15 + 27 + 5 < 8 * 2 ^ 27 := by decide
example : iterateEven27 16 u = fatal28 := by decide

end QPhaseCounterexample
