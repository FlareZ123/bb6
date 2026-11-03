import Std
namespace A38Mixed96

def normX (a c : Nat) : Nat := (a + 96 - ((c - 2) % 96)) % 96
def normY (k c : Nat) : Nat := (k + ((c - 2) % 96)) % 96

end A38Mixed96
