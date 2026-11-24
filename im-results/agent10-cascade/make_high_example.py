import sys
n=int(sys.argv[1]) if len(sys.argv)>1 else 10000
h,k=2,0
w=[]
for _ in range(n):
    assert h+k+4 != 4<<k
    z=2*h+5+(16<<k)+2*k+5
    v=(z&-z).bit_length()-1
    y=(z>>v)*3**(v-1)
    assert y%2==1
    h=(y-5)//2
    j=k
    while h+k+5>=8<<k:k+=1
    assert 4<<k<=h+k+4 and h+k+5<8<<k
    w.append((v-1,k-j))
def tree(l,r):
    if l==r:return '.empty'
    if r-l==1:return f'.atom {w[l][0]} {w[l][1]}'
    m=(l+r)//2
    return f'.branch ({tree(l,m)}) ({tree(m,r)})'
sys.set_int_max_str_digits(0)
print('import HighWordCertificate\nopen CascadePeriodic\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0')
print('def sampleCert : HighCert :=',tree(0,n))
print(f'theorem sampleChecked : checkHighBlock 2 0 sampleCert = some ({n},{h}) := by decide +kernel')
print(f'theorem samplePath : ResetPath {n} 2 {h} := checkHighBlock_sound _ _ _ _ _ sampleChecked')
print('#print axioms samplePath')
