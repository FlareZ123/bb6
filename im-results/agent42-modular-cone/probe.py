from functools import lru_cache

def canon(b,x,y):
    p=1<<b
    return x%p,y%p

@lru_cache(maxsize=1000000)
def excluded(b,x,y):
    if b<2:return False
    s=x+y
    if y%2 and s%4 in (1,2):return True
    o=s%2;q=s+o
    if q==0:return False
    v=(q&-q).bit_length()-1
    if v>=b:return False
    if y%2==0 and not excluded(b-1,*canon(b-1,s-2,(y-2)//2)):return False
    for n in range((x+1+o)%2,v-1,2):
        d=1<<(n+1);a=q//d-2-o;k=(x+2*y-a-7-3*n)//2
        if d*(a+2+o)!=q or 2*k+a+7+3*n!=x+2*y:return False
        if not excluded(b-n-2,*canon(b-n-2,a,k)):return False
    return True

def stop(j,m,b):return excluded(b,*canon(b,2*j+1,-j-3*m-4))
def stop_bits(j,m,cap=32):
    # One extra bit is available for the unified high family j>=2.
    return min(cap, 2*m+(2 if j>=2 else 1))

def stop_auto(j,m,cap=32):
    return excluded(stop_bits(j,m,cap),*canon(stop_bits(j,m,cap),2*j+1,-j-3*m-4))

def stop8(j,m):
    return excluded(8,*canon(8,2*j+1,-j-3*m-4))
if __name__=='__main__':
    print('cap, low rejected/tested, old high rejected/tested, adaptive high rejected/tested, adaptive outside j>3m+1 rejected/tested')
    for cap in [4,8,12,16,24,32]:
        low=sum(stop(0,m,min(2*m+1,cap)) for m in range(1024))
        hi=[(j,m) for j in range(1,128) for m in range(1,128)]
        out=[(j,m) for j,m in hi if j>3*m+1]
        old_high=sum(stop(j,m,min(2*m+1,cap)) for j,m in hi)
        high=sum(stop_auto(j,m,cap) for j,m in hi)
        outside=sum(stop_auto(j,m,cap) for j,m in out)
        print(cap,low,1024,old_high,len(hi),high,len(hi),outside,len(out),excluded.cache_info())
    print('low unresolved m<100:',[m for m in range(100) if not stop(0,m,2*m+1)])
    fixed8=sum(stop8(j,m) for j in range(256) for m in range(256))
    print('fixed b=8 accepted residue pairs modulo 256:',fixed8,'/',256*256)
