// Reproduce the p=37,79,101 second-level forced-residue tables.
"use strict";
function mod(a,m){a%=m;return a<0n?a+m:a;}
function powmod(a,e,m){let r=1n;a=mod(a,m);while(e>0n){if(e&1n)r=r*a%m;a=a*a%m;e>>=1n;}return r;}
function gcd(a,b){while(b){[a,b]=[b,a%b]}return a;}
function lcm(a,b){return a/gcd(a,b)*b;}
function mm(X,Y,m){return [
  [mod(X[0][0]*Y[0][0]+X[0][1]*Y[1][0],m),mod(X[0][0]*Y[0][1]+X[0][1]*Y[1][1],m)],
  [mod(X[1][0]*Y[0][0]+X[1][1]*Y[1][0],m),mod(X[1][0]*Y[0][1]+X[1][1]*Y[1][1],m)]
];}
function mp(X,e,m){let R=[[1n,0n],[0n,1n]];while(e>0n){if(e&1n)R=mm(R,X,m);X=mm(X,X,m);e>>=1n;}return R;}
function orderAndExponent(p){let o=1;while(powmod(2n,BigInt(o),BigInt(p))!==1n)o++;for(let e=0;e<o;e++)if(powmod(2n,BigInt(e),BigInt(p))===BigInt(p-3))return {o,e};throw new Error("no exponent");}
function Aat(j,p,M,lam){
 const r=BigInt(110*j+50),x=powmod(9n,r,2n*lam),a=((x+5n)/2n)%lam;
 return powmod(2n,a,M);
}
const specs=[
 {p:37,T:9,APeriod:1,As:[1053],expected:[14,36,7,13,10,4,31,12,10]},
 {p:79,T:39,APeriod:3,As:[1438,4078,3363],expected:[74,37,5,47,56,12,31,49,34,63,19,32,67,42,67,4,37,59,44,22,15,5,63,13,42,53,35,64,16,42,41,73,18,22,60,63,78,55,29]},
 {p:101,T:5,APeriod:1,As:[8],expected:[80,90,73,38,18]},
];
for(const {p,T,APeriod,As,expected} of specs){
 const M=55n*BigInt(p),lam=BigInt(lcm(lcm(4,10),p-1));
 const {o,e}=orderAndExponent(p),bias=mod(3n*powmod(2n,BigInt(e-1),BigInt(p))+3n,BigInt(p));
 const rows=[];
 for(let j=0;j<T;j++){
  const r=BigInt(110*j+50),x=powmod(9n,r,2n*lam),a=((x+5n)/2n)%lam,A=powmod(2n,a,M);
  const mat=[[A*A%M,mod(A-3n,M)],[0n,9n%M]];
  const P=mp(mat,r,M)[0][1],num=mod(8n*A*P+25n,M);
  if(num%55n!==0n)throw new Error("division by 55 failed");
  rows.push(Number(mod(num/55n-bias,BigInt(p))));
}
 if(rows.some((x,i)=>x!==expected[i]))throw new Error("forced-residue table mismatch for p="+p);
 const unique=[...new Set(Array.from({length:T},(_,j)=>Aat(j,p,M,lam).toString()))];
 for(let j=0;j<T;j++){
  if(Aat(j+T,p,M,lam)!==Aat(j,p,M,lam))throw new Error("A period-T check failed for p="+p);
  if(Aat(j+APeriod,p,M,lam)!==Aat(j,p,M,lam))throw new Error("A-cycle check failed for p="+p);
 }
 if(unique.length!==As.length||unique.some((x,i)=>x!==String(As[i])))throw new Error("A-cycle mismatch for p="+p);
 for(const A0 of As){
  const A=BigInt(A0),mat=[[A*A%M,mod(A-3n,M)],[0n,9n%M]];
  const I=mp(mat,110n*BigInt(T),M);
  if(I[0][0]!==1n||I[0][1]!==0n||I[1][0]!==0n||I[1][1]!==1n)throw new Error("period matrix mismatch for p="+p);
 }
 console.log("p =",p,"forced =",rows.join(","));
}
