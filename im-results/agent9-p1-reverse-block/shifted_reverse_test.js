// Independent scalar recurrence and exact shifted-window stress test.
// node shifted_reverse_test.js
function dw(b,k){let d=0;for(let j=0;j<k;j++)if((b>>j)&1)d+=j*2**j;return d}
function scalar(q,k,z,Y){for(let i=k-1;i>=0;i--){let p=q+i;if(z>=p)return -1;z=(2*z+((Y>>i)&1))%p}return z}
function fast(q,k,z,Y){let F=q+k,M=2**k,X=M*z+Y,b=Math.floor(X/(F-1)),c=X-q*b-dw(b,k);if(b<M&&c>=0&&c<q)return c;let u=b+1;c-=q+2*(u&-u)-2;return u<M&&c>=0&&c<q?c:-1}
let exhaustive=0,expanded=0;
for(let F=3;F<=140;F++)for(let k=1;k<=Math.floor(Math.log2(F-1));k++){let q=F-k;if(q<1)continue;for(let Y=0;Y<2**k;Y++)for(let z=0;z<F;z++){let a=scalar(q,k,z,Y),b=fast(q,k,z,Y);if(a!==b)throw Error(JSON.stringify({F,k,Y,z,a,b}));exhaustive++;if(2**(k+1)>F)expanded++}}
let seed=0x123456789abcdefn;
function rand(m){seed=(6364136223846793005n*seed+1442695040888963407n)&((1n<<64n)-1n);return seed%m}
function dwB(b,k){let d=0n;for(let j=0n;j<k;j++)if(b>>j&1n)d+=j*(1n<<j);return d}
let large=0,expandedLarge=0,gapChecks=0,badOld=0,maxX=0n;
for(let i=0;i<50000;i++){let F=3n+rand(2147483644n),k=BigInt((F-1n).toString(2).length-1);if(k<1n)continue;let q=F-k,M=1n<<k,Y=rand(M),z=rand(F),X=M*z+Y,b=X/(F-1n),c=X-q*b-dwB(b,k),u=b+1n,c1=c-q-2n*(u&-u)+2n;
let got=b<M&&c>=0n&&c<q?c:u<M&&c1>=0n&&c1<q?c1:-1n;
let cur=z;for(let j=k-1n;j>=0n;j--){let clock=q+j;if(cur>=clock){cur=-1n;break}cur=(2n*cur+(Y>>j&1n))%clock}
if(got!==cur)throw Error("large mismatch");
if(u<M){if(dwB(u,k)-dwB(b,k)!==2n*(u&-u)-2n)throw Error("gap");gapChecks++}
if(M*2n>F)expandedLarge++;
if(got>=0n){let B=c>=0n&&c<q?b:u;let o=X/F;if(B>o+1n)badOld++}
large++;if(X>maxX)maxX=X;
}
console.log({exhaustive,expanded,large,expandedLarge,gapChecks,oldTwoCandidateMisses:badOld,maxX:String(maxX)});
