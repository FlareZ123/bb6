// Eight-hole D1 sibling candidate scan equivalent to frontier_graft.cpp, with exact BigInt tape and FAR masks.
// Return values must be independently consumed by the Lean checker, never trusted as proof.
const root="1RB1LD1RC---1LA---------------------",graft="1RB1LD1RC---1LA------0LA------------";
const parse=s=>s.match(/.../g).map(v=>v==="---"?-1:12*Number(v[0])+6*Number(v[1]==="R")+v.charCodeAt(2)-65);
const decode=x=>x<0?"---":String(Math.floor(x/12))+(x%12>=6?"R":"L")+String.fromCharCode(65+x%6);
const show=p=>p.map(decode).join("");
function mask(p){let seen=1,todo=1;while(todo){let q=31-Math.clz32(todo&-todo);todo&=todo-1;for(let b=0;b<2;b++){let x=p[2*q+b];if(x<0)return 0;let d=1<<(x%6);todo|=d&~seen;seen|=d}}return seen}
const bits=Array.from({length:2048},(_,i)=>1n<<BigInt(i)),below=bits.map(b=>(b<<1n)-1n),above=bits.map(b=>-b),idx=new Map(bits.slice(0,64).map((b,i)=>[b,i]));
function classify(p,L,P){let q=0,h=1024,t=0n,hs=[],ts=[],prev=[],last=[-1,-1,-1,-1,-1,-1];for(let n=0;n<=L;n++){let s=2*q+Number((t&bits[h])!==0n);if(p[s]<0)return ["last",n,s];let lo=h,hi=h,i=n-1;for(let j=last[q];j>=0&&n-j<=P;j=prev[j]){while(i>=j){lo=Math.min(lo,hs[i]);hi=Math.max(hi,hs[i]);i--}let d=h-hs[j];if(d>=0&&((ts[j]^(t>>BigInt(d)))&above[lo])===0n)return ["cycle",j,n-j,true,lo-1024];if(d<=0&&((ts[j]^(t<<BigInt(-d)))&below[hi])===0n)return ["cycle",j,n-j,false,hi-1024]}if(n===L)break;hs[n]=h;ts[n]=t;prev[n]=last[q];last[q]=n;let a=p[s];t=a>=12?t|bits[h]:t&~bits[h];h+=a%12>=6?1:-1;q=a%6}return null}
function far(p,a,rev){let d=a.length/2,N=6*d+1,H=N-1,halt=bits[H],T=Array(2*N).fill(0n),rules=[];T[H]=T[N+H]=halt;for(let l=0;l<d;l++)for(let q=0;q<6;q++)for(let b=0;b<2;b++){let x=p[2*q+b],i=b*N+6*l+q;if(x<0){T[i]=halt;continue}let w=x/12|0,n=x%6,dir=x%12>=6;if(dir!==rev)T[i]=bits[6*a[2*l+w]+n];else for(let j=0;j<d;j++)for(let e=0;e<2;e++)if(a[2*j+e]===l)rules.push([i,e*N+6*j+n,w*N])}function compose(v,off){let r=0n;while(v){r|=T[off+idx.get(v&-v)];v&=v-1n}return r}for(;;){let cur=1n,seen=0n;while(cur){seen|=cur;if(seen&halt)return false;cur=compose(cur,0)&~seen}let change=false;for(let [dst,src,off] of rules){let x=T[dst]|compose(T[src],off);if(x!==T[dst]){T[dst]=x;change=true}}if(!change)return true}}
function scan(x,bank,known=new Set()){
 let nodes=0,max=0,counts={},mass={},opened=[];
 function inc(o,k,v=1){o[k]=(o[k]||0)+v}
 function solve(p,cut,holes,weight){if(++nodes>2000000)throw Error("node cap");let raw=show(p),t;
 if(raw===graft)t=["graft",raw];else if(known.has(raw))t=["auto",raw];else{let m=mask(p);t=m?["state",m]:classify(p,120,120)||classify(p,1000,256);if(!t){for(let a of bank){for(let rev of [false,true])if(far(p,a,rev)){t=["far",raw,+rev,a.join("")];break}if(t)break}if(!t){let a=classify(p,1000,1000);t=a&&a[0]==="cycle"?a:["open",raw]}}}
 if(t[0]==="last"&&holes>1){let n=t[1],s=t[2];max=Math.max(max,n);inc(counts,"split");inc(mass,"halt",weight*25**(holes-1));let kids=Array(24).fill(null);for(let y=0;y<24;y++){let q=y%6;if(q>cut)continue;let z=p.slice();z[s]=y;kids[y]=solve(z,Math.max(cut,q+1),holes-1,weight*(q===cut?6-cut:1))}return ["split",n,s,kids]}
 inc(counts,t[0]);inc(mass,t[0],weight*25**holes);if(t[0]==="last")max=Math.max(max,t[1]);if(t[0]==="open")opened.push(t[1]);return t}
 if(x%6>4)throw Error("move exceeds cut 4");let p=parse(root);p[7]=x;let tree=solve(p,Math.max(4,x%6+1),7,1);if(Object.values(mass).reduce((a,b)=>a+b,0)!==25**7)throw Error("mass mismatch");
 return {move:decode(x),counts,mass,open:opened,max_query:max,tree,nodes}
}
return {scan,parse,show,far,classify,root,graft};
