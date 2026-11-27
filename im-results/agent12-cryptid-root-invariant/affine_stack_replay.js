// Exact source-rule replay for first-coordinate pair stacks of cryptid #85.
// Source: google-deepmind/cryptids@3647718b5df22e1a61462dec0376bd204526285a,
// BusyBeaver/BB6/Accelerations/M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean.
// Affine acceleration is experimental, not a Lean theorem.
function model() {
const rle=a=>{let s=[];for(let x of a){x=BigInt(x);if(s.length&&s.at(-1)[0]===x)s.at(-1)[1]++;else s.push([x,1n])}return s};
const clone=s=>({q:s.q,L:s.L.map(x=>x.slice()),R:s.R.map(x=>x.slice()),K:s.K.map(x=>x.slice())});
function advance(s,guards=null){
 s=clone(s);let {L,R,K}=s;let q=s.q,cost=0n,halt=false;
 const cmp=(a,b)=>{let d=a-b;guards?.push(d);return d<0n?-1:d>0n?1:0};
 const head=a=>{if(!a.length)throw Error("empty head: "+JSON.stringify(s,(_,v)=>typeof v==="bigint"?String(v):v));return a[0][0]},count=a=>a[0][1],empty=a=>!a.length;
 function push(a,v,c=1n){if(cmp(c,0n)===0)return;if(c<0n)throw Error("negative run");if(a.length&&cmp(head(a),v)===0)a[0][1]+=c;else a.unshift([v,c])}
 function pop(a){let v=head(a);if(cmp(count(a),1n)===0)a.shift();else a[0][1]--;return v}
 function bump(a,n){if(empty(a))push(a,n-1n);else {let v=pop(a);push(a,v+n)}}
 function set(v,c){s.q=v;cost=c}
 function token(v){K.splice(0,K.length,...rle([v,0]))}
 if(q==="CR"){
  if(empty(L)){push(L,0n);bump(R,1n);set("EL",2n)}
  else if(cmp(head(L),0n)===0){let n=count(L);L.shift();bump(R,2n*n);set("CR",2n*n)}
  else if(cmp(head(L),1n)===0){pop(L);if(empty(L)){push(L,0n);bump(R,3n);push(R,0n);set("EL",6n)}
   else {let b=pop(L);if(cmp(b,0n)===0){bump(R,3n);push(R,0n);set("CR",5n)}
    else if(cmp(b,1n)===0){bump(L,1n);push(R,0n);push(R,1n);set("EL",16n)}
    else{push(L,b-2n);push(R,0n);push(R,1n);set("DR",15n)}}}
  else{set("HALT",2n);halt=true}}
 else if(q==="EL"){
  if(empty(R)){push(R,0n);set("CR",1n)}
  else if(cmp(head(R),0n)===0){let n=count(R);R.shift();push(L,0n,n);set("EL",2n*n)}
  else{let v=pop(R);push(R,v-1n);set("DL",1n)}}
 else if(q==="DL"){
  if(empty(R)){push(R,2n);set("CR",4n)}
  else {let v=pop(R);if(cmp(v,0n)===0){bump(L,1n);push(L,0n);set("EL",6n)}
   else if(cmp(v,1n)===0){token(2);set("tDR",4n)}
   else{push(R,v-2n);push(R,1n);set("DR",4n)}}}
 else if(q==="DR"){
  if(empty(L)){push(L,0n);set("EL",1n)}
  else if(empty(R)){let v=pop(L);if(cmp(v,0n)===0){bump(L,1n);push(R,0n);set("EL",4n)}else{push(L,v-1n);push(R,0n);set("DR",3n)}}
  else if(cmp(head(R),0n)===0){pop(R);let v=pop(L);if(cmp(v,0n)===0){token(2);set("tDR",4n)}else{push(L,v-1n);token(1);set("tCR",3n)}}
  else if(cmp(head(L),0n)===0){let n=count(L);L.shift();let v=pop(R);push(R,v-1n);push(R,0n,n-1n);push(R,1n);set("DR",4n*n)}
  else{let v=pop(L),w=pop(R);push(L,v-1n);push(R,w-1n);push(R,0n);set("CR",3n)}}
 else if(q==="tDR"){
  if(cmp(head(K),2n)!==0)throw Error("tDR head");pop(K);
  if(empty(L)){push(L,1n);push(L,0n);set("tEL",8n)}
  else if(cmp(head(L),0n)===0){let n=count(L);L.shift();push(K,1n,n);push(K,2n);set("tDR",4n*n)}
  else{let v=pop(L);if(cmp(v,1n)===0&&empty(L)){push(K,1n);push(L,1n);push(L,0n,3n);set("tEL",28n)}else{push(K,1n,2n);push(L,v-1n);set("tCR",3n)}}}
 else if(q==="tCR"){
  let k=pop(K);
  if(empty(L)){if(cmp(k,1n)===0){push(L,1n);push(L,0n);set("tEL",9n)}else{if(cmp(k,2n)<0)throw Error("tCR head");push(K,k-2n);push(L,1n);push(L,0n,2n);set("tEL",21n)}}
  else if(cmp(head(L),0n)===0){let n=count(L);L.shift();push(K,k+2n*n);set("tCR",2n*n)}
  else if(cmp(head(L),1n)===0){pop(L);if(empty(L)){push(K,k);push(L,1n);push(L,0n,3n);set("tEL",33n)}
   else{let v=pop(L);if(cmp(v,0n)===0){push(K,k+3n);push(K,1n);set("tCR",5n)}
    else if(cmp(v,1n)===0){push(K,k);if(empty(L)){push(L,1n);push(L,0n,2n)}else{let w=pop(L);push(L,w+2n);push(L,0n,2n)}set("tEL",25n)}
    else{push(K,k);push(K,1n);push(K,2n);push(L,v-2n);set("tDR",15n)}}}
  else{set("HALT",2n);halt=true}}
 else if(q==="tEL"){
  let k=head(K);
  if(cmp(k,0n)===0){pop(K);if(empty(K)){bump(R,1n);set("CR",1n)}else{bump(K,1n);set("tCR",1n)}}
  else if(cmp(k,1n)===0){let n=count(K);K.shift();push(L,0n,n);set("tEL",2n*n)}
  else if(cmp(k,2n)===0){pop(K);if(cmp(pop(L),0n)!==0)throw Error("tEL2 L");push(L,1n);push(L,0n);set("tEL",7n)}
  else{pop(K);push(K,k-3n);push(K,2n);set("tDR",5n)}}
 else throw Error("bad q "+q);
 return {s,cost,halt}
}
function sig(s){return s.q+"|"+["L","R","K"].map(k=>s[k].map(([v,c])=>`${v<3n?v:"+"}:${c===1n?1:"+"}`).join(",")).join("|")}
function flat(s){return ["L","R","K"].flatMap(k=>s[k].flat())}
function shifted(s,d,k){let t=clone(s),i=0;for(let x of ["L","R","K"])for(let a of t[x])for(let j=0;j<2;j++)a[j]+=k*d[i++];return t}
function same(a,b){return a.q===b.q&&["L","R","K"].every(k=>a[k].length===b[k].length&&a[k].every((x,i)=>x[0]===b[k][i][0]&&x[1]===b[k][i][1]))}
function replay(s,n){let g=[],c=0n;for(let i=0;i<n;i++){let a=advance(s,g);s=a.s;c+=a.cost;if(a.halt)return null}return {s,g,c}}
function affine(prev,current,p){
 let d=flat(current).map((v,i)=>v-flat(prev)[i]);let a=replay(prev,p),b=replay(current,p);if(!a||!b||!same(a.s,current)||!same(b.s,shifted(current,d,1n))||a.g.length!==b.g.length)return null;
 let max=null;
 function bound(v,w){let slope=w-v;if(v===0n)return w===0n;if((v<0n)!==(w<0n)||w===0n)return false;if((v>0n&&slope<0n)||(v<0n&&slope>0n)){let k=(v>0n?v-1n:-v-1n)/(slope>0n?slope:-slope);max=max===null?k:k<max?k:max}return true}
 for(let i=0;i<a.g.length;i++)if(!bound(a.g[i],b.g[i]))return null;
 let x=flat(prev),y=flat(current);for(let i=0;i<x.length;i++)if(!bound(x[i]+(i%2===0?1n:0n),y[i]+(i%2===0?1n:0n)))return null;
 if(max===null)return {infinite:true,d,p,cost:a.c,deltaCost:b.c-a.c,guards:a.g.length};
 if(max<2n)return null;
 return {s:shifted(current,d,max),cost:max*a.c+(b.c-a.c)*max*(max+1n)/2n,cycles:max,p,d,guards:a.g.length}
}
function run(s,t,budget=10000,ms=6000){let i=0,jump=0,skipped=0n,history=new Map(),records=[],start=Date.now();while(i<budget&&Date.now()-start<ms){let key=sig(s),old=history.get(key);if(old&&i-old.i<=80){let a;try{a=affine(old.s,s,i-old.i)}catch(e){a=null}if(a){if(a.infinite)return {s,t,i,jump,skipped,infinite:a,records};if(jump<20)records.push({q:s.q,t,period:a.p,cycles:a.cycles,cost:a.cost});s=a.s;t+=a.cost;skipped+=BigInt(a.p)*a.cycles;jump++;history.clear();continue}}history.set(key,{s,i});let a;try{a=advance(s)}catch(e){return {s,t,i,jump,skipped,error:String(e),records}}s=a.s;t+=a.cost;i++;if(a.halt)return {s,t,i,jump,skipped,halt:true,records};if(i%1000===0&&history.size>5000)history.clear()}return {s,t,i,jump,skipped,records}}
return {rle,advance,run,affine,same,clone,shifted}
}
module.exports=model;
if(require.main===module){const m=model(),seed=process.argv[2]==='85'?{q:'CR',L:m.rle([0,0]),R:m.rle([2]),K:[]}:{q:'DR',L:m.rle([0,0]),R:m.rle([1]),K:[]};const a=m.run(seed,process.argv[2]==='85'?11n:7n,Number(process.argv[3]||100000),Number(process.argv[4]||60000));console.log(JSON.stringify(a,(_,v)=>typeof v==='bigint'?String(v):v));}
