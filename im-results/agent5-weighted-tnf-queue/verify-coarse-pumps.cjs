'use strict';
// Exact symbolic fixture replay, same finite-tail transfer mechanism as Agent46AutoPump.
function verify(c){
 const t=c.table.match(/.{3}/g), lit=w=>typeof w==="string", P=w=>lit(w)?w:w[0],B=w=>lit(w)?"":w[1],S=w=>w[2],W=(p,b="",s="")=>b?[p,b,s]:p;
 const head=(w,known)=>P(w)[0]||(!known&&lit(w)?"0":null),drop=w=>P(w)?W(P(w).slice(1),B(w),S(w)):w,push=(w,p)=>W(p+P(w),B(w),S(w));
 function step(z,known=false){let [q,l,r]=z,a=head(l,known);if(a===null)throw Error("unknown l");const x=t[2*q+Number(a)];if(x==="---")throw Error("hole");if(x[1]==="L")return [x.charCodeAt(2)-65,drop(l),push(r,x[0])];let b=head(r,known);if(b===null)throw Error("unknown r");return [x.charCodeAt(2)-65,push(drop(l),b+x[0]),drop(r)]}
 const eq=(x,y)=>JSON.stringify(x)===JSON.stringify(y);
 function norm(w){if(lit(w))return w;let [p,b,s]=w;while(p&&p.at(-1)===b.at(-1)){let a=p.at(-1);p=p.slice(0,-1);b=a+b.slice(0,-1);s=push(s,a)}return W(p,b,norm(s))}
 function grow(w,n){return lit(w)?w:W(P(w)+B(w).repeat(n),B(w),grow(S(w),n))}
 function val(w,n){return lit(w)?w:P(w)+B(w).repeat(n)+val(S(w),n)}
 let z=[0,"",""];for(let i=0;i<c.entry;i++)z=step(z);
 if(!eq(z,[c.family[0],val(c.family[1],0),val(c.family[2],0)]))throw Error("seed "+c.root);
 z=c.family;let a=0,b=0;for(const op of c.ops){if(typeof op==="number"){for(let i=0;i<op;i++)z=step(z);b+=op;continue}
 const [d,lp,rp,I,O,L,R,k]=op;
 let input=d==="R"?[z[0],lp,rp+I]:[z[0],lp+I,rp],expected=d==="R"?[z[0],lp+O,rp]:[z[0],lp,rp+O];
 if(!eq(z,d==="R"?[z[0],push(L,lp),W(rp,I,R)]:[z[0],W(lp,I,L),push(R,rp)]))throw Error("symbolic pre "+c.root);
 for(let i=0;i<k;i++)input=step(input,true);if(!eq(input,expected))throw Error("local transfer "+c.root);
 z=d==="R"?[z[0],W(lp,O,L),push(R,rp)]:[z[0],push(L,lp),W(rp,O,R)];a+=k;
 }
 if(a!==c.a||b!==c.b||b<=0||!eq([z[0],norm(z[1]),norm(z[2])],[c.family[0],norm(grow(c.family[1],c.inc)),norm(grow(c.family[2],c.inc))]))throw Error("target "+c.root);
 return {root:c.root,entry:c.entry,inc:c.inc,a,b,sweeps:c.ops.filter(x=>typeof x!=="number").length};
}
function findAuto(t,seed,next,opts={}){
  t=t.replaceAll("_","");
  const m=t.match(/.{3}/g),lit=w=>typeof w==="string",pre=w=>lit(w)?w:w[0],block=w=>lit(w)?"":w[1],post=w=>w[2],W=(p,b="",s="")=>b?[p,b,s]:p;
  const head=w=>pre(w)[0]||(lit(w)?"0":null),drop=w=>pre(w)?W(pre(w).slice(1),block(w),post(w)):lit(w)?w:null;
  const push=(w,p)=>W(p+pre(w),block(w),post(w)),size=w=>pre(w).length+(lit(w)?0:size(post(w)));
  function norm(w){if(lit(w))return w;let [p,b,s]=w;while(p&&p.at(-1)===b.at(-1)){const c=p.at(-1);p=p.slice(0,-1);b=c+b.slice(0,-1);s=push(s,c)}return W(p,b,norm(s))}
  function grow(w,d){return lit(w)?w:W(pre(w)+block(w).repeat(d),block(w),grow(post(w),d))}
  const key=z=>JSON.stringify([z[0],norm(z[1]),norm(z[2])]);
  function step(z,local=false){let [q,l,r]=z,a=local?(l[0]||null):head(l);if(a===null)return null;const s=m[2*q+Number(a)];if(s==="---")return null;const nq=s.charCodeAt(2)-65;if(s[1]==="L")return [nq,drop(l),push(r,s[0])];let b=local?(r[0]||null):head(r);if(b===null)return null;return [nq,push(drop(l),b+s[0]),drop(r)]}
  function* sweeps(z){for(const d of ["R","L"]){let [a,b]=d==="R"?[z[1],z[2]]:[z[2],z[1]];if(lit(b))continue;let rp=pre(b),I=block(b),R=post(b);for(let f=0;f<=pre(a).length;f++){let lp=pre(a).slice(0,f),L=W(pre(a).slice(f),block(a),post(a)),s=d==="R"?[z[0],lp,rp+I]:[z[0],rp+I,lp];for(let k=1;k<=100;k++){s=step(s,true);if(!s)break;let [q,x,y]=s;if(d==="L")[x,y]=[y,x];if(q===z[0]&&y===rp&&x.startsWith(lp)&&x.length===lp.length+I.length){let O=x.slice(lp.length),aa=W(lp,O,L),bb=push(R,rp),newz=d==="R"?[q,aa,bb]:[q,bb,aa];yield [newz,d==="R"?[d,lp,rp,I,O,L,R,k]:[d,rp,lp,I,O,R,L,k]];break}}}}}
  function* inserts(x,y){const d=y.length-x.length;if(!d){if(x===y)yield x;return}if(d<0||d>120)return;for(let i=0;i<=x.length;i++){if(y.slice(0,i)===x.slice(0,i)&&y.slice(i+d)===x.slice(i))yield W(x.slice(0,i),y.slice(i,i+d),x.slice(i))}}
  let z=[0,"",""],old,neu;for(let i=0;i<=next;i++){if(i===seed)old=z;if(i===next){neu=z;break}z=step(z);if(!z)return null}
  if(old[0]!==neu[0])return null;
  let tried=new Set(),total=0;const maxNodes=opts.maxNodes||150000;
  for(let l of inserts(old[1],neu[1]))for(let r of inserts(old[2],neu[2])){let f=[old[0],l,r],fk=key(f);if(tried.has(fk))continue;tried.add(fk);let targets=new Map(Array.from({length:8},(_,i)=>[key([f[0],grow(l,i+1),grow(r,i+1)]),i+1])),seen=new Set();
    function dfs(z,path,a,b,sn){if(path.length&&targets.has(key(z)))return [targets.get(key(z)),path,a,b];if(++total>maxNodes||path.length>=350||sn>14||size(z[1])+size(z[2])>1500)return null;let k=JSON.stringify(z);if(seen.has(k))return null;seen.add(k);
      for(const [y,op] of sweeps(z)){if(JSON.stringify(y)===k)continue;let v=dfs(y,path.concat([op]),a+op[7],b,sn+1);if(v)return v}
      let y=step(z);if(y)return dfs(y,path.concat([1]),a,b+1,sn);return null
    }
    let v=dfs(f,[],0,0,0);if(v){let [inc,path,a,b]=v;let ops=[];for(let item of path){if(item===1&&typeof ops.at(-1)==="number")ops[ops.length-1]++;else ops.push(item)}return {table:t,entry:seed,family:f,inc,a,b,ops,searchNodes:total}}
  }
  return null
}
const cases=[[138,"1RB1LC_1RC0LD_0LA1LA_0RE0RD_---1RF_0RB1RB",43,154],[140,"1RB1LC_1RC0LD_0LA0LB_1RE1LB_0RF---_0RB1RD",58,145],[141,"1RB1LC_1RC0LD_0LA0RB_1LA1RE_1LF---_1RD1RF",130,197],[142,"1RB1LC_1RC0LD_0LA1LB_0RA0LE_1RE0LF_---1RD",162,312],[143,"1RB1LC_1RC0LD_0LA1RB_0RE1LB_1RF---_1LA0RE",113,198],[154,"1RB0LC_1RC0LD_0LA1LA_1RE0RD_1RF---_1RA1LD",187,329]];
const fixtures=require('./q0-coarse-pumps.json');
if(require.main===module) console.log(JSON.stringify((process.argv.includes('--regenerate')?cases.map(([root,t,s,n])=>({root,...findAuto(t,s,n)})):fixtures).map(verify),null,2));
module.exports={verify,findAuto};
