"use strict";
function discover(t,source,target,opts={}){
 const m=t.replaceAll("_","").match(/.{3}/g),lit=w=>typeof w==="string",tail=w=>Array.isArray(w)&&w.length===2,P=w=>lit(w)?w:w[0],B=w=>lit(w)||tail(w)?"":w[1],V=w=>tail(w)?w[1]:w[2],S=w=>w[3],W=(p,b="",v=0,s="")=>b?[p,b,v,s]:p;
 const head=(w,local)=>P(w)[0]||(!local&&lit(w)?"0":null),drop=w=>P(w)?(tail(w)?[P(w).slice(1),V(w)]:W(P(w).slice(1),B(w),V(w),S(w))):lit(w)?w:null,push=(w,p)=>tail(w)?[p+P(w),V(w)]:W(p+P(w),B(w),V(w),S(w)),size=w=>P(w).length+(lit(w)||tail(w)?0:size(S(w)));
 function norm(w){if(lit(w)||tail(w))return w;let [p,b,v,s]=w;while(p&&p.at(-1)===b.at(-1)){const c=p.at(-1);p=p.slice(0,-1);b=c+b.slice(0,-1);s=push(s,c)}return W(p,b,v,norm(s))}
 const key=z=>JSON.stringify([z[0],norm(z[1]),norm(z[2])]),tk=key(target);
 function step(z,local=false){let [q,l,r]=z,a=head(l,local);if(a===null)return null;const s=m[2*q+Number(a)];if(s==="---")return null;const nq=s.charCodeAt(2)-65;if(s[1]==="L")return [nq,drop(l),push(r,s[0])];let b=head(r,local);if(b===null)return null;return [nq,push(drop(l),b+s[0]),drop(r)]}
 function* sweeps(z){for(const d of ["R","L"]){let [a,b]=d==="R"?[z[1],z[2]]:[z[2],z[1]];if(lit(b)||tail(b))continue;let rp=P(b),I=B(b),v=V(b),R=S(b);for(let f=0;f<=P(a).length;f++){let lp=P(a).slice(0,f),L=tail(a)?[P(a).slice(f),V(a)]:W(P(a).slice(f),B(a),V(a),S(a)),s=d==="R"?[z[0],lp,rp+I]:[z[0],rp+I,lp];for(let k=1;k<=100;k++){s=step(s,true);if(!s)break;let [q,x,y]=s;if(d==="L")[x,y]=[y,x];if(q===z[0]&&y===rp&&x.startsWith(lp)&&x.length===lp.length+I.length){let O=x.slice(lp.length),aa=W(lp,O,v,L),bb=push(R,rp),newz=d==="R"?[q,aa,bb]:[q,bb,aa];yield [newz,d==="R"?[d,lp,rp,I,O,v,L,R,k]:[d,rp,lp,I,O,v,R,L,k]];break}}}}}
 function* frames(w){if(lit(w)||tail(w))return;let [p,b,v,s]=w;if(P(s)&&P(s)[0]===b[0])yield W(p+b[0],b.slice(1)+b[0],v,drop(s));if(p&&p.at(-1)===b.at(-1))yield W(p.slice(0,-1),b.at(-1)+b.slice(0,-1),v,push(s,p.at(-1)));for(const x of frames(s))yield W(p,b,v,x)}
 let seen=new Set(),total=0;const path=[];
 function dfs(z,sn,fr){if(path.length&&key(z)===tk)return true;if(++total>(opts.nodes||500000)||path.length>(opts.depth||2000)||sn>150||fr>300||size(z[1])+size(z[2])>1000)return false;let k=JSON.stringify(z);if(seen.has(k))return false;seen.add(k);
 for(const [y,op] of sweeps(z)){if(JSON.stringify(y)===k)continue;path.push(op);if(dfs(y,sn+1,fr))return true;path.pop()}
 const y=step(z);if(y){path.push(1);if(dfs(y,sn,fr))return true;path.pop()}
 if(opts.frames){for(const x of frames(z[1])){let y=[z[0],x,z[2]];path.push(["f",y]);if(dfs(y,sn,fr+1))return true;path.pop()}for(const x of frames(z[2])){let y=[z[0],z[1],x];path.push(["f",y]);if(dfs(y,sn,fr+1))return true;path.pop()}}
 return false}
 let ok=dfs(source,0,0);if(!ok)return {ok,total};const ops=[];for(const x of path){if(x===1&&typeof ops.at(-1)==="number")ops[ops.length-1]++;else ops.push(x)}return {ok,total,source,target,ops,primitive:ops.filter(x=>typeof x==="number").reduce((a,b)=>a+b,0),sweeps:ops.filter(x=>Array.isArray(x)&&x[0]!=="f").length,frames:ops.filter(x=>Array.isArray(x)&&x[0]==="f").length};
}
module.exports={discover};
