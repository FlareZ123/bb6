"use strict";
const {build}=require("./generate-q0-149-three-run-certs.cjs");
const bits=s=>"["+Array.from(s,c=>c==="1"?"true":"false").join(",")+"]";
const word=w=>typeof w==="string"?"(.lit "+bits(w)+")":w.length===2?"(.tail "+bits(w[0])+" "+w[1]+")":"(.periodic "+bits(w[0])+" "+bits(w[1])+" "+w[2]+" "+word(w[3])+")";
const pz=z=>"⟨"+z[0]+","+word(z[1])+","+word(z[2])+"⟩";
const action=o=>typeof o==="number"?".steps "+o:"."+(o[0]==="L"?"left":"right")+" "+o.slice(1,5).map(bits).join(" ")+" "+o[5]+" "+word(o[6])+" "+word(o[7])+" "+o[8];
const tbl=t=>t.replaceAll("_","").match(/.{3}/g).map((v,i)=>v==="---"?"  | "+(i>>1)+","+(!!(i%2))+" => none":"  | "+(i>>1)+","+(!!(i%2))+" => some (some ⟨"+(v[0]==="1")+","+(v[1]==="R")+","+(v.charCodeAt(2)-65)+"⟩)").join("\n");
const run=(v,n)=>"block "+v+" ("+n+")";
const u=n=>run(true,n),z=n=>run(false,n);
const lit=s=>Array.from(s.matchAll(/(0+|1+)/g),m=>run(m[0][0]==="1",m[0].length));
const append=xs=>xs.length===0?"[]":xs.map(x=>"("+x+")").join(" ++ ");
const expr=xs=>append(xs);
const tail=(s,X)=>[...lit(s),...X];
function seg(w,n,m,X,Y){
 if(typeof w==="string")return lit(w);
 if(w.length===2)return tail(w[0],w[1]?Y:X);
 if(!/^0+$|^1+$/.test(w[1]))throw Error("nonhomogeneous block");
 return [...lit(w[0]),"rep ("+run(w[1][0]==="1",w[1].length)+") "+(w[2]?m:n),...seg(w[3],n,m,X,Y)];
}
const T=(x,y)=>[[u(y),z(2),u(x)],[z(1)]];
const S=(x,b,W)=>[[z(2),u(x)],[...lit("10"),u(b),...W]];
const all=(a,b)=>a.map((v,i)=>[v,b[i]]);
function normalize(xs){
 let acc=[];
 for(let i=xs.length-1;i>=0;i--){
  let s=xs[i],a=s.match(/^block (true|false) \((.*)\)$/),b=s.match(/^rep \(block (true|false) \((.*)\)\) (.*)$/);
  if(b)a=[null,b[1],b[2]+"*"+b[3]];
  if(!a){acc.unshift({tail:s});continue;}
  let bit=a[1],n=a[2];
  if(acc.length&&acc[0].bit===bit){n="("+n+")+("+acc.shift().n+")";}
  acc.unshift({bit,n});
 }
 return acc;
}
const normExpr=xs=>expr(xs.map(s=>s.tail||run(s.bit,s.n)));
function eqProof(a,b){
 if(a.length!==b.length)throw Error("different normalized shapes "+JSON.stringify({a,b}));
 if(!a.length)return "rfl";
 let x=a[0],y=b[0],h;
 if(x.tail!==undefined){if(x.tail!==y.tail)throw Error("different tails");h="rfl";}
 else {if(x.bit!==y.bit)throw Error("different bits");h="congrArg (block "+x.bit+") (show ("+x.n+") = ("+y.n+") by omega)";}
 if(a.length===1)return h;
 return "congrArg₂ List.append ("+h+") ("+eqProof(a.slice(1),b.slice(1))+")";
}
function proof(a,b,cn,pad){
 if(pad!==undefined)return "      exact "+pad+"\n";
 let na=normalize(a),nb=normalize(b);
 return "      apply weq_of_eq\n      have e : ("+expr(a)+") = ("+expr(b)+") := by\n        calc\n          _ = ("+normExpr(na)+") := by simp only [List.append_assoc,blockRep,blockJoin,blockJoinLast]\n          _ = ("+normExpr(nb)+") := "+eqProof(na,nb)+"\n          _ = _ := by simp only [List.append_assoc,blockRep,blockJoin,blockJoinLast]\n      simpa [T,S,U,Z,Tails.PZ.eval,Tails.Word.eval,cert_"+cn+",block,rep,List.append_assoc] using e\n";
}
function gen(m){
 let out="namespace M"+m.index+"\ndef table : PartialMachine := fun s => match s.1.val,s.2 with\n"+tbl(m.table)+"\n  | _,_ => none\n";
 for(const [name,c] of Object.entries(m.certs)){
   out+="def cert_"+name+" : Tails.Cert := ⟨"+pz(c.src)+","+pz(c.target)+",["+c.ops.map(action).join(",")+"],"+c.cost.join(",")+"⟩\n";
   out+="theorem check_"+name+" : Tails.check table cert_"+name+" = true := by decide +kernel\n";
 }
 out+="theorem rules : Rules table where\n";
 for(const [name,c] of Object.entries(m.certs)){
   let n="n",mm="0",X=[u("x")],Y=[],Xarg="(U x)",Yarg="[]",src,dst,args,padL,padR;
   if(name==="init"){args="x n";src=T("x","n+1");dst=S("x","n",[]);}
   else if(name==="odd"){
     args="x b W hb";mm="x";X=[];Y=["W"];Xarg="[]";Yarg="W";
     src=S("x","2*n+1",[z(1),"W"]);dst=S("0","x+2",[z("2*n+1"),u(1),"W"]);
     dst[0]=[z(2)];padL="(WEq.pad [] 2).symm";
   }else{
     args="x b "+(name==="reduce"?"W ":"")+"hb hp";let b="2*n+2";
     if(name==="reduce"){Y=["W"];Yarg="W";src=S("x",b,[z(4),"W"]);dst=S("x+2",b+"+2",["W"]);}
     if(name==="end"){src=S("x",b,lit("01"));dst=T("x+2",b+"+2");padR="(WEq.pad [] 1).symm";}
     if(name==="turn1"){src=S("x",b,lit("0001"));dst=S("x+2",b+"+3",lit("011"));}
     if(name==="turn3"){src=S("x",b,lit("000111"));dst=S("x+2",b+"+3",lit("01111"));}
     if(name==="five"){src=S("x",b,lit("011111"));dst=S("x+2",b,lit("00001"));}
   }
   const field=name==="end"?"finish":name;
   out+="  "+field+" "+args+" := by\n";
   if(name!=="init")out+="    obtain ⟨n,hn⟩ : ∃ n : Nat, b = 2*n+"+(name==="odd"?"1 := ⟨b/2,by omega⟩":"2 := ⟨b/2-1,by omega⟩")+"\n    subst b\n";
   out+="    refine RE.ofRun (Tails.check_sound table cert_"+name+" check_"+name+" "+n+" "+mm+" "+Xarg+" "+Yarg+") (by change 0 < "+c.cost[0]+"*"+n+"+"+c.cost[1]+"*"+mm+"+"+c.cost[2]+"; omega) ?_ ?_\n";
   out+="    · refine ⟨rfl,?_,?_⟩\n";
   for(let i=0;i<2;i++)out+="      ·"+proof(src[i],seg(c.src[i+1],n,mm,X,Y),name).trimStart().replace(/^/," ").replace(/\n(?=.)/g,"\n  ");
   out+="    · refine ⟨rfl,?_,?_⟩\n";
   for(let i=0;i<2;i++)out+="      ·"+proof(seg(c.target[i+1],n,mm,X,Y),dst[i],name,i===0?padL:padR).trimStart().replace(/^/," ").replace(/\n(?=.)/g,"\n  ");
 }
 let seed=m.index===16?37:43;
 out+="theorem seed : run0 table "+seed+" ⟨0,[],[]⟩ = some ⟨0,"+bits("11110011")+",[]⟩ := by decide +kernel\n";
 out+="theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=\n  Q0149.never rules "+seed+" _ seed ⟨rfl,WEq.refl _,(WEq.pad [] 1).symm⟩ m hm\n";
 out+="theorem cover (B : Nat) : Cover (WeightedBound B) table :=\n  .leaf _ fun m hm => weighted_never B m (never m hm)\n#print axioms cover\nend M"+m.index+"\n";
 return out;
}
console.log("import Agent47Q0149Region\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nnamespace BB6Coverage.Agent31Pump.Q0149.Raw11\nopen BB6Coverage Agent31Pump Frame150 BB6.Agent13BlankDelay\n"+build().map(gen).join("\n")+"\nend BB6Coverage.Agent31Pump.Q0149.Raw11");
