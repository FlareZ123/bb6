// Discover a finite affine path with two concrete exponents, then certify
// every symbolic stack operation using rule() (not numerical extrapolation).
const fs=require("fs"),path=require("path");
const {rule,exits}=require("./generate_raw140_variant_transfer.js");
function instantiate(w,p) {
  return w.trim().split(/ +/).filter(Boolean).map(tok=>{
    if(tok==="X")return "8";if(tok==="Y")return "9";
    const [b,n]=tok.split("^");
    const k=n===undefined?1:n.startsWith("p")?p+(n.length===1?0:+n.slice(2)):+n;
    return b.repeat(k);
  }).join("");
}
function find(table,L0,R0,q0,d0,L1,R1,q1,d1,p){
  let q=q0,d=d0,L=instantiate(L0,p),R=instantiate(R0,p);
  const l=instantiate(L1,p),r=instantiate(R1,p),E=exits(table),seq=[];
  let cost=0;
  for(let i=0;i<10000;i++){
    if(q===q1&&d===d1&&L===l&&R===r)return {seq,cost};
    const S=d?R:L,a=+(S[0]||0);
    if(a>=8)throw Error("opaque context read");
    const e=E[[q,d,a]];if(!e)throw Error("undefined");
    let m=1;
    if(e[0]===q&&e[1]===d&&S.length)while(S[m]===S[0])m++;
    if(d)R=R.slice(m);else L=L.slice(m);
    seq.push(["ABCDEF"[q]+(d?"R":"L")+a,m]);
    const [n,z,b,k]=e;q=n;d=z;cost+=m*k;
    const v=String(b).repeat(m);
    if(d){if(L||b)L=v+L}else if(R||b)R=v+R;
  }
  throw Error("no endpoint");
}
function derive(name,table,...args){
  const a=find(table,...args,20),b=find(table,...args,21);
  if(a.seq.length!==b.seq.length)throw Error(name+" path lengths");
  const seq=a.seq.map(([s,m],i)=>{
    const [t,n]=b.seq[i];
    if(s!==t||n-m<0||n-m>1)throw Error(name+" differing path");
    if(n===m)return s+(m===1?"":"^"+m);
    if(m<20)throw Error(name+" negative affine count");
    return s+"^p"+(m===20?"":"+"+(m-20));
  }).join(" ");
  console.log(name,"cost",(b.cost-a.cost)+"p+"+(a.cost-20*(b.cost-a.cost)));
  return rule(name,table,...args,seq);
}
const specs=[
  ["seedA2",42,"3^p+4 2","2",0,1,"6^p 4","4^8 6 2",3,0],
  ["seedBblank",42,"5^p+4","",1,1,"1 3^3 5^p","1 5 2",4,1],
  ["lowB64",42,"5^p","6 4",1,1,"5^p+5","",1,1],
  ["seedMixed",42,"3^p+8 2","5 2 1 5",0,1,"2 7 3^p 2","3 2^3 4 6 4^2 6 4 0 5",4,1],
  ["oddInit","base","3^p+1","1 Y",4,1,"2","1^p+1 5 Y",4,1],
  ["oddPump","base","3^p 2","1 1 1 Y",4,1,"3^p+4 2","1 Y",4,1],
  ["oddFinish","base","3^p 2","1 5 Y",4,1,"3^p+4 2","Y",0,1],
  ["mixed44","base","2 X","3 4 4 Y",4,1,"X","2 5 4 6 Y",1,0],
  ["mixed54","base","2 X","3 5 4 Y",4,1,"X","2 2 4 6 Y",1,0],
  ["mixed464","base","2 X","3 4 6 4 Y",4,1,"4 5 2 6 X","4 Y",2,1],
  ["mixed466","base","2 X","3 4 6 6 Y",4,1,"4 5 2 6 X","6 Y",2,1],
  ["mixed564","base","2 X","3 5 6 4 Y",4,1,"4 5 2 2 X","4 Y",2,1],
  ["mixed566","base","2 X","3 5 6 6 Y",4,1,"4 5 2 2 X","6 Y",2,1],
  ["mixedBack4","base","5 5 2 6 X","Y",3,0,"X","2 5 4 4 Y",1,0],
  ["mixedBack5","base","5 5 2 2 X","Y",3,0,"X","2 2 4 4 Y",1,0],
  ["pump644","base","3^p 2","6 4 4 Y",0,1,"3^p+4 2","6 Y",0,1],
  ["a6ToB","base","3^p 2","6 Y",0,1,"5^p+3","Y",1,1],
  ["a24ToD","base","3^p 2","2 4 Y",0,1,"6^p+2 4","6 Y",3,0],
  ["initC","base","4 6 X","2 2 3 Y",0,1,"2 5 2 6 X","3 Y",4,1],
  ["finishC","base","5 2 6^p 4","2^4 Y",1,0,"3^p+2 2","2^5 Y",0,1],
  ["lowC315",42,"3^p 2","2 3 2 2 3 1 5",0,1,"3^p+13 2","2",0,1],
  ["evenFinish","base","3^p 2","1 1 5 Y",4,1,"1 3^p+4 2","Y",4,1]
];
let out="import Raw140VariantTransfer\nnamespace Raw14042LowLocal\nopen BB6BlockFAR Raw140Orbit Raw140Extra Raw140VariantTransfer\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n";
out+=specs.map(x=>derive(...x)).join("\n")+"\n"+specs.map(x=>"#print axioms "+x[0]).join("\n")+"\nend Raw14042LowLocal\n";
fs.writeFileSync(path.join(__dirname,"Raw14042LowLocal.lean"),out);
