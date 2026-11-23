// Exact coefficient check of the global canonical (p,q) to signed (X,Y) bridge.
// Node.js: node verify_global_signed_pq_bridge.js
// Affine triples [D coefficient, R coefficient, constant].
const add=(x,y)=>x.map((v,i)=>v+y[i]), mul=(n,x)=>x.map(v=>n*v);
const G={LO:18,LE:10,RO:2,RE:4};
const next={LO:{L:"LO",R:"RO"},LE:{L:"LE",R:"RE"},RO:{L:"LE",R:"RE"},RE:{L:"LO",R:"RO"}};
const B={LO:[-1,0,-5],LE:[-1,0,-2],RO:[-1,0,4],RE:[-1,0,1]};
const Dlt={LO:[2,2,14],LE:[2,2,8],RO:[2,2,0],RE:[2,2,3]};
const sourceC={
 LO:{L:[-18,-16,-122],R:[12,4,-6]},
 LE:{L:[-18,-16,-68],R:[12,4,-12]},
 RO:{L:[-18,-16,0],R:[12,4,-44]},
 RE:{L:[-18,-16,-36],R:[12,4,-20]}
};
const sourceF={
 LO:{L:[12,12,84],R:[-6,0,24]},
 LE:{L:[12,12,48],R:[-6,0,18]},
 RO:{L:[12,12,0],R:[-6,0,30]},
 RE:{L:[12,12,18],R:[-6,0,18]}
};
for (const s of Object.keys(G)) for (const branch of ["L","R"]) {
 const t=next[s][branch], g=G[s], gt=G[t];
 const k=branch==="L"
  ? add([0,0,g-gt], add(mul(2,B[s]),mul(-8,Dlt[s])))
  : add([0,0,-4*g-gt],add(mul(2,Dlt[s]),mul(-8,B[s])));
 const phi=branch==="L" ? mul(6,Dlt[s]) : add([0,0,3*g],mul(6,B[s]));
 const equal=(a,b)=>a.length===b.length && a.every((v,i)=>v===b[i]);
 const pass=equal(k,sourceC[s][branch])&&equal(phi,sourceF[s][branch]);
 console.log(s,branch,pass?"PASS":"FAIL",JSON.stringify({k,phi}));
 if(!pass)process.exitCode=1;
}
