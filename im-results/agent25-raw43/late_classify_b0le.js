#!/usr/bin/env node
const fs=require("fs"),path=require("path");
const api=new Function(fs.readFileSync(path.join(__dirname,"discover.js"),"utf8"))();
const rows={
 la31:"1RB0LA_1RC0LE_0RD0RE_1LD0RB_1LA1RF_1RD---",
 la44:"1RB0LA_1RC0LE_0RD1RA_1LD0RB_1LA1LF_---0LD",
 la62:"1RB0LA_1RC0LE_0RD1RF_1LD0RB_1LA1RA_0RE---",
 lb746:"1RB1RA_1RC0LE_0RD1RF_1LD0RB_1LB1LD_0RA---",
 lf330:"1RB1LF_1RC0LE_0RD0RB_1LD0RB_1LF---_0LA0LB",
 lf331:"1RB1RD_1RC0LE_0RD0RB_1LD0RB_1LF---_0LA0LB",
 lf396:"1RB1RD_1RC0LE_0RD1LA_1LD0RB_1LF---_0LA0LB",
 lf746:"1RB---_1RC0LE_0RD1RE_1LD0RB_1LF1RA_0RA0LF"
};
const id=process.argv[2]; if(!rows[id])throw new Error("unknown id");
const cap=+(process.argv[3]||1000000),lookback=+(process.argv[4]||256);
const result=api.classify(api.parse(rows[id]),cap,lookback);
console.log(JSON.stringify({id,table:rows[id],cap,lookback,result}));
