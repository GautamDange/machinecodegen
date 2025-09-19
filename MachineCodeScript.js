/* MachineCodeScript.js — minimal, fixes BRA + default.asm load
   - MSB (bit15) = 0
   - JZ/JC/JMP: 0 | opcode(4) | P(11)           (absolute PC, opcode nibble taken from rules)
   - BRA      : 0 | 1111      | BCOND(3) | O(8) (relative, two's complement)
   - x / params -> 0
   - Labels supported
   - Loads default.asm (same folder) once at startup; no fallback; no overwrite of existing text.
   - Creates MachineCodeHex.txt with hex values of all instructions
*/
(() => {
  const $ = (id) => document.getElementById(id);

  // ---------- tiny utils ----------
  const toIntSigned = (v) => {
    if (typeof v === 'number') return v|0;
    if (typeof v !== 'string') return NaN;
    v = v.trim();
    if (/^[+-]?\d+$/.test(v)) return parseInt(v,10);
    if (/^[+-]?0x[0-9a-f]+$/i.test(v)) return parseInt(v,16);
    if (/^[+-]?0b[01_]+$/i.test(v)) return parseInt(v.replace(/_/g,''),2);
    return NaN;
  };
  const maskToWidth = (value, width) => {
    const mod = 1 << Math.max(0,width);
    return ((value % mod) + mod) % mod;
  };
  const setBits = (word, startBit, width, value) => {
    const v = maskToWidth(value, width);
    for (let i=0;i<width;i++){
      const bitIndex = startBit - i;
      const bitVal = (v >> (width-1-i)) & 1;
      if (bitVal) word |= (1 << bitIndex); else word &= ~(1 << bitIndex);
    }
    return word >>> 0;
  };
  const toBin16 = (v) => (v & 0xFFFF).toString(2).padStart(16,'0').replace(/(.{4})/g,'$1 ').trim();
  const segmentedBits = (word, mnem) => {
    const raw = (word & 0xFFFF).toString(2).padStart(16,'0');
    const M = String(mnem||'').toUpperCase();
    const sizes = (M==='BRA') ? [1,4,3,8] : ((M==='JZ'||M==='JC'||M==='JMP') ? [1,4,11] : [1,4,3,2,3,3]);
    let i=0, out=[]; for(const w of sizes){ out.push(raw.slice(i,i+w)); i+=w; }
    return out.join(' | ');
  };

  // ---------- BCOND map ----------
  function parseCond(token){
    const t = String(token).trim().toUpperCase();
    if (/^[0-7]$/.test(t)) return parseInt(t,10) & 0x7;
    if (/^0B[01]+$/.test(t)) return parseInt(t.slice(2),2) & 0x7;
    if (/^0X[0-9A-F]+$/.test(t)) return parseInt(t,16) & 0x7;
    if (t==='AL'||t==='A'||t==='TRUE'||t==='UN') return 0b000;
    if (t==='Z'||t==='EQ') return 0b100;
    if (t==='C'||t==='CS') return 0b101;
    if (t==='V'||t==='OV') return 0b110;
    if (t==='N'||t==='MI') return 0b111;
    return 0b000;
  }

  // ---------- parse rules.json (AOA) ----------
  let RULES = []; let NAME2RULE = new Map();
  function parseRulesFromAOA(aoa){
    RULES=[]; NAME2RULE.clear();
    for(let r=1;r<aoa.length;r++){
      const row = aoa[r]; if(!row) continue;
      const mnemonic = (row[0]??'').toString().trim(); if(!mnemonic) continue;
      const operandsStr = (row[1]??'').toString().trim();
      let fields=[], col=2, bit=15;
      while(col<=17 && bit>=0){
        const cellRaw=row[col], cell=(cellRaw==null?'':String(cellRaw)).trim();
        if(cell===''||/^x$/i.test(cell)){ fields.push({kind:'ignore',msb:bit,width:1}); col++; bit--; continue; }
        if(cell==='0'||cell==='1'){ fields.push({kind:'const',msb:bit,width:1,value:Number(cell)}); col++; bit--; continue; }
        const mSlice = cell.match(/^(rd|rs|rt)\s*\[(\d+)\s*:\s*(\d+)\]\s*$/i);
        if(mSlice){ const name=mSlice[1].toLowerCase(), hi=+mSlice[2], lo=+mSlice[3];
          fields.push({kind:'field',name,hi,lo,width:Math.abs(hi-lo)+1,msb:bit}); col+=Math.abs(hi-lo)+1; bit-=Math.abs(hi-lo)+1; continue; }
        const mBit = cell.match(/^(rd|rs|rt)\s*\[(\d+)\]\s*$/i);
        if(mBit){ fields.push({kind:'fieldBit',name:mBit[1].toLowerCase(),which:+mBit[2],width:1,msb:bit}); col++; bit--; continue; }
        if(/^(Y|P|O)$/i.test(cell)){
          let w=1,c=col+1; while(c<=17){ const s=(row[c]==null?'':String(row[c])).trim(); if(new RegExp(`^${cell}$`,'i').test(s)){ w++; c++; } else break; }
          fields.push({kind:'imm',name:cell.toUpperCase(),width:w,msb:bit}); col+=w; bit-=w; continue;
        }
        if(/^(BCOND|COND)$/i.test(cell)){
          let w=1,c=col+1; while(c<=17){ const s=(row[c]==null?'':String(row[c])).trim(); if(/^(BCOND|COND)$/i.test(s)){ w++; c++; } else break; }
          fields.push({kind:'cond',width:w,msb:bit}); col+=w; bit-=w; continue;
        }
        fields.push({kind:'ignore',msb:bit,width:1}); col++; bit--; // unknown -> 0
      }
      const rule = { mnemonic: mnemonic.toUpperCase(), operandsStr, fields };
      RULES.push(rule); if(!NAME2RULE.has(rule.mnemonic)) NAME2RULE.set(rule.mnemonic, rule);
    }
    const cnt=$('opcodeCount'); if (cnt) cnt.textContent=RULES.length.toString();
  }

  // ---------- labels ----------
  function collectLabels(lines){
    const labels=Object.create(null); let pc=0;
    for(const line of lines){
      const code=line.replace(/;.*/,'').trim(); if(!code) continue;
      const m=code.match(/^([A-Za-z_]\w*)\s*:\s*(.*)$/);
      if(m){ const name=m[1].toUpperCase(); if(!(name in labels)) labels[name]=pc; if(m[2].trim()) pc+=1; }
      else pc+=1;
    }
    return labels;
  }
  function resolveValue(tok, labels){
    const t=String(tok).trim(); const n=toIntSigned(t);
    if(!Number.isNaN(n)) return n;
    const lab=t.replace(/:$/,'').toUpperCase();
    if(labels && (lab in labels)) return labels[lab];
    return NaN;
  }
  const parseReg = (tok)=>{ const m=String(tok).trim().match(/^r(\d{1,2})$/i); if(!m) return NaN; const n=+m[1]; return (n<0||n>15)?NaN:n; };

  // ---------- create hex file ----------
  function createHexFile(hexValues) {
    const content = hexValues.join('\n');
    const blob = new Blob([content], { type: 'text/plain' });
    const url = URL.createObjectURL(blob);
    
    const a = document.createElement('a');
    a.href = url;
    a.download = 'MachineCodeHex.txt';
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    URL.revokeObjectURL(url);
  }

  // ---------- assembler ----------
  function assembleLine(line, pc, labels){
    const raw=line.trim(); if(!raw) return {ok:true, code:null};
    const noCom=raw.replace(/;.*/,'').trim(); if(!noCom) return {ok:true, code:null};
    let code=noCom; const mL=code.match(/^([A-Za-z_]\w*)\s*:\s*(.*)$/); if(mL) code=mL[2].trim(); if(!code) return {ok:true, code:null};
    const m=code.match(/^(\S+)\s*(.*)$/); if(!m) return {ok:false, code:null};
    const MN=m[1].toUpperCase(); const rest=m[2].trim(); const ops=rest?rest.split(/\s*,\s*/):[];
    const rule=NAME2RULE.get(MN); if(!rule) return {ok:false, code:null};

    let rd=0, rs=0, rt=0, Y=0, P=0, O=0, COND=0;

    if (/^rd\s*,\s*rs\s*,\s*rt$/i.test(rule.operandsStr)){
      if (ops.length!==3) return {ok:false, code:null};
      rd=parseReg(ops[0]); rs=parseReg(ops[1]); rt=parseReg(ops[2]);
      if ([rd,rs,rt].some(Number.isNaN)) return {ok:false, code:null};
    } else if (/^rd\s*,\s*rs$/i.test(rule.operandsStr)){
      if (ops.length!==2) return {ok:false, code:null};
      rd=parseReg(ops[0]); rs=parseReg(ops[1]);
      if ([rd,rs].some(Number.isNaN)) return {ok:false, code:null};
    } else if (/^rd\s*,\s*Y$/i.test(rule.operandsStr)){
      if (ops.length!==2) return {ok:false, code:null};
      rd=parseReg(ops[0]); if(Number.isNaN(rd)) return {ok:false, code:null};
      Y=resolveValue(ops[1], labels); if(isNaN(Y)) return {ok:false, code:null};
    } else if (/^rd\s*,\s*\[rs\]$/i.test(rule.operandsStr)){
      if (ops.length!==2) return {ok:false, code:null};
      rd=parseReg(ops[0]); const mrs=String(ops[1]).match(/^\[(r\d{1,2})\]$/i); if(!mrs) return {ok:false, code:null};
      rs=parseReg(mrs[1]); if ([rd,rs].some(Number.isNaN)) return {ok:false, code:null};
    } else if (/^\[rs\]\s*,\s*rt$/i.test(rule.operandsStr)){
      if (ops.length!==2) return {ok:false, code:null};
      const mrs=String(ops[0]).match(/^\[(r\d{1,2})\]$/i); if(!mrs) return {ok:false, code:null};
      rs=parseReg(mrs[1]); rt=parseReg(ops[1]); if ([rs,rt].some(Number.isNaN)) return {ok:false, code:null};
    } else if (/\bP\b/i.test(rule.operandsStr) && !/\bcond\b/i.test(rule.operandsStr)){
      if (ops.length!==1) return {ok:false, code:null};
      P=resolveValue(ops[0], labels); if(isNaN(P)) return {ok:false, code:null};
    } else if (/\bcond\b/i.test(rule.operandsStr) && /\bO\b/i.test(rule.operandsStr)){
      if (ops.length!==2) return {ok:false, code:null};
      COND=parseCond(ops[0]);
      const rawO=ops[1]; const asNum=toIntSigned(rawO);
      if (!isNaN(asNum)) O=asNum; else { const lab=resolveValue(rawO, labels); if(isNaN(lab)) return {ok:false, code:null}; O=lab-(pc+1); }
    } else {
      return {ok:false, code:null};
    }

    // encode per table first (for non-control ops)
    let word=0, bit=15;
    for(const f of rule.fields){
      if (f.kind==='const'){ word=setBits(word,bit,1,f.value); bit--; }
      else if (f.kind==='ignore'){ bit--; }
      else if (f.kind==='field'){
        let v=0; if (f.name==='rd') v=rd; else if (f.name==='rs') v=rs; else if (f.name==='rt') v=rt;
        word=setBits(word,bit,f.width,v); bit-=f.width;
      } else if (f.kind==='fieldBit'){
        let v=0; if (f.name==='rd') v=(rd>>f.which)&1; else if (f.name==='rs') v=(rs>>f.which)&1; else if (f.name==='rt') v=(rt>>f.which)&1;
        word=setBits(word,bit,1,v); bit--;
      } else if (f.kind==='imm'){
        if (f.name==='Y') word=setBits(word,bit,f.width,Y);
        else if (f.name==='P') word=setBits(word,bit,f.width,P);
        else if (f.name==='O') word=setBits(word,bit,f.width,O);
        bit-=f.width;
      } else if (f.kind==='cond'){
        word=setBits(word,bit,f.width,COND); bit-=f.width;
      } else { bit--; }
    }

    // Hard override control-flow encodings
    if (MN==='BRA'){
      // 0 | 1111 | BCOND(3) | O(8)
      word = (0b1111<<11) | (maskToWidth(COND,3)<<8) | maskToWidth(O,8);
    } else if (MN==='JZ' || MN==='JC' || MN==='JMP'){
      // keep opcode nibble from table (bits 14..11), inject P(11)
      const opcodeNibble = (word>>11)&0xF;
      word = (opcodeNibble<<11) | maskToWidth(P,11);
    }

    // MSB=0
    word &= 0x7FFF;
    return {ok:true, code:word>>>0};
  }

  function assembleAll(){
    const lines=$('asm').value.split(/\r?\n/);
    const labels=collectLabels(lines);
    const tbody=$('outTable').querySelector('tbody'); tbody.innerHTML='';
    let pc=0;
    const hexValues = []; // Array to store hex values for the file
    
    for(let i=0;i<lines.length;i++){
      const line=lines[i];
      const res=assembleLine(line,pc,labels);
      const codePart=line.replace(/;.*/,'').trim().replace(/^([A-Za-z_]\w*)\s*:\s*/,'').trim();
      if(codePart) pc+=1;

      const m=(line.replace(/;.*/,'').trim().match(/^(\S+)\s*(.*)$/) || ['','','']);
      const mn=(m[1]||'').toUpperCase(), ops=m[2];
      const code16 = res.code==null ? null : (res.code & 0xFFFF);
      const hex = code16==null ? '' : '0x'+code16.toString(16).toUpperCase().padStart(4,'0');
      const bin = code16==null ? '' : toBin16(code16);
      const seg = code16==null ? '' : segmentedBits(code16, mn);

      // Add hex value to array for file creation (skip empty lines)
      if (code16 !== null) {
        hexValues.push(hex);
      }

      const tr=document.createElement('tr');
      tr.innerHTML = `
        <td class="small">${i+1}</td>
        <td class="mono small">${line.replace(/</g,'&lt;').replace(/>/g,'&gt;')}</td>
        <td>${mn}</td>
        <td class="small">${ops||''}</td>
        <td class="mono">${hex}</td>
        <td class="mono small">${bin}</td>
        <td class="mono small">${seg}</td>`;
      tbody.appendChild(tr);
    }
    
    // Create the hex file
    if (hexValues.length > 0) {
      createHexFile(hexValues);
    }
    
    $('assembleMsg').textContent = 'Assembled. MSB→0; JZ/JC/JMP=1|4|11; BRA=1|4|3|8. MachineCodeHex.txt created.';
  }

  // ---------- load default.asm (strict) ----------
  async function loadDefaultAsm(){
    const ta=$('asm'); 
    if(!ta) return;
    
    // Only skip loading if there's already meaningful content
    if(ta.value.trim() === '') {
      const status=$('assembleMsg');
      try{
        // cache-buster avoids stale content when you edit default.asm
        const resp = await fetch('default.asm?ts=' + Date.now(), {cache:'no-store'});
        if(!resp.ok){ 
          const msg=`default.asm not loaded (HTTP ${resp.status}).`; 
          if(status) status.textContent=msg; 
          console.error(msg); 
          return; 
        }
        const txt = await resp.text();
        if(!txt.trim()){ 
          const msg='default.asm is empty.'; 
          if(status) status.textContent=msg; 
          console.warn(msg); 
          return; 
        }
        ta.value = txt.replace(/\r?\n/g,'\n');
        if(status) status.textContent = 'Loaded default.asm.';
      }catch(e){
        const msg=`Failed to fetch default.asm: ${e?.message||e}`; 
        if(status) status.textContent=msg; 
        console.error(msg);
      }
    }
  }

  // ---------- rules.json load ----------
  async function loadRules(){
    const status=$('rulesStatus');
    try{
      const resp=await fetch('rules.json?ts='+Date.now(), {cache:'no-store'});
      if(!resp.ok) throw new Error(`HTTP ${resp.status}`);
      const aoa=await resp.json();
      parseRulesFromAOA(aoa);
      if(status) status.textContent = `Loaded rules.json · ${RULES.length} rules`;
    }catch(e){
      if(status) status.textContent='Failed to load rules.json';
      console.error(e);
    }
  }

  window.addEventListener('DOMContentLoaded', async () => {
    $('assembleBtn').addEventListener('click', assembleAll);
    await loadDefaultAsm();  // load your default.asm (no fallback, no overwrite if user typed)
    await loadRules();
  });
})();
