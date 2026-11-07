#!/usr/bin/env python3
"""Generator of the amd64 U-WITNESS-CALLSITE blocks for the toy-runtime ("Unmarshal-like") witnesses.
block(cfg) -> (defs_text, stmt_conjuncts_text, proof_terms_list)."""

def okpos(i, n, x):
    # disjunction position i of n: Or.inr^i (Or.inl x), last: Or.inr^(n-1) x
    if i == n - 1:
        return 'Or.inr (' * i + x + ')' * i
    return 'Or.inr (' * i + 'Or.inl (' + x + ')' + ')' * i

def block(c):
    S0 = c.get('s0', 's0'); B = c['B']; R = c.get('R', 'R'); R2 = c['R2']; RT = c.get('rt_eq', 'rt_eq'); N = c['nok']
    inv = c.get('inv0', 'inv0'); P = c['pos']
    ty = c['newty']; dst = c['dst']; src = c['src']
    ent = lambda x: f'(Extracted.program.contractAddr "{x}")'
    K = 'fun i => if i = 4 then s0.regs 4 else s0.regs i'
    d = []
    d.append(f'''/-- Call states of the runtime stubs (U-WITNESS-CALLSITE): `{S0}` with `RIP` at the stub's entry and the stub's argument registers. -/
def csNew : State := {{ {S0} with rip := BitVec.ofNat 64 newA, regs := fun i => if i = 0 then BitVec.ofNat 64 {ty} else {S0}.regs i }}
def csW1 : State := {{ {S0} with rip := BitVec.ofNat 64 w1A }}
def csW2 : State := {{ {S0} with rip := BitVec.ofNat 64 w2A }}
def csMg : State := {{ {S0} with rip := BitVec.ofNat 64 mgA, regs := fun i => if i = 0 then 1 else if i = 3 then 0 else if i = 1 then 0 else {S0}.regs i }}
def csMv : State := {{ {S0} with rip := BitVec.ofNat 64 mvA, regs := fun i => if i = 0 then BitVec.ofNat 64 {dst} else if i = 3 then BitVec.ofNat 64 {src} else if i = 1 then 1 else {S0}.regs i }}
def csCm : State := {{ {S0} with rip := BitVec.ofNat 64 cmA, regs := fun i => if i = 0 then 0 else if i = 3 then 0 else if i = 1 then 0 else if i = 7 then 0 else {S0}.regs i }}
def csIf : State := {{ {S0} with rip := BitVec.ofNat 64 ifA, regs := fun i => if i = 0 then 0 else {S0}.regs i }}
''')
    if c.get('sb'):
        d.append(f'''def csSb : State := {{ {S0} with rip := BitVec.ofNat 64 sbA, regs := fun i => if i = 0 then BitVec.ofNat 64 {c['sb_buf']} else if i = 3 then BitVec.ofNat 64 {c['sb_p']} else if i = 1 then 48 else {S0}.regs i }}
''')
    for nm, a, ad in (('New','new','newA'),('W1','w1','w1A'),('W2','w2','w2A'),('Mg','mg','mgA'),('Mv','mv','mvA'),('Cm','cm','cmA'),('If','if','ifA')):
        names = {'new':'runtime.newobject','w1':'runtime.gcWriteBarrier1','w2':'runtime.gcWriteBarrier2','mg':'runtime.mallocgc','mv':'runtime.memmove','cm':'runtime.cmpstring','if':'runtime.ifaceeq'}
        d.append(f'theorem cs{nm}_rip : cs{nm}.rip = BitVec.ofNat 64 {ent(names[a])} := by rw [addr_{a}]; rfl\n')
    if c.get('sb'):
        d.append(f'theorem csSb_rip : csSb.rip = BitVec.ofNat 64 {c["sb_addr"]} := by rw [show {c["sb_addr"]} = sbA by decide]; rfl\n')
    win = lambda s, n: f'(liveWin64 {s} 4096 {n})'
    sep = f'(by rw [{RT}]; intro r hr; simp only [liveWin64, calleeStack64, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with (rfl | rfl) | rfl <;> (simp only [outside_cons, outside_nil]; decide))'
    sep0 = f'(by rw [{RT}]; intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp only [outside_cons, outside_nil]; decide)'
    ok_new = okpos(P['new'], N, f'⟨rfl, by decide⟩') if not c.get('new_or') else okpos(P['new'], N, f'⟨rfl, Or.inl (by decide)⟩')
    ok_w1 = okpos(P['w1'], N, '⟨rfl, by decide⟩')
    ok_w2 = okpos(P['w2'], N, '⟨rfl, by decide⟩')
    ok_mg = okpos(P['mg'], N, '⟨rfl, 1, by decide, by decide, by decide⟩')
    ok_mv = okpos(P['mv'], N, f'⟨rfl, {dst}, {src}, 1, by decide, by decide, by decide⟩')
    # new / mallocgc / memmove (LiveAt based)
    d.append(f'''set_option maxRecDepth 100000 in
theorem csNew_pre : NewobjectPre64 4096 csNew ∧ StackRoom64 csNew 4096 1 ∧
    LiveAt {R} {ent('runtime.newobject')} [(csNew.regs 0).toNat] [] {B} (newobjectRound64 csNew)
      (csNew.regs 14).toNat csNew.mem {win('csNew',1)} :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by simp only [calleeStack64, outside_cons, outside_nil]; decide⟩,
    by rw [addr_new]; exact {ok_new}, {inv}, by decide, liveSep_nil _, {sep}⟩

set_option maxRecDepth 100000 in
theorem csMg_pre : MallocgcPre64 4096 csMg ∧ StackRoom64 csMg 4096 3 ∧
    LiveAt {R} {ent('runtime.mallocgc')} [(csMg.regs 0).toNat, (csMg.regs 3).toNat, (csMg.regs 1).toNat] [] {B} (mallocgcRound64 csMg)
      (csMg.regs 14).toNat csMg.mem {win('csMg',3)} :=
  ⟨⟨by decide, by decide, Or.inl (by decide)⟩, ⟨by decide, by simp only [calleeStack64, outside_cons, outside_nil]; decide⟩,
    by rw [addr_mg]; exact {ok_mg}, {inv}, by decide, liveSep_nil _, {sep}⟩

set_option maxRecDepth 100000 in
theorem csMv_pre : MemPre64 4096 3 csMv ∧
    LiveMemAt64 {R} {ent('runtime.memmove')} [(csMv.regs 0).toNat, (csMv.regs 3).toNat, (csMv.regs 1).toNat] [] {B} csMv {win('csMv',3)} ∧
    MemAmd64.Input csMv 4096 3 (csMv.regs 3).toNat (csMv.regs 1).toNat ∧
    LiveDest64 {R} [] csMv 4096 3 (csMv.regs 0).toNat (csMv.regs 1).toNat :=
  ⟨by decide, by rw [addr_mv]; exact ⟨{ok_mv}, {inv}, liveSep_nil _, {sep}⟩, by decide,
    by decide, by decide, by rw [{RT}]; simp only [calleeStack64, outside_cons, outside_nil]; decide, Or.inr (by rw [{RT}]; simp only [outside_cons, outside_nil]; decide), by simp only [outside_cons, outside_nil]; decide⟩

set_option maxRecDepth 100000 in
theorem csW1_pre : CallOK64 csW1 4096 0 ∧ {R}.ok {ent('runtime.gcWriteBarrier1')} [1] ∧
    {R}.inv {B} [] (csW1.regs 14).toNat (view {R}.rt [] csW1.mem) ∧ LiveSep [] [((csW1.regs 4).toNat - 4096, (csW1.regs 4).toNat + 8)] ∧
    LiveSep [((csW1.regs 4).toNat - 4096, (csW1.regs 4).toNat + 8)] {R}.rt :=
  ⟨by decide, by rw [addr_w1]; exact {ok_w1}, {inv}, liveSep_nil _,
    liveSep_one (by rw [{RT}]; simp only [outside_cons, outside_nil]; decide)⟩

set_option maxRecDepth 100000 in
theorem csW2_pre : CallOK64 csW2 4096 0 ∧ {R}.ok {ent('runtime.gcWriteBarrier2')} [2] ∧
    {R}.inv {B} [] (csW2.regs 14).toNat (view {R}.rt [] csW2.mem) ∧ LiveSep [] [((csW2.regs 4).toNat - 4096, (csW2.regs 4).toNat + 8)] ∧
    LiveSep [((csW2.regs 4).toNat - 4096, (csW2.regs 4).toNat + 8)] {R}.rt :=
  ⟨by decide, by rw [addr_w2]; exact {ok_w2}, {inv}, liveSep_nil _,
    liveSep_one (by rw [{RT}]; simp only [outside_cons, outside_nil]; decide)⟩

set_option maxRecDepth 100000 in
theorem csCm_pre : Janus.Contracts.Cmpstring.CmpstringPre64 16 csCm :=
  ⟨by decide, by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem csIf_pre : Janus.Contracts.IfaceAmd64.RTPre {R2} 3 csIf ∧ ((csIf.regs 0).toNat ≠ 0 → (csIf.regs 0).toNat + 16 ≤ 2 ^ 48 ∧
      csIf.mem.accessible (csIf.regs 0).toNat 16 false = true ∧ (csIf.mem.readLE ((csIf.regs 0).toNat + 8) 8 ≠ 0) ∧
      Janus.Contracts.Iface.EqOK {R2} csIf.mem (csIf.mem.readLE ((csIf.regs 0).toNat + 8) 8) (csIf.regs 3).toNat (csIf.regs 1).toNat) :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    fun h => absurd (by decide) h⟩
''')
    if c.get('sb'):
        ok_sb = okpos(P['sb'], N, c['sb_ok'])
        d.append(f'''set_option maxRecDepth 100000 in
theorem csSb_pre : RtLivePre64 4096 {R} (slicebytetostringSpec {c['st_addr']}) slicebytetostringLive {c['sb_addr']} [] {B} csSb := by
  have hok : {R}.ok {c['sb_addr']} [(csSb.regs 0).toNat, (csSb.regs 3).toNat, (csSb.regs 1).toNat] := by
    rw [show {c['sb_addr']} = sbA by decide]; exact {ok_sb}
  unfold RtLivePre64
  refine ⟨by decide, ?_, ?_, trivial, ⟨by decide, by simp only [calleeStack64, outside_cons, outside_nil]; decide⟩, hok, {inv}, by decide, liveSep_nil _, {sep}⟩
  · simp [slicebytetostringSpec, argWords64, arg, BufOK, StrIn]; decide
  · simp only [slicebytetostringSpec, argWords64, arg, ReadsOutside, calleeStack64, outside_cons, outside_nil]; decide
''')
    stmt = []
    L = '(Lc : List (Nat × Nat)) (bc : Nat)'
    stmt.append(f'''    (∃ {L} (s_c : State), s_c.rip = BitVec.ofNat 64 {ent('runtime.newobject')} ∧ NewobjectPre64 4096 s_c ∧ StackRoom64 s_c 4096 1 ∧
      LiveAt R {ent('runtime.newobject')} [(s_c.regs 0).toNat] Lc bc (newobjectRound64 s_c) (s_c.regs 14).toNat s_c.mem (liveWin64 s_c 4096 1)) ∧
    (∃ {L} (s_c : State), s_c.rip = BitVec.ofNat 64 {ent('runtime.mallocgc')} ∧ MallocgcPre64 4096 s_c ∧ StackRoom64 s_c 4096 3 ∧
      LiveAt R {ent('runtime.mallocgc')} [(s_c.regs 0).toNat, (s_c.regs 3).toNat, (s_c.regs 1).toNat] Lc bc (mallocgcRound64 s_c)
        (s_c.regs 14).toNat s_c.mem (liveWin64 s_c 4096 3)) ∧
    (∃ {L} (s_c : State), s_c.rip = BitVec.ofNat 64 {ent('runtime.memmove')} ∧ MemPre64 4096 3 s_c ∧
      LiveMemAt64 R {ent('runtime.memmove')} [(s_c.regs 0).toNat, (s_c.regs 3).toNat, (s_c.regs 1).toNat] Lc bc s_c (liveWin64 s_c 4096 3) ∧
      MemAmd64.Input s_c 4096 3 (s_c.regs 3).toNat (s_c.regs 1).toNat ∧
      LiveDest64 R Lc s_c 4096 3 (s_c.regs 0).toNat (s_c.regs 1).toNat) ∧''')
    for n in (1, 2):
        stmt.append(f'''    (∃ {L} (s_c : State), s_c.rip = BitVec.ofNat 64 {ent(f'runtime.gcWriteBarrier{n}')} ∧ CallOK64 s_c 4096 0 ∧
      R.ok {ent(f'runtime.gcWriteBarrier{n}')} [{n}] ∧ R.inv bc Lc (s_c.regs 14).toNat (view R.rt Lc s_c.mem) ∧
      LiveSep Lc [((s_c.regs 4).toNat - 4096, (s_c.regs 4).toNat + 8)] ∧
      LiveSep [((s_c.regs 4).toNat - 4096, (s_c.regs 4).toNat + 8)] R.rt) ∧''')
    stmt.append(f'''    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 {ent('runtime.cmpstring')} ∧ Janus.Contracts.Cmpstring.CmpstringPre64 16 s_c) ∧
    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 {ent('runtime.ifaceeq')} ∧ Janus.Contracts.IfaceAmd64.RTPre R2 3 s_c ∧ ((s_c.regs 0).toNat ≠ 0 →
      (s_c.regs 0).toNat + 16 ≤ 2 ^ 48 ∧ s_c.mem.accessible (s_c.regs 0).toNat 16 false = true ∧
      (s_c.mem.readLE ((s_c.regs 0).toNat + 8) 8 ≠ 0) ∧
      Janus.Contracts.Iface.EqOK R2 s_c.mem (s_c.mem.readLE ((s_c.regs 0).toNat + 8) 8) (s_c.regs 3).toNat (s_c.regs 1).toNat)) ∧''')
    terms = ['⟨[], %s, csNew, csNew_rip, csNew_pre⟩' % B, '⟨[], %s, csMg, csMg_rip, csMg_pre⟩' % B, '⟨[], %s, csMv, csMv_rip, csMv_pre⟩' % B,
             '⟨[], %s, csW1, csW1_rip, csW1_pre⟩' % B, '⟨[], %s, csW2, csW2_rip, csW2_pre⟩' % B,
             '⟨csCm, csCm_rip, csCm_pre⟩', '⟨csIf, csIf_rip, csIf_pre⟩']
    if c.get('sb'):
        stmt.append(f'''    (∃ {L} (s_c : State), s_c.rip = BitVec.ofNat 64 {c['sb_addr']} ∧
      RtLivePre64 4096 R (slicebytetostringSpec {c['st_addr']}) slicebytetostringLive {c['sb_addr']} Lc bc s_c) ∧''')
        terms.append('⟨[], %s, csSb, csSb_rip, csSb_pre⟩' % B)
    return ''.join(d), '\n'.join(stmt) + '\n', terms
