#!/usr/bin/env python3
"""Derive C/jet_elements_indexed_gen.v from C/jet_elements_indexed_ptr.v.

The generic indexed-getter proof is the accepted single-helper proof with the
success branch abstracted: the consumer supplies an arbitrary statement and
its contract on the selected element.  Every substitution is asserted."""
import sys
src = open('C/jet_elements_indexed_ptr.v').read()
out = sys.argv[1]

def rep(s, a, b, n=1):
    assert s.count(a) == n, (s.count(a), a)
    return s.replace(a, b)

i = src.index('From Coq'); j = src.index('Lemma out_sep_range')
hdr = src[i:j].replace('C.jet_elements_env_load C.jet_elements_indexed_scalar.',
                       'C.jet_elements_env_load C.jet_elements_indexed_scalar C.jet_elements_indexed_ptr.')
assert 'C.jet_elements_indexed_ptr.' in hdr
k = src.index('Lemma elements_indexed_ptr_mid')
body = src[k:]

# --- names
body = rep(body, 'elements_indexed_ptr_mid', 'elements_indexed_gen_mid', 2)
body = rep(body, 'elements_indexed_ptr_local', 'elements_indexed_gen_local')
# --- parameters (both statements)
body = rep(body, '''    (tp cp t3 t4 countfield arrfield sid cid : ident) (pt : type)
    (cdelta adelta sz poff psz : Z) (pexpr : expr) (cf f : function)
''', '''    (tp cp countfield : ident) (cdelta adelta sz : Z) (then_s : statement) (f : function)
''', 2)
body = rep(body, '''    (Ht3i : t3 <> _i) (Ht3d : t3 <> _dst) (Ht4i : t4 <> _i) (Ht4d : t4 <> _dst)
''', '', 2)
body = rep(body, '''    (Hpty : typeof pexpr = tptr pt)
    (Hnone : forall bl, (elements_version_locals bl)!cid = None)
    (Hsym : Genv.find_symbol (Clight.genv_genv elements_ge) cid = Some (elements_symbol_block cid))
    (Hfun : Genv.find_funct (Clight.genv_genv elements_ge) (Vptr (elements_symbol_block cid) Ptrofs.zero) =
      Some (Internal cf))
    (Hty : type_of_fundef (Internal cf) =
      Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr pt) Tnil)) tvoid cc_default)
''', '', 2)
body = rep(body, '''    (Haf : elements_field_at _elementsTransaction arrfield adelta)
''', '', 2)
body = rep(body, '''    (Hsz : 0 < sz <= 1000) (Hpoff : 0 <= poff /\\ poff + psz <= sz)
''', '''    (Hsz : 0 < sz <= 1000)
''', 2)
body = rep(body, 'o + size_chunk chunk <= ofs + psz ->', 'o + size_chunk chunk <= ofs + sz ->', 2)
THEN = '''forall bl le' mb x be ebase bt txbase bin inbase r cur,
      le'!_i = Some (Vlong r) -> le'!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
      le'!_env = Some (Vptr be (Ptrofs.repr ebase)) ->
      0 <= ebase -> ebase + 88 <= Ptrofs.max_unsigned ->
      0 <= txbase -> txbase + 760 <= Ptrofs.max_unsigned ->
      0 <= inbase -> inbase + sz * Int64.unsigned r + sz <= Ptrofs.max_unsigned ->
      Mem.load Mptr mb be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) ->
      Mem.load Mptr mb bt (txbase + adelta) = Some (Vptr bin (Ptrofs.repr inbase)) ->
      elemrep mb bin (inbase + sz * Int64.unsigned r) x ->
      out_sep bd dbase bw outedge cur nbits be ebase (ebase + 8) ->
      out_sep bd dbase bw outedge cur nbits bt (txbase + adelta) (txbase + adelta + 8) ->
      out_sep bd dbase bw outedge cur nbits bin (inbase + sz * Int64.unsigned r)
        (inbase + sz * Int64.unsigned r + sz) ->
      write_frame_at mb bd dbase bw outedge cur nbits ->
      exists le'' me,
        Clight2.exec_stmt elements_ge (elements_version_locals bl) le' mb then_s E0 le'' me Out_normal /\\
        write_effect mb me bd dbase bw outedge cur nbits (pcells x)'''
# mid: Hpay/Hptr -> Hthen
body = rep(body, '''    (Hpay : forall m' bin ofs x cur, elemrep m' bin ofs x -> 0 <= ofs -> ofs + psz <= Ptrofs.max_unsigned ->
      out_sep bd dbase bw outedge cur nbits bin ofs (ofs + psz) ->
      write_frame_at m' bd dbase bw outedge cur nbits ->
      exists me, Clight2.eval_funcall elements_ge m' (Internal cf)
        [Vptr bd (Ptrofs.repr dbase); Vptr bin (Ptrofs.repr ofs)] E0 me Vundef /\\
        write_effect m' me bd dbase bw outedge cur nbits (pcells x))
    (Hptr : forall e le' m' bin inbase r,
      le'!t4 = Some (Vptr bin (Ptrofs.repr inbase)) -> le'!_i = Some (Vlong r) ->
      0 <= inbase -> inbase + sz * Int64.unsigned r + poff + psz <= Ptrofs.max_unsigned ->
      eval_expr elements_ge e le' m' pexpr (Vptr bin (Ptrofs.repr (inbase + sz * Int64.unsigned r + poff))))
    m bs sbase''', '    (Hthen : ' + THEN + ')\n    m bs sbase')
# local: Hpay/Hptr -> Hthen
body = rep(body, '''    (Hpay : forall bd dbase bw outedge m' bin ofs x cur, elemrep m' bin ofs x -> 0 <= ofs ->
      ofs + psz <= Ptrofs.max_unsigned ->
      out_sep bd dbase bw outedge cur nbits bin ofs (ofs + psz) ->
      write_frame_at m' bd dbase bw outedge cur nbits ->
      exists me, Clight2.eval_funcall elements_ge m' (Internal cf)
        [Vptr bd (Ptrofs.repr dbase); Vptr bin (Ptrofs.repr ofs)] E0 me Vundef /\\
        write_effect m' me bd dbase bw outedge cur nbits (pcells x))
    (Hptr : forall e le' m' bin inbase r,
      le'!t4 = Some (Vptr bin (Ptrofs.repr inbase)) -> le'!_i = Some (Vlong r) ->
      0 <= inbase -> inbase + sz * Int64.unsigned r + poff + psz <= Ptrofs.max_unsigned ->
      eval_expr elements_ge e le' m' pexpr (Vptr bin (Ptrofs.repr (inbase + sz * Int64.unsigned r + poff))))
''', '    (Hthen : forall bd dbase bw outedge, ' + THEN + ')\n')
# statements
body = rep(body, '(elements_indexed_then_ptr t3 t4 arrfield sid pexpr cid pt) (elements_skip_stmt nbits)',
           'then_s (elements_skip_stmt nbits)', 4)
body = rep(body, 'countfield cdelta (elements_indexed_then_ptr t3 t4 arrfield sid pexpr cid pt)',
           'countfield cdelta then_s')
body = rep(body, 'elemrep m bin (inbase + sz * Z.of_nat j + poff) x) ->', 'elemrep m bin (inbase + sz * Z.of_nat j) x) ->')
body = rep(body, '(indexed_ptr_rep elems_of elemrep sz poff adelta cdelta) spec.', '(indexed_ptr_rep elems_of elemrep sz 0 adelta cdelta) spec.')
# success branch
body = rep(body, '      set (ofs := inbase + sz * Int64.unsigned r + poff).', '      set (ofs := inbase + sz * Int64.unsigned r).')
a = body.index('      assert (HSp : out_sep bd dbase bw outedge (cursor - 1) nbits bin ofs (ofs + psz)).')
b = body.index("      exists le'', me. split; [exact HExec|].")
body = body[:a] + '''      assert (HSp : out_sep bd dbase bw outedge (cursor - 1) nbits bin ofs (ofs + sz)).
      { eapply out_sep_range with (lo := inbase) (hi := inbase + sz * nn); [|slia|slia].
        eapply out_sep_sub with (cursor := cursor) (count := 1 + nbits); [slia|slia|slia|slia|exact S5]. }
      assert (HS1' : out_sep bd dbase bw outedge (cursor - 1) nbits be ebase (ebase + 8)).
      { eapply out_sep_sub with (cursor := cursor) (count := 1 + nbits); [slia|slia|slia|slia|exact S1]. }
      assert (HS4' : out_sep bd dbase bw outedge (cursor - 1) nbits bt (txbase + adelta) (txbase + adelta + 8)).
      { eapply out_sep_sub with (cursor := cursor) (count := 1 + nbits); [slia|slia|slia|slia|exact S4]. }
      destruct (Hthen bl le' mb x be ebase bt txbase bin inbase r (cursor - 1) Hi Hd He
        He0 He1 Ht0 Ht1 Hi0 ltac:(slia) Hmb0 Hmb1 Hrepb HS1' HS4' HSp HFb) as (le'' & me & HExec & E2).
''' + body[b:]
# local proof body
body = rep(body, '''    (elements_indexed_gen_mid (elems_of environment) nbits pcells elemrep tp cp t3 t4 countfield arrfield sid cid
      pt cdelta adelta sz poff psz pexpr cf f Htp Hcp Ht3i Ht3d Ht4i Ht4d Hnb Hlen Hpty Hnone Hsym Hfun Hty
      Hcf Haf Hcb Hab Hsz Hpoff Hpres bd dbase bw outedge (Hpay bd dbase bw outedge) Hptr
      m bs sbase bi edge cursor read_cursor a be ebase bt txbase bin inbase nI bytes He0 He1 Ht0 Ht1 Hi0 Hi1
      HLtx HLin HLn HnI HLelem S1 S4 S5''', '''    (elements_indexed_gen_mid (elems_of environment) nbits pcells elemrep tp cp countfield
      cdelta adelta sz then_s f Htp Hcp Hnb Hlen
      Hcf Hcb Hab Hsz Hpres bd dbase bw outedge (Hthen bd dbase bw outedge)
      m bs sbase bi edge cursor read_cursor a be ebase bt txbase bin inbase nI bytes He0 He1 Ht0 Ht1 Hi0 Hi1
      HLtx HLin HLn HnI (fun j x Hj => eq_rect _ (fun o => elemrep m bin o x) (HLelem j x Hj) _ (Z.add_0_r _)) S1 S4 S5''')
doc = '''(** GENERATED by C/gen-elements-indexed-gen.py from [jet_elements_indexed_ptr];
    do not edit.

    Generic proof of the indexed Elements getters: [i = read32(src)], a bounds
    bit, then an arbitrary statement on the selected element, or padding.
    The consumer supplies the element representation, its cells and the
    contract of the success statement. *)
'''
open(out, 'w').write(doc + hdr + body)
