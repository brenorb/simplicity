(** Success statements of indexed Elements getters that call two pointer-taking
    helpers on the selected element (asset then amount). *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine C.jet_elements_prim.
Require Import C.jet_application_sep C.jet_frame_copy C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_output_slice.
Require Import C.jet_wide C.jet_wide_spec C.jet_encoding C.jet_input_layout C.jet_output_layout_step.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_version_exec C.jet_exec.
Require C.jets.
Require Import C.jet_elements_field_eval C.jet_elements_effects C.jet_elements_wrapper.
Require Import C.jet_elements_transport C.jet_elements_call C.jet_elements_read_step C.jet_elements_steps.
Require Import C.jet_elements_index_eval C.jet_elements_indexed_exec C.jet_elements_indexed_ptr_then.
Require Import C.jet_elements_env_load C.jet_elements_indexed_scalar C.jet_elements_indexed_ptr C.jet_elements_indexed_gen.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge ge0.
Set Default Timeout 60.

Ltac gsop := rewrite PTree.gso by (first [assumption | apply not_eq_sym; assumption | discriminate]).

Lemma exec_elements_indexed_then_ptr_le e le t3 t4 arrfield adelta sid pexpr cid pt cf pofs
    mb me be ebase bt txbase bin inbase bd dbase r :
  t3 <> _i -> t3 <> _dst -> t4 <> _i -> t4 <> _dst -> typeof pexpr = tptr pt ->
  e!cid = None ->
  Genv.find_symbol (Clight.genv_genv elements_ge) cid = Some (elements_symbol_block cid) ->
  Genv.find_funct (Clight.genv_genv elements_ge) (Vptr (elements_symbol_block cid) Ptrofs.zero) = Some (Internal cf) ->
  type_of_fundef (Internal cf) = Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr pt) Tnil)) tvoid cc_default ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_i = Some (Vlong r) ->
  0 <= ebase -> ebase + 8 <= Ptrofs.max_unsigned ->
  0 <= txbase -> 0 <= adelta -> txbase + adelta + 8 <= Ptrofs.max_unsigned ->
  elements_field_at _elementsTransaction arrfield adelta ->
  Mem.load Mptr mb be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) ->
  Mem.load Mptr mb bt (txbase + adelta) = Some (Vptr bin (Ptrofs.repr inbase)) ->
  (forall le', le'!t4 = Some (Vptr bin (Ptrofs.repr inbase)) -> le'!_i = Some (Vlong r) ->
    eval_expr elements_ge e le' mb pexpr (Vptr bin (Ptrofs.repr pofs))) ->
  Clight2.eval_funcall elements_ge mb (Internal cf)
    [Vptr bd (Ptrofs.repr dbase); Vptr bin (Ptrofs.repr pofs)] E0 me Vundef ->
  Clight2.exec_stmt elements_ge e le mb (elements_indexed_then_ptr t3 t4 arrfield sid pexpr cid pt)
    E0 (PTree.set t4 (Vptr bin (Ptrofs.repr inbase)) (PTree.set t3 (Vptr bt (Ptrofs.repr txbase)) le)) me Out_normal.
Proof.
  intros Ht3i Ht3d Ht4i Ht4d Hpty He Hsym Hfun Hty HEnv HDst HI He0 He1 Ht0 Ha0 HaM HF Hl1 Hl2 Hptr Hcall.
  set (le_a := PTree.set t3 (Vptr bt (Ptrofs.repr txbase)) le).
  set (le_b := PTree.set t4 (Vptr bin (Ptrofs.repr inbase)) le_a).
  change (PTree.set t4 (Vptr bin (Ptrofs.repr inbase)) (PTree.set t3 (Vptr bt (Ptrofs.repr txbase)) le)) with le_b.
  unfold elements_indexed_then_ptr.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := le_a).
  - apply exec_set.
    eapply eval_elements_field_value with (sid := _txEnv) (delta := 0) (chunk := Mptr).
    + reflexivity.
    + exact elements_txEnv_tx.
    + reflexivity.
    + apply eval_elements_deref_struct; exact HEnv.
    + rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact Hl1].
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := le_b).
    + apply exec_set.
      eapply eval_elements_field_value with (sid := _elementsTransaction) (delta := adelta) (chunk := Mptr).
      * reflexivity.
      * exact HF.
      * reflexivity.
      * apply eval_elements_deref_struct. unfold le_a. apply PTree.gss.
      * rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact Hl2].
    + eapply exec_Scall with (vf := Vptr (elements_symbol_block cid) Ptrofs.zero) (f := Internal cf)
        (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr bin (Ptrofs.repr pofs)]) (vres := Vundef).
      * reflexivity.
      * eapply eval_Elvalue; [apply eval_Evar_global; [exact He|exact Hsym]|apply deref_loc_reference; reflexivity].
      * eapply eval_Econs; [apply eval_Etempvar; unfold le_b, le_a; gsop; gsop; exact HDst|reflexivity|].
        eapply eval_Econs.
        -- apply Hptr; [unfold le_b; apply PTree.gss|unfold le_b, le_a; gsop; gsop; exact HI].
        -- rewrite Hpty. reflexivity.
        -- apply eval_Enil.
      * exact Hfun.
      * exact Hty.
      * exact Hcall.
Qed.

(** Two helper calls on the selected element, each preceded by its own
    reload of [env->tx] and of the array pointer. *)
Definition elements_indexed_then_ptr2 (ta3 ta4 t3 t4 arrfield sid : ident)
    (pexpr1 : expr) (cid1 : ident) (pt1 : type) (pexpr2 : expr) (cid2 : ident) (pt2 : type) : statement :=
  Ssequence (elements_indexed_then_ptr ta3 ta4 arrfield sid pexpr1 cid1 pt1)
    (elements_indexed_then_ptr t3 t4 arrfield sid pexpr2 cid2 pt2).

Lemma exec_elements_indexed_then_ptr2 {A} (n1 n2 : Z) (pcells1 pcells2 : A -> list Cell)
    (elemrep : mem -> block -> Z -> A -> Prop)
    (ta3 ta4 t3 t4 arrfield sid cid1 cid2 : ident) (pt1 pt2 : type)
    (adelta sz poff1 poff2 : Z) (pexpr1 pexpr2 : expr) (cf1 cf2 : function)
    (Hta3 : ta3 <> _i /\ ta3 <> _dst /\ ta3 <> _env) (Hta4 : ta4 <> _i /\ ta4 <> _dst /\ ta4 <> _env)
    (Ht3 : t3 <> _i /\ t3 <> _dst) (Ht4 : t4 <> _i /\ t4 <> _dst)
    (Hn1 : 0 < n1) (Hn2 : 0 < n2) (Hlen1 : forall x, Z.of_nat (length (pcells1 x)) = n1)
    (Hpty1 : typeof pexpr1 = tptr pt1) (Hpty2 : typeof pexpr2 = tptr pt2)
    (Hnone1 : forall bl, (elements_version_locals bl)!cid1 = None)
    (Hnone2 : forall bl, (elements_version_locals bl)!cid2 = None)
    (Hsym1 : Genv.find_symbol (Clight.genv_genv elements_ge) cid1 = Some (elements_symbol_block cid1))
    (Hfun1 : Genv.find_funct (Clight.genv_genv elements_ge) (Vptr (elements_symbol_block cid1) Ptrofs.zero) =
      Some (Internal cf1))
    (Hty1 : type_of_fundef (Internal cf1) =
      Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr pt1) Tnil)) tvoid cc_default)
    (Hsym2 : Genv.find_symbol (Clight.genv_genv elements_ge) cid2 = Some (elements_symbol_block cid2))
    (Hfun2 : Genv.find_funct (Clight.genv_genv elements_ge) (Vptr (elements_symbol_block cid2) Ptrofs.zero) =
      Some (Internal cf2))
    (Hty2 : type_of_fundef (Internal cf2) =
      Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr pt2) Tnil)) tvoid cc_default)
    (Haf : elements_field_at _elementsTransaction arrfield adelta)
    (Hab : 0 <= adelta /\ adelta + 8 <= 760) (Hsz : 0 < sz <= 1000)
    (Hpres : forall m1 m2 b ofs x, elemrep m1 b ofs x ->
      (forall chunk o v, ofs <= o -> o + size_chunk chunk <= ofs + sz ->
        Mem.load chunk m1 b o = Some v -> Mem.load chunk m2 b o = Some v) -> elemrep m2 b ofs x)
    bd dbase bw outedge
    (Hpay1 : forall m' bin ofs x cur, elemrep m' bin ofs x -> 0 <= ofs -> ofs + sz <= Ptrofs.max_unsigned ->
      out_sep bd dbase bw outedge cur n1 bin ofs (ofs + sz) ->
      write_frame_at m' bd dbase bw outedge cur n1 ->
      exists me, Clight2.eval_funcall elements_ge m' (Internal cf1)
        [Vptr bd (Ptrofs.repr dbase); Vptr bin (Ptrofs.repr (ofs + poff1))] E0 me Vundef /\
        write_effect m' me bd dbase bw outedge cur n1 (pcells1 x))
    (Hpay2 : forall m' bin ofs x cur, elemrep m' bin ofs x -> 0 <= ofs -> ofs + sz <= Ptrofs.max_unsigned ->
      out_sep bd dbase bw outedge cur n2 bin ofs (ofs + sz) ->
      write_frame_at m' bd dbase bw outedge cur n2 ->
      exists me, Clight2.eval_funcall elements_ge m' (Internal cf2)
        [Vptr bd (Ptrofs.repr dbase); Vptr bin (Ptrofs.repr (ofs + poff2))] E0 me Vundef /\
        write_effect m' me bd dbase bw outedge cur n2 (pcells2 x))
    (Hptr1 : forall e le' m' bin inbase r,
      le'!ta4 = Some (Vptr bin (Ptrofs.repr inbase)) -> le'!_i = Some (Vlong r) ->
      0 <= inbase -> inbase + sz * Int64.unsigned r + sz <= Ptrofs.max_unsigned ->
      eval_expr elements_ge e le' m' pexpr1 (Vptr bin (Ptrofs.repr (inbase + sz * Int64.unsigned r + poff1))))
    (Hptr2 : forall e le' m' bin inbase r,
      le'!t4 = Some (Vptr bin (Ptrofs.repr inbase)) -> le'!_i = Some (Vlong r) ->
      0 <= inbase -> inbase + sz * Int64.unsigned r + sz <= Ptrofs.max_unsigned ->
      eval_expr elements_ge e le' m' pexpr2 (Vptr bin (Ptrofs.repr (inbase + sz * Int64.unsigned r + poff2)))) :
  forall bl le' mb x be ebase bt txbase bin inbase r cur,
    le'!_i = Some (Vlong r) -> le'!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
    le'!_env = Some (Vptr be (Ptrofs.repr ebase)) ->
    0 <= ebase -> ebase + 88 <= Ptrofs.max_unsigned ->
    0 <= txbase -> txbase + 760 <= Ptrofs.max_unsigned ->
    0 <= inbase -> inbase + sz * Int64.unsigned r + sz <= Ptrofs.max_unsigned ->
    Mem.load Mptr mb be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) ->
    Mem.load Mptr mb bt (txbase + adelta) = Some (Vptr bin (Ptrofs.repr inbase)) ->
    elemrep mb bin (inbase + sz * Int64.unsigned r) x ->
    out_sep bd dbase bw outedge cur (n1 + n2) be ebase (ebase + 8) ->
    out_sep bd dbase bw outedge cur (n1 + n2) bt (txbase + adelta) (txbase + adelta + 8) ->
    out_sep bd dbase bw outedge cur (n1 + n2) bin (inbase + sz * Int64.unsigned r)
      (inbase + sz * Int64.unsigned r + sz) ->
    write_frame_at mb bd dbase bw outedge cur (n1 + n2) ->
    exists le'' me,
      Clight2.exec_stmt elements_ge (elements_version_locals bl) le' mb
        (elements_indexed_then_ptr2 ta3 ta4 t3 t4 arrfield sid pexpr1 cid1 pt1 pexpr2 cid2 pt2) E0 le'' me Out_normal /\
      write_effect mb me bd dbase bw outedge cur (n1 + n2) (pcells1 x ++ pcells2 x).
Proof.
  intros bl le' mb x be ebase bt txbase bin inbase r cur Hi Hd He He0 He1 Ht0 Ht1 Hi0 HiM Hl0 Hl1 Hrep S1 S4 S5 HF.
  pose proof HF as [_ [_ [_ [HCur _]]]].
  assert (Hr0 : 0 <= Int64.unsigned r) by apply Int64.unsigned_range.
  assert (Hs0 : 0 <= sz * Int64.unsigned r) by (apply Z.mul_nonneg_nonneg; lia).
  set (ofs := inbase + sz * Int64.unsigned r) in *.
  destruct Hta3 as (Ha3i & Ha3d & Ha3e). destruct Hta4 as (Ha4i & Ha4d & Ha4e).
  destruct Ht3 as (H3i & H3d). destruct Ht4 as (H4i & H4d).
  assert (HFa : write_frame_at mb bd dbase bw outedge cur n1).
  { eapply write_frame_at_shorter; [|exact HF]. lia. }
  assert (S5a : out_sep bd dbase bw outedge cur n1 bin ofs (ofs + sz)).
  { eapply out_sep_sub with (cursor := cur) (count := n1 + n2); [lia|lia|lia|lia|exact S5]. }
  destruct (Hpay1 mb bin ofs x cur Hrep ltac:(lia) ltac:(lia) S5a HFa) as (m1 & HC1 & E1).
  set (le1 := PTree.set ta4 (Vptr bin (Ptrofs.repr inbase)) (PTree.set ta3 (Vptr bt (Ptrofs.repr txbase)) le')).
  pose proof (exec_elements_indexed_then_ptr_le (elements_version_locals bl) le' ta3 ta4 arrfield adelta sid
    pexpr1 cid1 pt1 cf1 (ofs + poff1) mb m1 be ebase bt txbase bin inbase bd dbase r
    Ha3i Ha3d Ha4i Ha4d Hpty1 (Hnone1 bl) Hsym1 Hfun1 Hty1 He Hd Hi
    He0 ltac:(lia) Ht0 (proj1 Hab) ltac:(lia) Haf Hl0 Hl1
    (fun le'' H4 HI' => Hptr1 _ le'' mb bin inbase r H4 HI' Hi0 HiM) HC1) as HEx1.
  fold le1 in HEx1.
  assert (HLoad1 : forall chunk b lo hi o, out_sep bd dbase bw outedge cur (n1 + n2) b lo hi ->
    lo <= o -> o + size_chunk chunk <= hi -> Mem.load chunk m1 b o = Mem.load chunk mb b o).
  { intros chunk b lo hi o Hs Hlo Hhi.
    eapply write_effect_env_load with (bf := bd) (base := dbase) (bw := bw) (edge := outedge)
      (cursor := cur) (cursor0 := cur) (count0 := n1 + n2) (n := n1) (cells := pcells1 x) (lo := lo) (hi := hi);
      [lia|lia|lia|lia|exact E1|exact Hs|exact Hlo|exact Hhi]. }
  assert (Hrep1 : elemrep m1 bin ofs x).
  { eapply Hpres; [exact Hrep|]. intros chunk o v Hlo Hhi Hl.
    rewrite (HLoad1 chunk bin ofs (ofs + sz) o S5 Hlo Hhi). exact Hl. }
  assert (Hm0 : Mem.load Mptr m1 be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase))).
  { rewrite (HLoad1 Mptr be ebase (ebase + 8) (ebase + 0) S1 ltac:(lia) ltac:(change (size_chunk Mptr) with 8; lia)).
    exact Hl0. }
  assert (Hm1 : Mem.load Mptr m1 bt (txbase + adelta) = Some (Vptr bin (Ptrofs.repr inbase))).
  { rewrite (HLoad1 Mptr bt (txbase + adelta) (txbase + adelta + 8) (txbase + adelta) S4 ltac:(lia)
      ltac:(change (size_chunk Mptr) with 8; lia)). exact Hl1. }
  assert (HF2 : write_frame_at m1 bd dbase bw outedge (cur - n1) n2).
  { eapply write_frame_at_after_effect with (cells := pcells1 x) (m := mb); [apply Hlen1|lia|exact HF|exact E1]. }
  assert (S5b : out_sep bd dbase bw outedge (cur - n1) n2 bin ofs (ofs + sz)).
  { eapply out_sep_sub with (cursor := cur) (count := n1 + n2); [lia|lia|lia|lia|exact S5]. }
  destruct (Hpay2 m1 bin ofs x (cur - n1) Hrep1 ltac:(lia) ltac:(lia) S5b HF2) as (me & HC2 & E2).
  assert (Hi1 : le1!_i = Some (Vlong r)).
  { unfold le1. rewrite PTree.gso by (apply not_eq_sym; exact Ha4i).
    rewrite PTree.gso by (apply not_eq_sym; exact Ha3i). exact Hi. }
  assert (Hd1 : le1!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
  { unfold le1. rewrite PTree.gso by (apply not_eq_sym; exact Ha4d).
    rewrite PTree.gso by (apply not_eq_sym; exact Ha3d). exact Hd. }
  assert (He1' : le1!_env = Some (Vptr be (Ptrofs.repr ebase))).
  { unfold le1. rewrite PTree.gso by (apply not_eq_sym; exact Ha4e).
    rewrite PTree.gso by (apply not_eq_sym; exact Ha3e). exact He. }
  pose proof (exec_elements_indexed_then_ptr_le (elements_version_locals bl) le1 t3 t4 arrfield adelta sid
    pexpr2 cid2 pt2 cf2 (ofs + poff2) m1 me be ebase bt txbase bin inbase bd dbase r
    H3i H3d H4i H4d Hpty2 (Hnone2 bl) Hsym2 Hfun2 Hty2 He1' Hd1 Hi1
    He0 ltac:(lia) Ht0 (proj1 Hab) ltac:(lia) Haf Hm0 Hm1
    (fun le'' H4 HI' => Hptr2 _ le'' m1 bin inbase r H4 HI' Hi0 HiM) HC2) as HEx2.
  eexists. exists me. split.
  - unfold elements_indexed_then_ptr2.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m1) (le1 := le1); [exact HEx1|exact HEx2].
  - exact (write_effect_seq mb m1 me bd dbase bw outedge cur n1 n2 (pcells1 x) (pcells2 x)
      (Hlen1 x) ltac:(lia) HF E1 E2).
Qed.
