(** "Current input" Bitcoin getters whose payload is written by a
    pointer-taking Bitcoin helper (current_prev_outpoint):
      if (env->tx->COUNT <= env->ix) return false;
      HELPER(dst, &env->tx->ARRAY[env->ix].FIELD);  return true; *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_sep C.jet_frame_copy C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_encoding.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage.
Require C.jets.
Require Import C.jet_bitcoin_version_exec C.jet_bitcoin_field_eval C.jet_bitcoin_transport C.jet_bitcoin_call.
Require Import C.jet_bitcoin_wrapper C.jet_bitcoin_effects C.jet_bitcoin_indexed_exec C.jet_bitcoin_current_exec.
Require Import C.jet_bitcoin_indexed_scalar C.jet_bitcoin_indexed_ptr.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque bitcoin_ge ge0.
Set Default Timeout 60.

Definition bitcoin_current_ptr_rest (t1 t2 t3 ta tb tc arrfield countfield sid : ident) (pexpr : expr)
    (cid : ident) (pt : type) : statement :=
  Ssequence
    (Ssequence (Sset ta bitcoin_env_tx_expr)
      (Ssequence
        (Sset tb (Efield (Ederef (Etempvar ta (tptr (Tstruct _bitcoinTransaction noattr)))
          (Tstruct _bitcoinTransaction noattr)) countfield tulong))
        (Ssequence (Sset tc bitcoin_env_ix_expr)
          (Sifthenelse (Ebinop Ole (Etempvar tb tulong) (Etempvar tc tulong) tint)
            (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip))))
    (Ssequence
      (Ssequence (Sset t1 bitcoin_env_tx_expr)
        (Ssequence
          (Sset t2 (Efield (Ederef (Etempvar t1 (tptr (Tstruct _bitcoinTransaction noattr)))
            (Tstruct _bitcoinTransaction noattr)) arrfield (tptr (Tstruct sid noattr))))
          (Ssequence (Sset t3 bitcoin_env_ix_expr)
            (Scall None
              (Evar cid (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr pt) Tnil)) tvoid cc_default))
              [Etempvar _dst (tptr (Tstruct _frameItem noattr)); pexpr]))))
      (Sreturn (Some (Econst_int (Int.repr 1) tint)))).

Ltac gsoc2 := rewrite PTree.gso by (first [assumption | apply not_eq_sym; assumption | discriminate]).

Lemma exec_bitcoin_current_ptr_rest e le0 t1 t2 t3 ta tb tc arrfield countfield sid pexpr cid pt cf pofs
    cdelta adelta mc me be ebase bt txbase bin inbase bd dbase nI ixv :
  ta <> _env -> tb <> _env -> tc <> _env -> t1 <> _env -> t2 <> _env -> t3 <> _env ->
  t1 <> _dst -> t2 <> _dst -> t3 <> _dst -> ta <> _dst -> tb <> _dst -> tc <> _dst ->
  tc <> tb -> t3 <> t2 -> typeof pexpr = tptr pt ->
  e!cid = None ->
  Genv.find_symbol (Clight.genv_genv bitcoin_ge) cid = Some (bitcoin_symbol_block cid) ->
  Genv.find_funct (Clight.genv_genv bitcoin_ge) (Vptr (bitcoin_symbol_block cid) Ptrofs.zero) = Some (Internal cf) ->
  type_of_fundef (Internal cf) = Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr pt) Tnil)) tvoid cc_default ->
  le0!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le0!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  0 <= ebase -> ebase + 56 <= Ptrofs.max_unsigned ->
  0 <= txbase -> 0 <= cdelta -> txbase + cdelta + 8 <= Ptrofs.max_unsigned ->
  0 <= adelta -> txbase + adelta + 8 <= Ptrofs.max_unsigned ->
  bitcoin_field_at _bitcoinTransaction countfield cdelta ->
  bitcoin_field_at _bitcoinTransaction arrfield adelta ->
  Mem.load Mptr mc be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) ->
  Mem.load Mint64 mc bt (txbase + cdelta) = Some (Vlong nI) ->
  Mem.load Mint64 mc be (ebase + 48) = Some (Vlong ixv) ->
  Mem.load Mptr mc bt (txbase + adelta) = Some (Vptr bin (Ptrofs.repr inbase)) ->
  Int64.ltu ixv nI = true ->
  (forall le', le'!t2 = Some (Vptr bin (Ptrofs.repr inbase)) -> le'!t3 = Some (Vlong ixv) ->
    eval_expr bitcoin_ge e le' mc pexpr (Vptr bin (Ptrofs.repr pofs))) ->
  Clight2.eval_funcall bitcoin_ge mc (Internal cf)
    [Vptr bd (Ptrofs.repr dbase); Vptr bin (Ptrofs.repr pofs)] E0 me Vundef ->
  exists le1, Clight2.exec_stmt bitcoin_ge e le0 mc
    (bitcoin_current_ptr_rest t1 t2 t3 ta tb tc arrfield countfield sid pexpr cid pt) E0 le1 me bitcoin_returned_one.
Proof.
  intros Ha Hb Hc H1 H2 H3 H1d H2d H3d Had Hbd Hcd Hcb H32 Hpty He Hsym Hfun Hty HEnv HDst He0 He1 Ht0
    Hc0 HcM Ha0 HaM HFc HFa Hl_tx Hl_cnt Hl_ix Hl_arr Hlt Hptr Hcall.
  set (la_a := PTree.set ta (Vptr bt (Ptrofs.repr txbase)) le0).
  set (la_b := PTree.set tb (Vlong nI) la_a).
  set (la_c := PTree.set tc (Vlong ixv) la_b).
  set (lb1 := PTree.set t1 (Vptr bt (Ptrofs.repr txbase)) la_c).
  set (lb2 := PTree.set t2 (Vptr bin (Ptrofs.repr inbase)) lb1).
  set (lb3 := PTree.set t3 (Vlong ixv) lb2).
  assert (HEa : la_a!_env = Some (Vptr be (Ptrofs.repr ebase))) by (unfold la_a; gsoc2; exact HEnv).
  assert (HEb : la_b!_env = Some (Vptr be (Ptrofs.repr ebase))) by (unfold la_b; gsoc2; exact HEa).
  assert (HEc : la_c!_env = Some (Vptr be (Ptrofs.repr ebase))) by (unfold la_c; gsoc2; exact HEb).
  assert (HE1 : lb1!_env = Some (Vptr be (Ptrofs.repr ebase))) by (unfold lb1; gsoc2; exact HEc).
  assert (HE2 : lb2!_env = Some (Vptr be (Ptrofs.repr ebase))) by (unfold lb2; gsoc2; exact HE1).
  eexists. unfold bitcoin_current_ptr_rest.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := la_c).
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := la_a).
    + apply exec_set. eapply eval_bitcoin_env_tx_expr; [exact HEnv|exact He0|lia|exact Hl_tx].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := la_b).
      * apply exec_set.
        eapply eval_bitcoin_field_value with (sid := _bitcoinTransaction) (delta := cdelta) (chunk := Mint64).
        -- reflexivity.
        -- exact HFc.
        -- reflexivity.
        -- apply eval_bitcoin_deref_struct. unfold la_a. apply PTree.gss.
        -- rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact Hl_cnt].
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := la_c).
        -- apply exec_set. eapply eval_bitcoin_env_ix; [exact HEb|exact He0|exact He1|exact Hl_ix].
        -- eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
           ++ eapply eval_Ebinop with (v1 := Vlong nI) (v2 := Vlong ixv).
              ** apply eval_Etempvar. unfold la_c. gsoc2. apply PTree.gss.
              ** apply eval_Etempvar. unfold la_c. apply PTree.gss.
              ** change (Some (Val.of_bool (negb (Int64.ltu ixv nI))) = Some (Vint Int.zero)).
                 rewrite Hlt. reflexivity.
           ++ reflexivity.
           ++ apply exec_Sskip.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me) (le1 := lb3); [|apply exec_Sreturn_some, eval_Econst_int].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := lb1).
    + apply exec_set. eapply eval_bitcoin_env_tx_expr; [exact HEc|exact He0|lia|exact Hl_tx].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := lb2).
      * apply exec_set.
        eapply eval_bitcoin_field_value with (sid := _bitcoinTransaction) (delta := adelta) (chunk := Mptr).
        -- reflexivity.
        -- exact HFa.
        -- reflexivity.
        -- apply eval_bitcoin_deref_struct. unfold lb1. apply PTree.gss.
        -- rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact Hl_arr].
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := lb3).
        -- apply exec_set. eapply eval_bitcoin_env_ix; [exact HE2|exact He0|exact He1|exact Hl_ix].
        -- eapply exec_Scall with (vf := Vptr (bitcoin_symbol_block cid) Ptrofs.zero) (f := Internal cf)
             (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr bin (Ptrofs.repr pofs)]) (vres := Vundef).
           ++ reflexivity.
           ++ eapply eval_Elvalue; [apply eval_Evar_global; [exact He|exact Hsym]|apply deref_loc_reference; reflexivity].
           ++ eapply eval_Econs.
              ** apply eval_Etempvar. unfold lb3, lb2, lb1, la_c, la_b, la_a. gsoc2. gsoc2. gsoc2. gsoc2. gsoc2.
                 gsoc2. exact HDst.
              ** reflexivity.
              ** eapply eval_Econs.
                 --- apply Hptr; [unfold lb3; gsoc2; apply PTree.gss|unfold lb3; apply PTree.gss].
                 --- rewrite Hpty. reflexivity.
                 --- apply eval_Enil.
           ++ exact Hfun.
           ++ exact Hty.
           ++ exact Hcall.
Qed.
