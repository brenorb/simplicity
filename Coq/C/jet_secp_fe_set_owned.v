(** Original field set_int(0/1) on one whole owned 40-byte field block. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep C.jet_sx_pure
  C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_fe_nv C.jet_secp_local_regions
  C.jet_secp_b32_exec C.jet_secp_point_write_run C.jet_secp_point_write_preservation
  C.jet_secp_owned_slice_fields C.jet_secp_multiply_normalize_bridge C.jet_secp_point_set_bit.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition fe_set_holes := map (fun i => mkcell (8*i) Mint64 None) [0;1;2;3;4].
Definition fe_set_regs := [mkreg fe_set_holes true (Some 40)].
Definition fe_set_run (bit : bool) := xfun (genv_cenv secp_ge) [] (int_table secp_pure) 100
  f_secp256k1_fe_set_int [XP 0 0;XI (if bit then Int.one else Int.zero)] fe_set_regs [] 0.
Definition fe_set_tree := Eval vm_compute in fun bit => match bit with
  | true => fe_set_run true | false => fe_set_run false end.
Definition fe_set_state (bit : bool) := match fe_set_tree bit with
  | Some (RIf _ (RDone st _) _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition fe_set_out (bit : bool) :=
  [XI2L Signed (XI (if bit then Int.one else Int.zero));
   XI2L Signed (XIc Int.zero);XI2L Signed (XIc Int.zero);XI2L Signed (XIc Int.zero);XI2L Signed (XIc Int.zero)].
Lemma fe_set_run_eq bit : fe_set_run bit=Some
  (RIf (point_set_bit_cond bit) (RDone (fe_set_state bit) ONormal) (RDone (fe_set_state bit) ONormal)).
Proof. destruct bit;reflexivity. Qed.
Lemma fe_set_selected bit rho beta :
  rsel rho (lay beta) (RIf (point_set_bit_cond bit)
    (RDone (fe_set_state bit) ONormal) (RDone (fe_set_state bit) ONormal))=
    (fe_set_state bit,ONormal).
Proof. cbn [rsel];destruct (truth rho (lay beta) (point_set_bit_cond bit));reflexivity. Qed.
Lemma fe_set_return bit : (stemps (fe_set_state bit))!1%positive=None.
Proof. destruct bit;reflexivity. Qed.
Lemma fe_set_output bit : sregs (fe_set_state bit)=
  [mkreg (u64_cells 0 (fe_set_out bit)) true (Some 40)].
Proof. destruct bit;reflexivity. Qed.
Lemma fe_set_log bit : slog (fe_set_state bit)=[].
Proof. destruct bit;reflexivity. Qed.

Lemma fe_set_initial rho m b : Mem.range_perm m b 0 40 Cur Freeable ->
  rep rho [(b,0)] fe_set_regs m.
Proof.
  intro HF;apply (rep_add _ [] [] m b 0);[apply rep_nil|cbn;tauto|].
  unfold fe_set_regs;cbn [hd].
  unfold region_ok;cbn [rcells rw rfree bas blk lay nth fst snd length app].
  split;[lia|];split;[eapply Mem.perm_valid_block;apply (HF 0);lia|].
  split;[reflexivity|];split.
  - apply Forall_forall;intros c HC;
      cbn [fe_set_holes map In] in HC;
      repeat match type of HC with _ \/ _ => destruct HC as [HC|HC] end;
      try contradiction;subst c;apply writable_undefined_cell;
      cbn [bas blk lay nth fst snd size_chunk align_chunk];
      try (change Ptrofs.max_unsigned with 18446744073709551615;lia).
    all: try (apply freeable_range_writable;intros pos HP;apply HF;lia).
    all: match goal with |- (8|?n) => exists (n/8);reflexivity end.
  - split;[reflexivity|];split;[reflexivity|];split;[exact HF|].
    repeat constructor;cbn;lia.
Qed.

Theorem eval_fe_set_owned (bit : bool) m b : Mem.range_perm m b 0 40 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_set_int)
    [Vptr b (Ptrofs.repr 0);Vint (if bit then Int.one else Int.zero)] E0 mf Vundef /\
  fe_at mf b 0 (words5 (point_set_bit_words bit)) /\
  Mem.range_perm mf b 0 40 Cur Freeable /\
  lframe (fun bx _ => bx<>b) m mf.
Proof.
  intro HF;set (rho:=fun _ : nat => Int64.zero).
  assert (HLog : leaves_log_nil (RIf (point_set_bit_cond bit)
      (RDone (fe_set_state bit) ONormal) (RDone (fe_set_state bit) ONormal))=true)
    by (cbn [leaves_log_nil];rewrite fe_set_log;reflexivity).
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 100 f_secp256k1_fe_set_int
    [XP 0 0;XI (if bit then Int.one else Int.zero)] fe_set_regs 0 _
    (fe_set_run_eq bit) HLog rho [(b,0)] m (fe_set_initial rho m b HF))
    as (mf & result & HC & HP & HV & HS & HL).
  rewrite fe_set_selected in HP,HV;cbn [fst] in HP,HV.
  rewrite fe_set_return in HV;subst result.
  rewrite fe_set_output in HP.
  pose proof (rep_region _ _ _ mf 0 _ HP eq_refl) as HR.
  pose proof HR as (_ & _ & _ & _ & _ & _ & HFree & _).
  assert (HField : fe_at mf b 0 (words5 (point_set_bit_words bit))).
  { eapply owned_region_field_slice with (rho:=rho) (beta:=[(b,0)]) (r:=0%nat) (size:=40) (exprs:=fe_set_out bit).
    - exact HR.
    - lia.
    - exists 0;reflexivity.
    - lia.
    - change (40<=18446744073709551615);lia.
    - reflexivity.
    - reflexivity.
    - intros c HH;exact HH.
    - destruct bit;reflexivity. }
  exists mf;split;[exact HC|];split;[exact HField|];split;[exact HFree|].
  eapply lframe_implies;[exact HL|].
  intros bx pos HO HV' (r & s & d & ch & HN & HC' & HB & HR');
    destruct r as [|r];[|destruct r;discriminate].
  apply HO;exact HB.
Qed.
