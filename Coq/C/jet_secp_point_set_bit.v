(** Original field set_int(0/1) on a slice of one owned point allocation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep C.jet_sx_pure
  C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_fe_nv C.jet_secp_local_regions
  C.jet_secp_b32_exec C.jet_secp_point_write_run C.jet_secp_point_write_preservation
  C.jet_secp_owned_slice_fields C.jet_secp_multiply_normalize_bridge.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition point_set_holes k := map (fun i => mkcell (point_coordinate_offset k+8*i) Mint64 None) [0;1;2;3;4].
Definition point_set_regs k := [mkreg (point_set_holes k) true (Some 128)].
Definition point_set_bit_run k (bit : bool) := xfun (genv_cenv secp_ge) [] (int_table secp_pure) 100
  f_secp256k1_fe_set_int [XP 0 (point_coordinate_offset k);XI (if bit then Int.one else Int.zero)] (point_set_regs k) [] 0.
Definition point_set_bit_tree := Eval vm_compute in fun k bit => match k,bit with
  | PointX,true => point_set_bit_run PointX true | PointY,true => point_set_bit_run PointY true
  | PointZ,true => point_set_bit_run PointZ true | PointX,false => point_set_bit_run PointX false
  | PointY,false => point_set_bit_run PointY false | PointZ,false => point_set_bit_run PointZ false end.
Definition point_set_bit_state k bit := match point_set_bit_tree k bit with
  | Some (RIf _ (RDone st _) _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition point_set_bit_cond (bit : bool) := XIcmp Cle Signed (XIc Int.zero) (XI (if bit then Int.one else Int.zero)).
Definition point_set_bit_out (bit : bool) :=
  [XI2L Signed (XI (if bit then Int.one else Int.zero));
   XI2L Signed (XIc Int.zero);XI2L Signed (XIc Int.zero);XI2L Signed (XIc Int.zero);XI2L Signed (XIc Int.zero)].
Definition point_set_bit_words (bit : bool) (i : nat) := if Nat.eqb i 0 then (if bit then Int64.one else Int64.zero) else Int64.zero.
Lemma point_set_bit_run_eq k bit : point_set_bit_run k bit=Some
  (RIf (point_set_bit_cond bit) (RDone (point_set_bit_state k bit) ONormal) (RDone (point_set_bit_state k bit) ONormal)).
Proof. destruct k,bit;reflexivity. Qed.
Lemma point_set_bit_selected k bit rho beta :
  rsel rho (lay beta) (RIf (point_set_bit_cond bit)
    (RDone (point_set_bit_state k bit) ONormal) (RDone (point_set_bit_state k bit) ONormal))=
    (point_set_bit_state k bit,ONormal).
Proof. cbn [rsel];destruct (truth rho (lay beta) (point_set_bit_cond bit));reflexivity. Qed.
Lemma point_set_bit_return k bit : (stemps (point_set_bit_state k bit))!1%positive=None.
Proof. destruct k,bit;reflexivity. Qed.
Lemma point_set_bit_output k bit : sregs (point_set_bit_state k bit)=
  [mkreg (u64_cells (point_coordinate_offset k) (point_set_bit_out bit)) true (Some 128)].
Proof. destruct k,bit;reflexivity. Qed.
Lemma point_set_bit_log k bit : slog (point_set_bit_state k bit)=[].
Proof. destruct k,bit;reflexivity. Qed.
Lemma point_set_shape k : map rshape (point_set_regs k)=map rshape (point_write_initial_regs k).
Proof. destruct k;reflexivity. Qed.

Lemma point_set_initial k rho m b : Mem.range_perm m b 0 128 Cur Freeable ->
  rep rho [(b,0)] (point_set_regs k) m.
Proof.
  intro HF;apply (rep_add _ [] [] m b 0);[apply rep_nil|cbn;tauto|].
  unfold point_set_regs;cbn [hd].
  unfold region_ok;cbn [rcells rw rfree bas blk lay nth fst snd length app].
  split;[lia|];split;[eapply Mem.perm_valid_block;apply (HF 0);lia|].
  split;[destruct k;reflexivity|];split.
  - apply Forall_forall;intros c HC;destruct k;
      cbn [point_set_holes point_coordinate_offset map In] in HC;
      repeat match type of HC with _ \/ _ => destruct HC as [HC|HC] end;
      try contradiction;subst c;apply writable_undefined_cell;
      cbn [bas blk lay nth fst snd size_chunk align_chunk];
      try (change Ptrofs.max_unsigned with 18446744073709551615;lia).
    all: try (apply freeable_range_writable;intros pos HP;apply HF;lia).
    all: match goal with |- (8|?n) => exists (n/8);reflexivity end.
  - split;[reflexivity|];split;[reflexivity|];split;[exact HF|].
    destruct k;repeat constructor;cbn;lia.
Qed.

Theorem eval_point_set_bit k (bit : bool) m b : Mem.range_perm m b 0 128 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_set_int)
    [Vptr b (Ptrofs.repr (point_coordinate_offset k));Vint (if bit then Int.one else Int.zero)] E0 mf Vundef /\
  fe_at mf b (point_coordinate_offset k) (words5 (point_set_bit_words bit)) /\
  Mem.range_perm mf b 0 128 Cur Freeable /\
  lframe (fun bx pos => bx<>b \/ pos<point_coordinate_offset k \/ point_coordinate_offset k+40<=pos) m mf.
Proof.
  intro HF;set (rho:=fun _ : nat => Int64.zero).
  assert (HLog : leaves_log_nil (RIf (point_set_bit_cond bit)
      (RDone (point_set_bit_state k bit) ONormal) (RDone (point_set_bit_state k bit) ONormal))=true)
    by (cbn [leaves_log_nil];rewrite point_set_bit_log;reflexivity).
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 100 f_secp256k1_fe_set_int
    [XP 0 (point_coordinate_offset k);XI (if bit then Int.one else Int.zero)] (point_set_regs k) 0 _
    (point_set_bit_run_eq k bit) HLog rho [(b,0)] m (point_set_initial k rho m b HF))
    as (mf & result & HC & HP & HV & HS & HL).
  rewrite point_set_bit_selected in HP,HV;cbn [fst] in HP,HV.
  rewrite point_set_bit_return in HV;subst result.
  rewrite point_set_bit_output in HP.
  pose proof (rep_region _ _ _ mf 0 _ HP eq_refl) as HR.
  pose proof HR as (_ & _ & _ & _ & _ & _ & HFree & _).
  assert (HField : fe_at mf b (point_coordinate_offset k) (words5 (point_set_bit_words bit))).
  { eapply owned_region_field_slice with (rho:=rho) (beta:=[(b,0)]) (r:=0%nat) (size:=128) (exprs:=point_set_bit_out bit).
    - exact HR.
    - pose proof (point_coordinate_offset_bounds k);lia.
    - destruct k;cbn;[exists 0|exists 5|exists 10];reflexivity.
    - pose proof (point_coordinate_offset_bounds k);lia.
    - change (128<=18446744073709551615);lia.
    - reflexivity.
    - reflexivity.
    - intros c HH;exact HH.
    - destruct bit;reflexivity. }
  exists mf;split;[exact HC|];split;[exact HField|];split;[exact HFree|].
  rewrite point_set_shape in HL;eapply lframe_implies;[exact HL|].
  intros bx pos HO HV HFoot.
  destruct (point_write_foot_bounds k b bx pos HFoot) as [HE HP'];subst bx.
  destruct HO as [HN|[HN|HN]];[contradiction|lia|lia].
Qed.
