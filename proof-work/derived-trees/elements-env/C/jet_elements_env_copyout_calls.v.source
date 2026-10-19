(** The callees of [copyOutput] with one statement per callee: optional raw
    byte strings ([rawsrc]) and optional buffers ([bufsrc]) cover the NULL
    and non-NULL cases of the accepted theorems. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model C.jet_uint32_array_init.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_add_n_init C.jet_sha_ctx_abs C.jet_sha_be32_exec C.jet_sha_uchars_exec.
Require Import C.jet_elements_env_field_eval C.jet_elements_env_tomidstate C.jet_elements_env_hashbuffer.
Require Import C.jet_elements_env_hashbuffer_empty C.jet_elements_env_readbe64.
Require Import C.jet_elements_env_copyrawamt C.jet_elements_env_copyrawconf C.jet_elements_env_calc_token.
Require Import C.jet_elements_env_isfee C.jet_elements_env_copyout_defs.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Lemma co_sym_hashBuffer :
  Genv.find_symbol (Clight.genv_genv sha_ge) _hashBuffer = Some (sha_symbol_block _hashBuffer).
Proof. vm_compute; reflexivity. Qed.
Lemma co_fun_hashBuffer :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _hashBuffer) Ptrofs.zero) =
    Some (Internal f_hashBuffer).
Proof. vm_compute; reflexivity. Qed.
Lemma co_sym_copyRawConfidential :
  Genv.find_symbol (Clight.genv_genv sha_ge) _copyRawConfidential = Some (sha_symbol_block _copyRawConfidential).
Proof. vm_compute; reflexivity. Qed.
Lemma co_fun_copyRawConfidential :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _copyRawConfidential) Ptrofs.zero) =
    Some (Internal f_copyRawConfidential).
Proof. vm_compute; reflexivity. Qed.
Lemma co_sym_copyRawAmt :
  Genv.find_symbol (Clight.genv_genv sha_ge) _copyRawAmt = Some (sha_symbol_block _copyRawAmt).
Proof. vm_compute; reflexivity. Qed.
Lemma co_fun_copyRawAmt :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _copyRawAmt) Ptrofs.zero) =
    Some (Internal f_copyRawAmt).
Proof. vm_compute; reflexivity. Qed.
Lemma co_sym_parseNullData :
  Genv.find_symbol (Clight.genv_genv sha_ge) _parseNullData = Some (sha_symbol_block _parseNullData).
Proof. vm_compute; reflexivity. Qed.
Lemma co_fun_parseNullData :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _parseNullData) Ptrofs.zero) =
    Some (Internal f_parseNullData).
Proof. vm_compute; reflexivity. Qed.

Local Opaque sha_ge.

(** An optional raw byte string. *)
Inductive rawsrc : Type := RNull | RPtr (b : block) (o : ptrofs).

Definition rs_val (s : rawsrc) : val :=
  match s with RNull => Vlong Int64.zero | RPtr b o => Vptr b o end.

Definition rs_other (s : rawsrc) (b0 : block) : Prop :=
  match s with RNull => True | RPtr b _ => b <> b0 end.

Definition rs_readable (m : mem) (b : block) (o : ptrofs) (n : nat) (bs : list int) : Prop :=
  Ptrofs.unsigned o + Z.of_nat n <= Ptrofs.max_unsigned /\
  forall i, (i < n)%nat ->
    Mem.load Mint8unsigned m b (Ptrofs.unsigned o + Z.of_nat i) = Some (Vint (nth i bs Int.zero)).

(** A raw confidential value (asset or nonce): NULL or 33 bytes. *)
Definition conf_ok (m : mem) (s : rawsrc) (d : option (list int)) : Prop :=
  match s, d with
  | RNull, None => True
  | RPtr b o, Some bs => rs_readable m b o 33 bs
  | _, _ => False
  end.

Definition conf_of (d : option (list int)) : int * list int :=
  match d with
  | None => (Int.zero, repeat Int.zero 8)
  | Some bs => (conf_prefix (nth 0 bs Int.zero), tm_words (tl bs))
  end.

Lemma copyconf_any bconf oconf m s d :
  0 <= oconf -> oconf + 36 <= Ptrofs.max_unsigned -> (4 | oconf) ->
  Mem.range_perm m bconf oconf (oconf + 36) Cur Writable ->
  conf_ok m s d -> rs_other s bconf ->
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_copyRawConfidential)
      [Vptr bconf (Ptrofs.repr oconf); rs_val s] E0 m' Vundef /\
    rc_post bconf oconf m m' (fst (conf_of d)) (snd (conf_of d)).
Proof.
  intros H0 HM HA PW HOk HOth. destruct s as [|b o]; destruct d as [bs|]; try contradiction.
  - exact (eval_copyRawConfidential_null bconf oconf H0 HM HA m PW).
  - destruct HOk as [HR HB].
    exact (eval_copyRawConfidential_raw bconf oconf H0 HM HA b o bs HOth m PW HR HB).
Qed.

(** A raw amount: NULL, an explicit value (9 bytes, first byte 1) or a
    confidential one (33 bytes). *)
Definition amt_ok (m : mem) (s : rawsrc) (d : option (list int)) : Prop :=
  match s, d with
  | RNull, None => True
  | RPtr b o, Some bs =>
      if Int.eq (nth 0 bs Int.zero) (Int.repr 1) then rs_readable m b o 9 bs else rs_readable m b o 33 bs
  | _, _ => False
  end.

Definition amt_prefix (d : option (list int)) : int :=
  match d with
  | None => Int.repr 1
  | Some bs => if Int.eq (nth 0 bs Int.zero) (Int.repr 1) then Int.repr 1 else amt_parity (nth 0 bs Int.zero)
  end.

Definition amt_at (m : mem) (bamt : block) (oamt : Z) (d : option (list int)) : Prop :=
  match d with
  | None => Mem.load Mint64 m bamt oamt = Some (Vlong Int64.zero)
  | Some bs =>
      if Int.eq (nth 0 bs Int.zero) (Int.repr 1)
      then Mem.load Mint64 m bamt oamt =
             Some (Vlong (c_be64 (nth 1 bs Int.zero) (nth 2 bs Int.zero) (nth 3 bs Int.zero) (nth 4 bs Int.zero)
                                 (nth 5 bs Int.zero) (nth 6 bs Int.zero) (nth 7 bs Int.zero) (nth 8 bs Int.zero)))
      else uint32_array_at m bamt oamt (tm_words (tl bs))
  end.

Lemma copyamt_any bamt oamt m s d :
  0 <= oamt -> oamt + 40 <= Ptrofs.max_unsigned -> (8 | oamt) ->
  Mem.range_perm m bamt oamt (oamt + 40) Cur Writable ->
  amt_ok m s d -> rs_other s bamt ->
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_copyRawAmt)
      [Vptr bamt (Ptrofs.repr oamt); rs_val s] E0 m' Vundef /\
    Mem.load Mint32 m' bamt (oamt + 32) = Some (Vint (amt_prefix d)) /\
    amt_at m' bamt oamt d /\
    (forall ch b ofs, b <> bamt \/ ofs + size_chunk ch <= oamt \/ oamt + 40 <= ofs ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros H0 HM HA PW HOk HOth. destruct s as [|b o]; destruct d as [bs|]; try contradiction.
  - destruct (eval_copyRawAmt_null bamt oamt H0 HM HA m PW) as (m' & HX & HP & HV & HF & HPm & HNb).
    exists m'. split; [exact HX|]. split; [exact HP|]. split; [exact HV|]. split; [exact HF|].
    split; [intros b ofs k p Hp; apply HPm; exact Hp|].
    intros b Hb. unfold Mem.valid_block in *. rewrite HNb. exact Hb.
  - cbn [amt_ok amt_prefix amt_at] in *.
    pose proof (Int.eq_spec (nth 0 bs Int.zero) (Int.repr 1)) as HE.
    destruct (Int.eq (nth 0 bs Int.zero) (Int.repr 1)).
    + destruct HOk as [HR HB].
      destruct (eval_copyRawAmt_explicit bamt oamt H0 HM HA b o bs HOth m PW HR HB HE)
        as (m' & HX & HP & HV & HF & HPm & HNb).
      exists m'. split; [exact HX|]. split; [exact HP|]. split; [exact HV|]. split; [exact HF|].
      split; [intros b0 ofs k p Hp; apply HPm; exact Hp|].
      intros b0 Hb. unfold Mem.valid_block in *. rewrite HNb. exact Hb.
    + destruct HOk as [HR HB].
      destruct (eval_copyRawAmt_confidential bamt oamt H0 HM HA b o bs HOth m PW HR HB HE)
        as (m' & HX & HP & HV & HF & HPm & HNb).
      exists m'. split; [exact HX|]. split; [exact HP|]. split; [exact HV|]. split; [exact HF|].
      split; [intros b0 ofs k p Hp; apply HPm; exact Hp|].
      intros b0 Hb. unfold Mem.valid_block in *. rewrite HNb. exact Hb.
Qed.

(** An optional buffer [(buf, len)]. *)
Inductive bufsrc : Type := BNull | BPtr (b : block) (o : ptrofs) (bs : list int).

Definition buf_bytes (s : bufsrc) : list int :=
  match s with BNull => [] | BPtr _ _ bs => bs end.

Definition buf_other (s : bufsrc) (b0 : block) : Prop :=
  match s with BNull => True | BPtr b _ _ => b <> b0 end.

Definition buf_at (m : mem) (bbuf : block) (obuf : Z) (s : bufsrc) (len : int) : Prop :=
  Mem.load Mint32 m bbuf (obuf + 8) = Some (Vint len) /\
  Z.of_nat (length (buf_bytes s)) = Int.unsigned len /\
  match s with
  | BNull => Mem.load Mptr m bbuf obuf = Some (Vlong Int64.zero)
  | BPtr b o bs =>
      Mem.load Mptr m bbuf obuf = Some (Vptr b o) /\ Mem.valid_block m b /\
      Ptrofs.unsigned o + Z.of_nat (length bs) <= Ptrofs.max_unsigned /\
      forall i, (i < length bs)%nat ->
        Mem.load Mint8unsigned m b (Ptrofs.unsigned o + Z.of_nat i) = Some (Vint (nth i bs Int.zero))
  end.

Lemma hashbuf_any (Hmodel : memcpy_model) m bres ores bbuf obuf s len :
  0 <= ores -> ores + 32 <= Ptrofs.max_unsigned -> (4 | ores) ->
  Mem.range_perm m bres ores (ores + 32) Cur Writable ->
  GC <> bres -> GM <> bres -> 0 <= obuf -> obuf + 16 <= Ptrofs.max_unsigned ->
  buf_at m bbuf obuf s len -> bbuf <> bres -> buf_other s bres ->
  sha_dispatch_ok m -> Mem.load Mint64 m GM 0 = Some (Vlong sha_max_counter) ->
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_hashBuffer)
      [Vptr bres (Ptrofs.repr ores); Vptr bbuf (Ptrofs.repr obuf)] E0 m' Vundef /\
    (forall j, (j < 8)%nat ->
       Mem.load Mint32 m' bres (ores + 4 * Z.of_nat j) =
         Some (Vint (nth j (hash_buffer_regs (buf_bytes s)) Int.zero))) /\
    (forall ch b ofs, Mem.valid_block m b ->
       (b <> bres \/ ofs + size_chunk ch <= ores \/ ores + 32 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros H0 HM HA PW NG NM Hb0 HbM (HLen & HLn & HS) Nbuf HOth Hdisp HMax.
  destruct s as [|b o bs]; cbn [buf_bytes buf_other] in *.
  - assert (len = Int.zero).
    { rewrite <- (Int.repr_unsigned len). rewrite <- HLn. reflexivity. }
    subst len.
    exact (eval_hashBuffer_empty Hmodel m bres ores bbuf obuf H0 HM HA PW NG NM Hb0 HbM HS HLen
             (or_introl Nbuf) Hdisp HMax).
  - destruct HS as (HP & Vb & HoM & HB).
    destruct (eval_hashBuffer Hmodel m bres ores bbuf (Ptrofs.repr obuf) b o bs len H0 HM HA PW
                (not_eq_sym NG) (not_eq_sym NM) HOth Nbuf Vb) as (m' & HX & HR & HF & HPm & HV).
    { rewrite Ptrofs.unsigned_repr by lia. lia. }
    { rewrite Ptrofs.unsigned_repr by lia. exact HP. }
    { rewrite Ptrofs.unsigned_repr by lia. exact HLen. }
    { exact HLn. }
    { exact HoM. }
    { exact HB. }
    { exact Hdisp. }
    { exact HMax. }
    exists m'. split; [exact HX|]. split; [exact HR|]. split; [exact HF|].
    split; [intros b0 ofs k p _ Hp; apply HPm; exact Hp|exact HV].
Qed.

(** Call statements. *)
Lemma co_call2 e le m m' (fid : ident) (f : function) (a1 a2 : expr) (v1 v2 : val) (ty1 ty2 : type) :
  e!fid = None ->
  Genv.find_symbol (Clight.genv_genv sha_ge) fid = Some (sha_symbol_block fid) ->
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block fid) Ptrofs.zero) = Some (Internal f) ->
  type_of_function f = Tfunction (Tcons ty1 (Tcons ty2 Tnil)) tvoid cc_default ->
  eval_expr sha_ge e le m a1 v1 -> sem_cast v1 (typeof a1) ty1 m = Some v1 ->
  eval_expr sha_ge e le m a2 v2 -> sem_cast v2 (typeof a2) ty2 m = Some v2 ->
  Clight2.eval_funcall sha_ge m (Internal f) [v1; v2] E0 m' Vundef ->
  Clight2.exec_stmt sha_ge e le m
    (Scall None (Evar fid (Tfunction (Tcons ty1 (Tcons ty2 Tnil)) tvoid cc_default)) [a1; a2])
    E0 le m' Out_normal.
Proof.
  intros He HSy HFn HTy H1 C1 H2 C2 HC. change le with (set_opttemp None Vundef le) at 2.
  eapply exec_Scall with (vf := Vptr (sha_symbol_block fid) Ptrofs.zero) (vargs := [v1; v2]) (f := Internal f).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact He|exact HSy]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [exact H1|exact C1|]. eapply eval_Econs; [exact H2|exact C2|apply eval_Enil].
  - exact HFn.
  - cbn [type_of_fundef]. exact HTy.
  - exact HC.
Qed.

(** Transport of the input descriptions to a memory that agrees on the
    blocks they read. *)
Definition same_on (b : block) (m m' : mem) : Prop :=
  forall ch ofs, Mem.load ch m' b ofs = Mem.load ch m b ofs.

Definition rs_same (s : rawsrc) (m m' : mem) : Prop :=
  match s with RNull => True | RPtr b _ => same_on b m m' end.

Lemma rs_readable_same m m' b o n bs : same_on b m m' -> rs_readable m b o n bs -> rs_readable m' b o n bs.
Proof. intros HS [H1 H2]. split; [exact H1|]. intros i Hi. rewrite HS. exact (H2 i Hi). Qed.

Lemma conf_ok_same m m' s d : rs_same s m m' -> conf_ok m s d -> conf_ok m' s d.
Proof.
  destruct s as [|b o]; destruct d as [bs|]; cbn; try tauto. intros HS H. exact (rs_readable_same _ _ _ _ _ _ HS H).
Qed.

Lemma amt_ok_same m m' s d : rs_same s m m' -> amt_ok m s d -> amt_ok m' s d.
Proof.
  destruct s as [|b o]; destruct d as [bs|]; cbn; try tauto. intros HS H.
  destruct (Int.eq (nth 0 bs Int.zero) (Int.repr 1)); exact (rs_readable_same _ _ _ _ _ _ HS H).
Qed.

Lemma conf_ok_valid m b o d : conf_ok m (RPtr b o) d -> Mem.valid_block m b.
Proof.
  destruct d as [bs|]; cbn; [|tauto]. intros [_ H].
  pose proof (H 0%nat ltac:(lia)) as HL. eapply Mem.valid_access_valid_block.
  eapply Mem.valid_access_implies; [exact (Mem.load_valid_access _ _ _ _ _ HL)|constructor].
Qed.

Lemma amt_ok_valid m b o d : amt_ok m (RPtr b o) d -> Mem.valid_block m b.
Proof.
  destruct d as [bs|]; cbn; [|tauto]. intros H.
  assert (HL : exists v, Mem.load Mint8unsigned m b (Ptrofs.unsigned o + Z.of_nat 0) = Some v).
  { destruct (Int.eq (nth 0 bs Int.zero) (Int.repr 1)); destruct H as [_ H]; eexists; apply (H 0%nat); lia. }
  destruct HL as [v HL]. eapply Mem.valid_access_valid_block.
  eapply Mem.valid_access_implies; [exact (Mem.load_valid_access _ _ _ _ _ HL)|constructor].
Qed.

Definition buf_same (s : bufsrc) (m m' : mem) : Prop :=
  match s with BNull => True | BPtr b _ _ => same_on b m m' /\ (Mem.valid_block m b -> Mem.valid_block m' b) end.

Lemma buf_at_same m m' bbuf obuf s len :
  same_on bbuf m m' -> buf_same s m m' -> buf_at m bbuf obuf s len -> buf_at m' bbuf obuf s len.
Proof.
  intros HB HS (H1 & H2 & H3). split; [rewrite HB; exact H1|]. split; [exact H2|].
  destruct s as [|b o bs]; cbn in *.
  - rewrite HB. exact H3.
  - destruct HS as [HS HV]. destruct H3 as (H3 & H4 & H5 & H6).
    split; [rewrite HB; exact H3|]. split; [exact (HV H4)|]. split; [exact H5|].
    intros i Hi. rewrite HS. exact (H6 i Hi).
Qed.

(** The script buffer as [parseNullData] reads it. *)
Definition buf_blk (dflt : block) (s : bufsrc) : block :=
  match s with BNull => dflt | BPtr b _ _ => b end.
Definition buf_ofs (s : bufsrc) : ptrofs :=
  match s with BNull => Ptrofs.zero | BPtr _ o _ => o end.

Lemma buf_blk_other dflt s b0 : dflt <> b0 -> buf_other s b0 -> buf_blk dflt s <> b0.
Proof. destruct s; cbn; auto. Qed.

Lemma buf_blk_valid m bbuf obuf s len :
  buf_at m bbuf obuf s len -> Mem.valid_block m bbuf -> Mem.valid_block m (buf_blk bbuf s).
Proof. intros (_ & _ & H) Hv. destruct s; cbn in *; [exact Hv|tauto]. Qed.

Lemma buf_parse_facts m bbuf obuf s len :
  buf_at m bbuf obuf s len ->
  Ptrofs.unsigned (buf_ofs s) + Int.unsigned len <= Ptrofs.max_unsigned /\
  (0 < Int.unsigned len -> Mem.load Mptr m bbuf obuf = Some (Vptr (buf_blk bbuf s) (buf_ofs s))) /\
  (forall i, 0 <= i < Int.unsigned len ->
     Mem.load Mint8unsigned m (buf_blk bbuf s) (Ptrofs.unsigned (buf_ofs s) + i) =
       Some (Vint (nth (Z.to_nat i) (buf_bytes s) Int.zero))).
Proof.
  intros (H1 & H2 & H3). destruct s as [|b o bs]; cbn in *.
  - split; [rewrite <- H2; change (Ptrofs.unsigned Ptrofs.zero) with 0; vm_compute; discriminate|].
    split; intros; lia.
  - destruct H3 as (H3 & H4 & H5 & H6). split; [lia|]. split; [intros _; exact H3|].
    intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) at 1 by lia. apply H6. lia.
Qed.

Lemma weak_valid_keep m m' b ofs :
  (forall o k p, Mem.perm m b o k p -> Mem.perm m' b o k p) ->
  Mem.weak_valid_pointer m b ofs = true -> Mem.weak_valid_pointer m' b ofs = true.
Proof.
  intros HP H. apply Mem.weak_valid_pointer_spec in H. apply Mem.weak_valid_pointer_spec.
  rewrite !Mem.valid_pointer_nonempty_perm in *. destruct H as [H|H]; [left|right]; apply HP, H.
Qed.

Lemma weak_valid_block m b ofs : Mem.weak_valid_pointer m b ofs = true -> Mem.valid_block m b.
Proof.
  intros H. apply Mem.weak_valid_pointer_spec in H. rewrite !Mem.valid_pointer_nonempty_perm in H.
  destruct H as [H|H]; eapply Mem.perm_valid_block; exact H.
Qed.

(** Word arrays of eight words by index. *)
Lemma uint32_array_at_nth m b base ws :
  uint32_array_at m b base ws -> length ws = 8%nat ->
  forall j, (j < 8)%nat -> Mem.load Mint32 m b (base + 4 * Z.of_nat j) = Some (Vint (nth j ws Int.zero)).
Proof. intros H HL j Hj. apply H. apply nth_error_nth'. lia. Qed.

Lemma conf_of_length d : length (snd (conf_of d)) = 8%nat.
Proof. destruct d; cbn [conf_of snd]; [unfold tm_words; rewrite map_length, seq_length; reflexivity|reflexivity]. Qed.

Lemma amt_at_same m m' bamt oamt d :
  (forall ch ofs, oamt <= ofs -> ofs + size_chunk ch <= oamt + 32 ->
     Mem.load ch m' bamt ofs = Mem.load ch m bamt ofs) ->
  amt_at m bamt oamt d -> amt_at m' bamt oamt d.
Proof.
  intros HS. destruct d as [bs|]; cbn [amt_at].
  - destruct (Int.eq (nth 0 bs Int.zero) (Int.repr 1)).
    + intros H. rewrite HS by (change (size_chunk Mint64) with 8; lia). exact H.
    + intros H i x Hi.
      assert (i < 8)%nat.
      { assert (Hlt : (i < length (tm_words (tl bs)))%nat) by (apply nth_error_Some; congruence).
        unfold tm_words in Hlt. rewrite map_length, seq_length in Hlt. exact Hlt. }
      rewrite HS by (change (size_chunk Mint32) with 4; lia). exact (H i x Hi).
  - intros H. rewrite HS by (change (size_chunk Mint64) with 8; lia). exact H.
Qed.

Lemma div4_of_8 x d k : (8 | x) -> d = 4 * k -> (4 | x + d).
Proof. intros [q ->] ->. exists (2 * q + k). ring. Qed.
