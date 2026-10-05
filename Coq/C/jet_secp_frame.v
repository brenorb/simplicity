(** The byte-level frame helpers [read8s] and [write8s] as oracles of the
    symbolic executor in the secp256k1 translation unit. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_exec C.jet_frame_spec C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_encoding.
Require Import C.jet_read8s_layout C.jet_write8s_layout C.jet_write8_sequence C.jet_bitcoin_effects.
Require Import C.jet_frame_inv C.jet_frame_bits.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_sx_exec C.jet_sx_orc C.jet_sx_rep.
Require Import C.jet_secp_linkage.
Require C.jets.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Definition tRD8 : nat := 1.
Definition tWR8 : nat := 2.
Definition β0 : nat -> block * Z := fun _ => (1%positive, 0).

Fixpoint byte_cells (ofs : Z) (n : nat) (v : nat) : list cell :=
  match n with
  | O => []
  | S n => mkcell ofs Mint8unsigned (Some (XL2I (XLv v))) :: byte_cells (ofs + 1) n (S v)
  end.
Fixpoint byte_undef (ofs : Z) (n : nat) : list cell :=
  match n with O => [] | S n => mkcell ofs Mint8unsigned None :: byte_undef (ofs + 1) n end.

Lemma byte_cells_shape n : forall ofs v, map cshape (byte_cells ofs n v) = map cshape (byte_undef ofs n).
Proof. induction n; intros; simpl; [reflexivity|]. rewrite IHn. reflexivity. Qed.

Lemma byte_cells_In n : forall ofs v c, In c (byte_cells ofs n v) ->
  exists j, (j < n)%nat /\ c = mkcell (ofs + Z.of_nat j) Mint8unsigned (Some (XL2I (XLv (v + j)))).
Proof.
  induction n as [|n IH]; intros ofs v c Hin; simpl in Hin; [contradiction|].
  destruct Hin as [<-|Hin].
  - exists 0%nat. split; [lia|]. f_equal; [lia|]. rewrite Nat.add_0_r. reflexivity.
  - destruct (IH _ _ _ Hin) as (j & Hj & ->). exists (S j). split; [lia|]. f_equal; [lia|].
    replace (v + S j)%nat with (S v + j)%nat by lia. reflexivity.
Qed.

Lemma byte_undef_nth n : forall ofs j, (j < n)%nat ->
  In (ofs + Z.of_nat j, Mint8unsigned) (map cshape (byte_undef ofs n)).
Proof.
  induction n as [|n IH]; intros ofs j Hj; [lia|]. simpl. destruct j.
  - left. unfold cshape. simpl. f_equal. lia.
  - right. replace (ofs + Z.of_nat (S j)) with (ofs + 1 + Z.of_nat j) by lia. apply IH. lia.
Qed.

Fixpoint shape_eqb (a b : list (Z * memory_chunk)) : bool :=
  match a, b with
  | [], [] => true
  | (o1, c1) :: t1, (o2, c2) :: t2 => Z.eqb o1 o2 && chunk_eqb c1 c2 && shape_eqb t1 t2
  | _, _ => false
  end.
Lemma shape_eqb_eq a : forall b, shape_eqb a b = true -> a = b.
Proof.
  induction a as [|[o1 c1] t1 IH]; intros [|[o2 c2] t2] H; simpl in H; try discriminate; [reflexivity|].
  apply andb_true_iff in H. destruct H as [H H3]. apply andb_true_iff in H. destruct H as [H1 H2].
  apply Z.eqb_eq in H1. apply chunk_eqb_eq in H2. rewrite (IH _ H3). congruence.
Qed.

Definition as_xp0 (x : sx) : option nat :=
  match x with XP r d => if Z.eqb d 0 then Some r else None | _ => None end.
Lemma as_xp0_eq x r : as_xp0 x = Some r -> x = XP r 0.
Proof.
  destruct x; simpl; try discriminate. destruct (Z.eqb_spec d 0); [|discriminate].
  intros H; inversion H; subst. reflexivity.
Qed.

(** The read cursor of a local frame: the initial cursor (variable 0) plus a
    constant. *)
Definition cur_k (x : sx) : option int64 :=
  match x with
  | XLb Badd (XLv O) (XLc kc) => Some kc
  | _ => None
  end.
Lemma cur_k_eq x kc : cur_k x = Some kc -> x = XLb Badd (XLv 0%nat) (XLc kc).
Proof.
  destruct x; simpl; try discriminate. destruct o; try discriminate.
  destruct x1; try discriminate. destruct n; try discriminate.
  destruct x2; try discriminate. intros H; inversion H; subst. reflexivity.
Qed.

(** A local frame struct: its edge pointer and its cursor. *)
Definition frame_cells (regS : region) : option (sx * int64) :=
  match rcells regS with
  | [c1; c2] =>
      match cval c1, cval c2 with
      | Some xp, Some xc =>
          match cur_k xc with
          | Some kc =>
              if Z.eqb (cofs c1) 0 && chunk_eqb (cchunk c1) Mint64 &&
                 Z.eqb (cofs c2) 8 && chunk_eqb (cchunk c2) Mint64 && isk KA xp
              then Some (xp, kc) else None
          | None => None
          end
      | _, _ => None
      end
  | _ => None
  end.
Definition mk_frame_cells (xp : sx) (kc : int64) : list cell :=
  [mkcell 0 Mint64 (Some xp); mkcell 8 Mint64 (Some (XLb Badd (XLv 0%nat) (XLc kc)))].
Lemma frame_cells_eq regS xp kc :
  frame_cells regS = Some (xp, kc) -> rcells regS = mk_frame_cells xp kc /\ isk KA xp = true.
Proof.
  unfold frame_cells. destruct (rcells regS) as [|c1 [|c2 [|? ?]]]; try discriminate.
  destruct c1 as [o1 ch1 v1], c2 as [o2 ch2 v2]. simpl.
  destruct v1 as [xp'|]; [|discriminate]. destruct v2 as [xc|]; [|discriminate].
  destruct (cur_k xc) as [kc'|] eqn:Ek; [|discriminate].
  destruct (Z.eqb o1 0 && chunk_eqb ch1 Mint64 && Z.eqb o2 8 && chunk_eqb ch2 Mint64 && isk KA xp') eqn:E; [|discriminate].
  intros H; inversion H; subst.
  apply andb_true_iff in E. destruct E as [E K5]. apply andb_true_iff in E. destruct E as [E K4].
  apply andb_true_iff in E. destruct E as [E K3]. apply andb_true_iff in E. destruct E as [K1 K2].
  apply Z.eqb_eq in K1, K3. apply chunk_eqb_eq in K2, K4. subst.
  rewrite (cur_k_eq _ _ Ek). split; [reflexivity|assumption].
Qed.

Definition is_wr (ev : event) : bool := Nat.eqb (etag ev) tWR8.
Definition has_wr (log : list event) : bool := existsb is_wr log.
Definition wr_bytes (ρ : nat -> int64) (ev : event) : list int :=
  map (fun x => ii (den ρ β0 x)) (tl (eargs ev)).
Definition outsA (ρ : nat -> int64) (log : list event) : list Cell :=
  concat (map (fun ev => if is_wr ev then byte_sequence_cells (wr_bytes ρ ev) else []) log).
Fixpoint written (log : list event) : Z :=
  match log with
  | [] => 0
  | ev :: t => (if is_wr ev then 8 * Z.of_nat (length (tl (eargs ev))) else 0) + written t
  end.

Lemma outsA_length ρ log : Z.of_nat (length (outsA ρ log)) = written log.
Proof.
  induction log as [|ev t IH]; [reflexivity|]. unfold outsA in *. cbn [map concat written].
  rewrite app_length, Nat2Z.inj_add, IH. destruct (is_wr ev); [|reflexivity].
  rewrite byte_sequence_cells_length. unfold wr_bytes. rewrite map_length, Nat2Z.inj_mul. reflexivity.
Qed.
Lemma outsA_app ρ l1 l2 : outsA ρ (l1 ++ l2) = outsA ρ l1 ++ outsA ρ l2.
Proof. unfold outsA. rewrite map_app, concat_app. reflexivity. Qed.
Lemma has_wr_app l1 l2 : has_wr (l1 ++ l2) = has_wr l1 || has_wr l2.
Proof. unfold has_wr. apply existsb_app. Qed.
Lemma written_app l1 l2 : written (l1 ++ l2) = written l1 + written l2.
Proof. induction l1; simpl; lia. Qed.

Lemma i64_add_repr a b : Int64.add (Int64.repr a) (Int64.repr b) = Int64.repr (a + b).
Proof.
  unfold Int64.add. apply Int64.eqm_samerepr.
  apply Int64.eqm_add; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma secp_read8s_layout m bo output bf base bi edge cursor (xs : list (Ty.tySem (Word 3))) :
  0 <= output -> output + Z.of_nat (length xs) <= Ptrofs.max_unsigned ->
  Mem.range_perm m bo output (output + Z.of_nat (length xs)) Cur Writable ->
  bf <> bo -> bf <> bi -> bo <> bi ->
  frame_base_valid base -> 0 <= cursor -> cursor + 8 * Z.of_nat (length xs) <= Int64.max_unsigned ->
  frame_fields_at m bf base bi edge cursor -> Mem.valid_access m Mint64 bf (base + 8) Writable ->
  (forall i x, nth_error xs i = Some x ->
    frame_input_word_at m bi edge (cursor + 8 * Z.of_nat i) x) ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal jets.f_read8s)
      [Vptr bo (Ptrofs.repr output); Vlong (Int64.repr (Z.of_nat (length xs)));
        Vptr bf (Ptrofs.repr base)] E0 mf Vundef /\
    uint8_array_at mf bo output (map word8_array_value xs) /\
    frame_fields_at mf bf base bi edge (cursor + 8 * Z.of_nat (length xs)) /\
    (forall chunk b ofs,
      (b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs) ->
      (b <> bo \/ ofs + size_chunk chunk <= output \/
        output + Z.of_nat (length xs) <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros. destruct (eval_read8s_layout m bo output bf base bi edge cursor xs) as (mf & Hev & Hrest); try assumption.
  exists mf. split; [|exact Hrest].
  apply (secp_transport_call jets._read8s jets.f_read8s); [|exact Hev].
  do 19 right. left. reflexivity.
Qed.

Section FRAMEA.
Variables (m0 : mem) (bd : block) (dbase : Z) (bw : block) (outedge cursor N : Z) (bi : block).
Variables (edge rc : Z) (ibits : list bool).
Variables (w0 : bool) (outs0 : list Cell) (capA : Z).
Hypothesis HF0 : write_frame_at m0 bd dbase bw outedge cursor N.
Hypothesis Hin : frame_input_cells_at m0 bi edge rc (map Some ibits).
Hypothesis Hrc0 : 0 <= rc.
Hypothesis HrcM : rc + Z.of_nat (length ibits) <= Int64.max_unsigned.

Definition evokA (ρ : nat -> int64) (ev : event) : Prop :=
  if Nat.eqb (etag ev) tRD8 then
    match eargs ev with
    | [xp; XLc k; XLc n] =>
        den ρ β0 xp = Vptr bi (Ptrofs.repr edge) /\
        forall j, (j < ecnt ev)%nat ->
          ρ (ebase ev + j)%nat = Int64.repr (ifield ibits (Z.to_nat (Int64.unsigned k) + 8 * j) 8)
    | _ => False
    end
  else if Nat.eqb (etag ev) tWR8 then
    match eargs ev with
    | xd :: _ => den ρ β0 xd = Vptr bd (Ptrofs.repr dbase)
    | [] => False
    end
  else True.

Definition extA : block -> Prop := fext m0 bd bw bi.

Definition invA (ρ : nat -> int64) (log : list event) (m : mem) : Prop :=
  ρ 0%nat = Int64.repr rc /\
  finv m0 bd dbase bw outedge cursor N bi m (w0 || has_wr log) (outs0 ++ outsA ρ log) /\
  Z.of_nat (length outs0) + capA <= N /\ written log <= capA.

Lemma invA_stable ρ log m m' : invA ρ log m -> lframe (fun b _ => extA b) m m' -> invA ρ log m'.
Proof.
  intros (H1 & H2 & H3 & H4) U. split; [exact H1|]. split; [|split; assumption].
  eapply finv_stable; [exact HF0|exact H2|exact U].
Qed.

Lemma invA_valid ρ log m b : invA ρ log m -> extA b -> Mem.valid_block m b.
Proof. intros (_ & (HV & _) & _) Hb. exact (HV b Hb). Qed.

Definition orc_rd8 (nin : Z) : oracle := fun base log xs regs =>
  match xs with
  | [x1; xn; x3] =>
      match as_xp0 x1, xconst xn, as_xp0 x3 with
      | Some rb, Some n, Some rs =>
          match nth_error regs rb, nth_error regs rs with
          | Some regb, Some regS =>
              match frame_cells regS with
              | Some (xp, kc) =>
                  if negb w0 && negb (has_wr log) && Z.ltb 0 n &&
                     Z.leb (Int64.unsigned kc + 8 * n) nin && negb (Nat.eqb rb rs) &&
                     rw regb && rw regS &&
                     shape_eqb (map cshape (rcells regb)) (map cshape (byte_undef 0 (Z.to_nat n)))
                  then
                    Some (upd (upd regs rb (mkreg (byte_cells 0 (Z.to_nat n) base) (rw regb) (rfree regb)))
                              rs (mkreg (mk_frame_cells xp (Int64.repr (Int64.unsigned kc + 8 * n)))
                                        (rw regS) (rfree regS)),
                          None, tRD8, Z.to_nat n, [xp; XLc kc; XLc (Int64.repr n)])
                  else None
              | None => None
              end
          | _, _ => None
          end
      | _, _, _ => None
      end
  | _ => None
  end.

Lemma loword_byte z : 0 <= z < 256 ->
  Int64.loword (Int64.repr z) = word8_array_value (@fromZ (WordToZ 3) z).
Proof.
  intros Hz. unfold Int64.loword, word8_array_value.
  rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia).
  rewrite to_fromZ. change (two_power_nat (ToZ.Theory.bitSize (WordToZ 3))) with 256.
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Ltac fixlen :=
  match goal with
  | Hxl : Datatypes.length ?xs = ?nn |- context[Datatypes.length ?l] =>
      change (Datatypes.length l) with (Datatypes.length xs); rewrite Hxl
  end.

Lemma orc_rd8_ok nin :
  nin = Z.of_nat (length ibits) ->
  oracle_ok secp_ge evokA invA extA jets.f_read8s (orc_rd8 nin).
Proof.
  intros Hnin base xs regs regs' v tag cnt eargs log ρ β m Ho Hrep Hsep Hinv Hsol Hev.
  unfold orc_rd8 in Ho.
  destruct xs as [|x1 [|xn [|x3 [|? ?]]]]; try discriminate.
  destruct (as_xp0 x1) as [rb|] eqn:E1; [|discriminate].
  destruct (xconst xn) as [n|] eqn:En; [|discriminate].
  destruct (as_xp0 x3) as [rs|] eqn:E3; [|discriminate].
  destruct (nth_error regs rb) as [regb|] eqn:ERB; [|discriminate].
  destruct (nth_error regs rs) as [regS|] eqn:ERS; [|discriminate].
  destruct (frame_cells regS) as [[xp kc]|] eqn:Efc; [|discriminate].
  match type of Ho with (if ?c then _ else _) = _ => destruct c eqn:Chk; [|discriminate] end.
  apply andb_true_iff in Chk. destruct Chk as [Chk C8]. apply andb_true_iff in Chk. destruct Chk as [Chk C7].
  apply andb_true_iff in Chk. destruct Chk as [Chk C6]. apply andb_true_iff in Chk. destruct Chk as [Chk C5].
  apply andb_true_iff in Chk. destruct Chk as [Chk C4]. apply andb_true_iff in Chk. destruct Chk as [Chk C3].
  apply andb_true_iff in Chk. destruct Chk as [C1 C2].
  apply negb_true_iff in C1, C2, C5. apply Z.ltb_lt in C3. apply Z.leb_le in C4. apply Nat.eqb_neq in C5.
  apply shape_eqb_eq in C8.
  apply as_xp0_eq in E1, E3. subst x1 x3.
  destruct (xconst_sound ρ (lay β) xn n En) as [Hdn Hnr].
  destruct (frame_cells_eq _ _ _ Efc) as [HcS HKA]. destruct (den_KA xp HKA) as (bp & op & ->).
  inversion Ho; subst regs' v tag cnt eargs; clear Ho.
  destruct Hinv as (Hρ0 & Hfinv & Hcap & Hwr). rewrite C1, C2 in Hfinv. simpl orb in Hfinv.
  unfold evokA in Hev. cbn [etag eargs ecnt ebase] in Hev. change (Nat.eqb tRD8 tRD8) with true in Hev.
  cbv iota in Hev. destruct Hev as [Hptr Hvars]. simpl den in Hptr. inversion Hptr; subst bp op.
  set (nn := Z.to_nat n) in *. set (k := Int64.unsigned kc) in *.
  assert (Hk0 : 0 <= k) by (unfold k; pose proof (Int64.unsigned_range kc); lia).
  assert (Hnn : Z.of_nat nn = n) by (unfold nn; lia).
  set (bS := blk β rs). set (sb := bas β rs). set (bB := blk β rb). set (ob := bas β rb).
  pose proof Hrep as (Hlen & Hnrep & _).
  assert (Hrbl : (rb < length β)%nat) by (rewrite Hlen; apply nth_error_Some; congruence).
  assert (Hrsl : (rs < length β)%nat) by (rewrite Hlen; apply nth_error_Some; congruence).
  assert (HbSB : bS <> bB).
  { intros E. apply C5. symmetry. eapply blk_inj; eauto. }
  (* the frame struct *)
  destruct (rep_region _ _ _ _ _ _ Hrep ERS) as (HsB0 & HvS & _ & HcellsS & _).
  rewrite HcS, C7 in HcellsS.
  pose proof (Forall_inv HcellsS) as Hc1. pose proof (Forall_inv (Forall_inv_tail HcellsS)) as Hc2.
  destruct Hc1 as (Hm1 & Ha1 & Hp1 & Hv1). destruct Hc2 as (Hm2 & Ha2 & Hp2 & Hv2).
  cbn [cofs cchunk cval] in *. change (size_chunk Mint64) with 8 in *. change (align_chunk Mint64) with 8 in *.
  fold bS sb in Hm1, Ha1, Hp1, Hv1, Hm2, Ha2, Hp2, Hv2, HsB0.
  destruct (Hv1 _ eq_refl) as [Hl1 _]. destruct (Hv2 _ eq_refl) as [Hl2 _].
  simpl den in Hl1, Hl2. rewrite Hρ0 in Hl2.
  assert (Ecur : Int64.add (Int64.repr rc) kc = Int64.repr (rc + k)).
  { rewrite <- (Int64.repr_unsigned kc) at 1. apply i64_add_repr. }
  rewrite Ecur in Hl2.
  assert (HFS : frame_fields_at m bS sb bi edge (rc + k)).
  { split; [rewrite Z.add_0_r in Hl1; exact Hl1|exact Hl2]. }
  (* the buffer *)
  destruct (rep_region _ _ _ _ _ _ Hrep ERB) as (HoB0 & HvB & _ & HcellsB & _).
  rewrite C6 in HcellsB. fold bB ob in HoB0, HcellsB.
  assert (Hbuf : forall j, (j < nn)%nat ->
            ob + Z.of_nat j + 1 <= Ptrofs.max_unsigned /\
            Mem.perm m bB (ob + Z.of_nat j) Cur Writable).
  { intros j Hj. pose proof (byte_undef_nth nn 0 j Hj) as Hsh. rewrite <- C8 in Hsh.
    apply in_map_iff in Hsh. destruct Hsh as (c & Hc & Hinc). unfold cshape in Hc. inversion Hc as [[Ho Hch]].
    pose proof (proj1 (Forall_forall _ _) HcellsB c Hinc) as (Hm & _ & Hp & _).
    rewrite Ho, Hch in Hm, Hp. change (size_chunk Mint8unsigned) with 1 in *. fold bB ob in Hm, Hp.
    split; [lia|]. apply Hp. lia. }
  (* the input *)
  assert (Hne : ibits <> []).
  { intros E. rewrite E in Hnin. simpl in Hnin. lia. }
  pose proof (input_bi_valid m0 bi edge rc ibits Hin Hne) as Hbiv.
  assert (Hextbi : extA bi) by (split; [right; right; reflexivity|exact Hbiv]).
  assert (HSi : bS <> bi) by (intros E; apply (Hsep rs Hrsl); fold bS; rewrite E; exact Hextbi).
  assert (HBi : bB <> bi) by (intros E; apply (Hsep rb Hrbl); fold bB; rewrite E; exact Hextbi).
  set (xs := map (fun j => @fromZ (WordToZ 3) (ifield ibits (Z.to_nat k + 8 * j) 8)) (List.seq 0%nat nn)).
  assert (Hxl : length xs = nn) by (unfold xs; rewrite map_length, seq_length; reflexivity).
  destruct (secp_read8s_layout m bB ob bS sb bi edge (rc + k) xs) as (mf & Hevf & Harr & HFf & Hload & Hperm & Hvalid).
  { exact HoB0. }
  { fixlen. destruct (Hbuf (nn - 1)%nat ltac:(lia)) as [H _]. lia. }
  { fixlen. intros o Ho. destruct (Hbuf (Z.to_nat (o - ob)) ltac:(lia)) as [_ H].
    replace (ob + Z.of_nat (Z.to_nat (o - ob))) with o in H by lia. exact H. }
  { exact HbSB. }
  { exact HSi. }
  { exact HBi. }
  { split; lia. }
  { lia. }
  { fixlen. lia. }
  { exact HFS. }
  { split; [intros o Ho; apply Hp2; simpl in Ho; lia|exact Ha2]. }
  { intros i x Hi. unfold xs in Hi. rewrite nth_error_map in Hi.
    destruct (nth_error (List.seq 0%nat nn) i) as [j|] eqn:Ej; [|discriminate]. simpl in Hi. inversion Hi; subst x.
    assert (Hil : (i < nn)%nat) by (rewrite <- (seq_length nn 0); apply nth_error_Some; congruence).
    rewrite (nth_error_nth' _ 0%nat) in Ej by (rewrite seq_length; exact Hil).
    rewrite seq_nth in Ej by exact Hil. inversion Ej; subst j. simpl Nat.add.
    replace (rc + k + 8 * Z.of_nat i) with (rc + Z.of_nat (Z.to_nat k + 8 * i)) by lia.
    eapply input_byte_word; [exact Hin|exact Hfinv|]. lia. }
  assert (Hxn : Z.of_nat (length xs) = n) by (rewrite Hxl; exact Hnn).
  match type of Hevf with context[Z.of_nat (Datatypes.length ?l)] =>
    change (Z.of_nat (Datatypes.length l)) with (Z.of_nat (length xs)) in Hevf, HFf, Hload end.
  rewrite Hxn in Hevf, HFf, Hload.
  assert (Hloadext : forall chunk b ofs, extA b -> Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
  { intros chunk b ofs Hb. apply Hload.
    - left. intros E. apply (Hsep rs Hrsl). fold bS. rewrite <- E. exact Hb.
    - left. intros E. apply (Hsep rb Hrbl). fold bB. rewrite <- E. exact Hb. }
  exists mf, Vundef. split.
  { simpl map. rewrite Hdn. unfold blk, bas in *. fold bB ob bS sb. rewrite !Z.add_0_r. exact Hevf. }
  split.
  { (* the regions *)
    eapply rep_update with (regs := regs) (m := m); [exact Hrep| |exact Hperm|exact Hvalid|].
    - rewrite (upd_map_id rshape _ rs _ regS).
      + rewrite (upd_map_id rshape regs rb _ regb ERB); [reflexivity|].
        unfold rshape. simpl. rewrite byte_cells_shape, C8. reflexivity.
      + rewrite upd_other by exact C5. exact ERS.
      + unfold rshape. simpl. rewrite HcS. reflexivity.
    - intros r reg reg' c' x Hr Hr' Hin' Hx.
      destruct (Nat.eq_dec r rs) as [->|Hrs].
      + rewrite (upd_same _ rs _ regS) in Hr' by (rewrite upd_other by exact C5; exact ERS).
        inversion Hr'; subst reg'; clear Hr'. rewrite ERS in Hr. inversion Hr; subst reg; clear Hr.
        cbn [rcells mk_frame_cells In] in Hin'. destruct Hin' as [<-|[<-|[]]].
        * left. split; [rewrite HcS; left; reflexivity|].
          cbn [cofs cchunk]. apply Hload; [right; left; fold bS sb; simpl; lia|left; fold bS; exact HbSB].
        * right. cbn [cofs cchunk cval] in *. inversion Hx; subst x. split; [|reflexivity].
          destruct HFf as [_ HF2]. fold bS sb. rewrite HF2. cbn [den il lop]. rewrite Hρ0.
          rewrite i64_add_repr. do 2 f_equal. fold k.
          change (match n with 0 => 0 | Z.pos y' => Z.pos y'~0~0~0 | Z.neg y' => Z.neg y'~0~0~0 end) with (8 * n).
          f_equal. lia.
      + destruct (Nat.eq_dec r rb) as [->|Hrb].
        * rewrite upd_other in Hr' by congruence. rewrite (upd_same _ rb _ regb ERB) in Hr'.
          inversion Hr'; subst reg'; clear Hr'. cbn [rcells] in Hin'.
          destruct (byte_cells_In _ _ _ _ Hin') as (j & Hj & ->).
          right. cbn [cofs cchunk cval] in *. inversion Hx; subst x. split; [|reflexivity].
          fold bB ob. rewrite Z.add_0_l.
          rewrite (Harr j (word8_array_value (@fromZ (WordToZ 3) (ifield ibits (Z.to_nat k + 8 * j) 8)))).
          2: { unfold xs. rewrite !nth_error_map.
               rewrite (nth_error_nth' _ 0%nat) by (rewrite seq_length; exact Hj).
               rewrite seq_nth by exact Hj. reflexivity. }
          cbn [den il]. rewrite (Hvars j Hj). fold k.
          rewrite loword_byte; [reflexivity|].
          apply (ifield_range ibits (Z.to_nat k + 8 * j) 8). lia.
        * rewrite !upd_other in Hr' by congruence. rewrite Hr in Hr'. inversion Hr'; subst reg'.
          left. split; [exact Hin'|].
          assert (Hrl : (r < length β)%nat) by (rewrite Hlen; apply nth_error_Some; congruence).
          apply Hload; left; intros E; [apply Hrs|apply Hrb]; eapply blk_inj; eauto. }
  split.
  { (* the frame state *)
    split; [exact Hρ0|]. rewrite has_wr_app, outsA_app, written_app, C1, C2. simpl.
    rewrite app_nil_r, Z.add_0_r. split; [|split; assumption].
    eapply finv_stable; [exact HF0|exact Hfinv|].
    split; [intros chunk b ofs _ Hb; apply Hloadext; apply (Hb ofs); pose proof (size_chunk_pos chunk); lia|].
    split; [intros b ofs kk p _ _ Hp; apply Hperm; exact Hp|intros b Hv; apply Hvalid; exact Hv]. }
  split.
  { rewrite (upd_map_id rshape _ rs _ regS).
    - rewrite (upd_map_id rshape regs rb _ regb ERB); [reflexivity|].
      unfold rshape. simpl. rewrite byte_cells_shape, C8. reflexivity.
    - rewrite upd_other by exact C5. exact ERS.
    - unfold rshape. simpl. rewrite HcS. reflexivity. }
  split; [reflexivity|].
  (* framing *)
  split.
  { intros chunk b ofs Hvb HP. pose proof (size_chunk_pos chunk) as Hsz. apply Hload.
    - destruct (peq b bS) as [->|]; [|left; assumption]. right.
      destruct (Z_le_dec (ofs + size_chunk chunk) (sb + 8)); [left; assumption|].
      destruct (Z_le_dec (sb + 16) ofs); [right; assumption|]. exfalso.
      destruct (HP (Z.max ofs (sb + 8)) ltac:(lia)) as (_ & Hnf & _). apply Hnf.
      exists rs, (rshape regS), 8, Mint64. split; [rewrite nth_error_map, ERS; reflexivity|].
      split; [unfold rshape; simpl; rewrite HcS; simpl; right; left; reflexivity|].
      split; [reflexivity|]. fold sb. simpl. lia.
    - destruct (peq b bB) as [->|]; [|left; assumption]. right.
      destruct (Z_le_dec (ofs + size_chunk chunk) ob); [left; assumption|].
      destruct (Z_le_dec (ob + n) ofs); [right; assumption|]. exfalso.
      destruct (HP (Z.max ofs ob) ltac:(lia)) as (_ & Hnf & _). apply Hnf.
      exists rb, (rshape regb), (Z.max ofs ob - ob), Mint8unsigned.
      split; [rewrite nth_error_map, ERB; reflexivity|].
      split.
      { unfold rshape. simpl. rewrite C8.
        replace (Z.max ofs ob - ob) with (0 + Z.of_nat (Z.to_nat (Z.max ofs ob - ob))) by lia.
        apply byte_undef_nth. lia. }
      split; [reflexivity|]. fold ob. simpl. lia. }
  split; [intros b ofs kk p _ _ Hp; apply Hperm; exact Hp|exact Hvalid].
Qed.

(** ** Writing bytes *)
Definition cell_sx (c : cell) : sx := match cval c with Some x => x | None => XIc Int.zero end.
Definition cell_KI (c : cell) : bool := match cval c with Some x => isk KI x | None => false end.

Definition orc_wr8 : oracle := fun base log xs regs =>
  match xs with
  | [xd; x2; xn] =>
      match as_xp0 x2, xconst xn with
      | Some rb, Some n =>
          match nth_error regs rb with
          | Some regb =>
              if isk KA xd && Z.ltb 0 n &&
                 shape_eqb (map cshape (rcells regb)) (map cshape (byte_undef 0 (Z.to_nat n))) &&
                 forallb cell_KI (rcells regb) && Z.leb (written log + 8 * n) capA
              then Some (regs, None, tWR8, 0%nat, xd :: map cell_sx (rcells regb))
              else None
          | None => None
          end
      | _, _ => None
      end
  | _ => None
  end.

Lemma secp_write8s_layout m bb input bf base bw' edge' cursor' xs :
  0 <= input -> input + Z.of_nat (length xs) <= Ptrofs.max_unsigned ->
  bb <> bf -> bb <> bw' -> uint8_array_at m bb input xs ->
  write_frame_at m bf base bw' edge' cursor' (8 * Z.of_nat (length xs)) ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal jets.f_write8s)
      [Vptr bf (Ptrofs.repr base); Vptr bb (Ptrofs.repr input);
        Vlong (Int64.repr (Z.of_nat (length xs)))] E0 mf Vundef /\
    write_effect m mf bf base bw' edge' cursor' (8 * Z.of_nat (length xs)) (byte_sequence_cells xs).
Proof.
  intros. destruct (eval_write8s_layout m bb input bf base bw' edge' cursor' xs) as (mf & Hev & Hrest); try assumption.
  exists mf. split; [|exact Hrest].
  apply (secp_transport_call jets._write8s jets.f_write8s); [|exact Hev].
  do 18 right. left. reflexivity.
Qed.

Lemma byte_undef_length n : forall ofs, length (byte_undef ofs n) = n.
Proof. induction n; intros; simpl; [reflexivity|]. rewrite IHn. reflexivity. Qed.

Lemma byte_shape_nth n : forall ofs cs, map cshape cs = map cshape (byte_undef ofs n) ->
  forall j c, nth_error cs j = Some c -> cofs c = ofs + Z.of_nat j /\ cchunk c = Mint8unsigned.
Proof.
  induction n as [|n IH]; intros ofs cs H j c Hn.
  - destruct cs; [destruct j; discriminate|discriminate].
  - destruct cs as [|c0 t]; [discriminate|]. simpl in H. unfold cshape at 1 3 in H. cbn [cofs cchunk] in H.
    injection H as H1 H2 H3.
    destruct j; simpl in Hn.
    + inversion Hn; subst c0. split; [lia|first [assumption|reflexivity|congruence]].
    + destruct (IH (ofs + 1) t H3 j c Hn) as [E1 E2]. split; [lia|exact E2].
Qed.

Lemma orc_wr8_ok : oracle_ok secp_ge evokA invA extA jets.f_write8s orc_wr8.
Proof.
  intros base xs regs regs' v tag cnt eargs log ρ β m Ho Hrep Hsep Hinv Hsol Hev.
  unfold orc_wr8 in Ho.
  destruct xs as [|xd [|x2 [|xn [|? ?]]]]; try discriminate.
  destruct (as_xp0 x2) as [rb|] eqn:E2; [|discriminate].
  destruct (xconst xn) as [n|] eqn:En; [|discriminate].
  destruct (nth_error regs rb) as [regb|] eqn:ERB; [|discriminate].
  match type of Ho with (if ?c then _ else _) = _ => destruct c eqn:Chk; [|discriminate] end.
  apply andb_true_iff in Chk. destruct Chk as [Chk C5]. apply andb_true_iff in Chk. destruct Chk as [Chk C4].
  apply andb_true_iff in Chk. destruct Chk as [Chk C3]. apply andb_true_iff in Chk. destruct Chk as [C1 C2].
  apply Z.ltb_lt in C2. apply Z.leb_le in C5. apply shape_eqb_eq in C3. rewrite forallb_forall in C4.
  apply as_xp0_eq in E2. subst x2.
  destruct (xconst_sound ρ (lay β) xn n En) as [Hdn Hnr].
  destruct (den_KA xd C1) as (bp & op & ->).
  inversion Ho; subst regs' v tag cnt eargs; clear Ho.
  destruct Hinv as (Hρ0 & Hfinv & Hcap & Hwr).
  unfold evokA in Hev. cbn [etag eargs] in Hev. change (Nat.eqb tWR8 tRD8) with false in Hev.
  change (Nat.eqb tWR8 tWR8) with true in Hev. cbv iota in Hev. simpl den in Hev. inversion Hev; subst bp op.
  set (nn := Z.to_nat n) in *.
  assert (Hnn : Z.of_nat nn = n) by (unfold nn; lia).
  set (bB := blk β rb). set (ob := bas β rb).
  pose proof Hrep as (Hlen & Hnrep & _).
  assert (Hrbl : (rb < length β)%nat) by (rewrite Hlen; apply nth_error_Some; congruence).
  assert (Hcl : length (rcells regb) = nn).
  { rewrite <- (map_length cshape), C3, map_length. apply byte_undef_length. }
  assert (HNpos : 0 < N).
  { pose proof (outsA_length ρ log). pose proof (written log). 
    assert (0 <= written log) by (rewrite <- (outsA_length ρ log); lia). lia. }
  pose proof (fext_bd m0 bd dbase bw outedge cursor N bi HF0) as Hextd.
  assert (Hextw : extA bw).
  { split; [right; left; reflexivity|]. exact (bw_valid m0 bd dbase bw outedge cursor N HF0 HNpos). }
  assert (HBd : bB <> bd) by (intros E; apply (Hsep rb Hrbl); fold bB; rewrite E; exact Hextd).
  assert (HBw : bB <> bw) by (intros E; apply (Hsep rb Hrbl); fold bB; rewrite E; exact Hextw).
  destruct (rep_region _ _ _ _ _ _ Hrep ERB) as (HoB0 & HvB & _ & HcellsB & _).
  fold bB ob in HoB0, HcellsB.
  set (ys := map (fun c => ii (den ρ (lay β) (cell_sx c))) (rcells regb)).
  assert (Hyl : length ys = nn) by (unfold ys; rewrite map_length; exact Hcl).
  assert (Harr : uint8_array_at m bB ob ys).
  { intros i x Hi. unfold ys in Hi. rewrite nth_error_map in Hi.
    destruct (nth_error (rcells regb) i) as [c|] eqn:Ec; [|discriminate]. simpl in Hi. inversion Hi; subst x.
    destruct (byte_shape_nth nn 0 _ C3 i c Ec) as [Eo Ech].
    pose proof (nth_error_In _ _ Ec) as Hinc.
    pose proof (proj1 (Forall_forall _ _) HcellsB c Hinc) as (_ & _ & _ & Hv).
    pose proof (C4 c Hinc) as Hk. unfold cell_KI in Hk. unfold cell_sx.
    destruct (cval c) as [x|] eqn:Ev; [|discriminate].
    destruct (Hv x eq_refl) as [Hl _]. rewrite Eo, Ech in Hl. fold bB ob in Hl. rewrite Z.add_0_l in Hl.
    rewrite Hl. rewrite (den_KI ρ (lay β) x Hk) at 1. reflexivity. }
  assert (Hmaxb : ob + Z.of_nat nn <= Ptrofs.max_unsigned).
  { destruct (nth_error (rcells regb) (nn - 1)) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
    destruct (byte_shape_nth nn 0 _ C3 _ c Ec) as [Eo Ech].
    pose proof (proj1 (Forall_forall _ _) HcellsB c (nth_error_In _ _ Ec)) as (Hm & _).
    rewrite Eo, Ech in Hm. change (size_chunk Mint8unsigned) with 1 in Hm. fold ob in Hm. lia. }
  set (outs := outs0 ++ outsA ρ log) in *.
  assert (Houts : Z.of_nat (length outs) = Z.of_nat (length outs0) + written log).
  { unfold outs. rewrite app_length, Nat2Z.inj_add, outsA_length. reflexivity. }
  pose proof (finv_wframe m0 bd dbase bw outedge cursor N bi HF0 m _ outs Hfinv) as Hwf.
  assert (Hwf' : write_frame_at m bd dbase bw outedge (cursor - Z.of_nat (length outs)) (8 * Z.of_nat (length ys))).
  { destruct Hwf as (HB & HFl & HE & HC & HM & HD & PD & HW).
    split; [exact HB|]. split; [exact HFl|]. split; [exact HE|]. split; [rewrite Hyl; lia|]. split; [exact HM|].
    split; [exact HD|]. split; [exact PD|]. intros i Hi. apply HW. rewrite Hyl in Hi. lia. }
  destruct (secp_write8s_layout m bB ob bd dbase bw outedge (cursor - Z.of_nat (length outs)) ys)
    as (mf & Hevf & Heff); try assumption.
  { rewrite Hyl. exact Hmaxb. }
  pose proof Heff as (_ & _ & _ & Hload & Hperm & Hvalid).
  exists mf, Vundef. split.
  { simpl map. rewrite Hdn. unfold blk, bas in *. fold bB ob. rewrite Z.add_0_r.
    rewrite Hyl, Hnn in Hevf. exact Hevf. }
  split.
  { eapply rep_update with (regs := regs) (m := m); [exact Hrep|reflexivity|exact Hperm|exact Hvalid|].
    intros r reg reg' c' x Hr Hr' Hin' Hx. rewrite Hr in Hr'. inversion Hr'; subst reg'.
    left. split; [exact Hin'|].
    assert (Hrl : (r < length β)%nat) by (rewrite Hlen; apply nth_error_Some; congruence).
    apply Hload; left; intros E; apply (Hsep r Hrl); rewrite E; assumption. }
  split.
  { split; [exact Hρ0|]. rewrite has_wr_app, outsA_app, written_app.
    change (has_wr [mkev tWR8 base 0 (XA bd (Ptrofs.repr dbase) :: map cell_sx (rcells regb))]) with true.
    rewrite !orb_true_r.
    assert (Ebytes : outsA ρ [mkev tWR8 base 0 (XA bd (Ptrofs.repr dbase) :: map cell_sx (rcells regb))] =
                     byte_sequence_cells ys).
    { unfold outsA, is_wr. cbn [map concat etag]. change (Nat.eqb tWR8 tWR8) with true. cbv iota.
      rewrite app_nil_r. f_equal. unfold wr_bytes, ys. cbn [eargs tl]. rewrite map_map.
      apply map_ext. intros c. exact (proj1 (den_proj_indep ρ (cell_sx c) β0 (lay β))). }
    rewrite Ebytes, app_assoc. fold outs.
    split.
    { eapply finv_write; [exact HF0|exact Hfinv|reflexivity| |].
      - rewrite byte_sequence_cells_length, Nat2Z.inj_mul, Hyl. change (Z.of_nat 8) with 8. lia.
      - rewrite byte_sequence_cells_length, Nat2Z.inj_mul. change (Z.of_nat 8) with 8. exact Heff. }
    split; [exact Hcap|].
    unfold is_wr. cbn [written etag eargs tl]. unfold is_wr. cbn [etag]. change (Nat.eqb tWR8 tWR8) with true. cbv iota.
    rewrite map_length, Hcl. lia. }
  split; [reflexivity|]. split; [reflexivity|].
  split.
  { intros chunk b ofs Hvb HP. pose proof (size_chunk_pos chunk) as Hsz.
    destruct (HP ofs ltac:(lia)) as (_ & _ & Hne).
    apply Hload; left; intros E; apply Hne; rewrite E; assumption. }
  split; [intros b ofs kk p _ _ Hp; apply Hperm; exact Hp|exact Hvalid].
Qed.
End FRAMEA.
