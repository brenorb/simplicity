(** Size and array-framing contracts for arbitrary canonical Buffer63 chunks.
    These facts support the mixed absent/present actual C loop; they do not
    prove an individual jet or assume any helper execution. *)
From Coq Require Import List Lia ZArith.
From compcert Require Import Integers AST Memory.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_encoding.
Require Import C.jet_read8s_layout C.jet_write_buffer8_empty_run C.jet_write_buffer8_empty_cells.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition byte_chunk_values (chunk : byte_chunk) : list (Ty.tySem (Word 3)) :=
  match snd chunk with None => [] | Some xs => xs end.
Fixpoint byte_chunks_values (chunks : list byte_chunk) : list (Ty.tySem (Word 3)) :=
  match chunks with [] => [] | c :: cs => byte_chunk_values c ++ byte_chunks_values cs end.
Fixpoint byte_chunks_capacity (chunks : list byte_chunk) : nat :=
  match chunks with [] => 0%nat | c :: cs => (fst c + byte_chunks_capacity cs)%nat end.
Fixpoint byte_chunks_width (chunks : list byte_chunk) : Z :=
  match chunks with [] => 0 | c :: cs => 1 + 8 * Z.of_nat (fst c) + byte_chunks_width cs end.
Definition byte_chunks_sized := Forall (fun chunk : byte_chunk =>
  match snd chunk with None => True | Some xs => length xs = fst chunk end).
Fixpoint buffer_byte_counts (depth : nat) : list nat :=
  match depth with O => [1%nat] | S d => Nat.pow 2 (S d) :: buffer_byte_counts d end.

Lemma buffer_byte_chunks_counts depth (x : Ty.tySem (buffer_type (Word 3) depth)) :
  map fst (buffer_byte_chunks depth x) = buffer_byte_counts depth.
Proof.
  induction depth; [destruct x as [[]|x]; reflexivity|].
  destruct x as [head tail]. change (Nat.pow 2 (S depth) :: map fst (buffer_byte_chunks depth tail) =
    Nat.pow 2 (S depth) :: buffer_byte_counts depth). rewrite IHdepth; reflexivity.
Qed.

Lemma uint8_array_before_preserved m mf bo output xs next :
  output + Z.of_nat (length xs) <= next ->
  (forall ofs, ofs + 1 <= next -> Mem.load Mint8unsigned mf bo ofs = Mem.load Mint8unsigned m bo ofs) ->
  uint8_array_at m bo output xs -> uint8_array_at mf bo output xs.
Proof.
  intros Hnext HLoad HArray i x Hi. unfold uint8_array_at in HArray.
  assert (Hsmall : (i < length xs)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  rewrite HLoad; [exact (HArray i x Hi)|lia].
Qed.
Lemma buffer_byte_chunks_sized depth (x : Ty.tySem (buffer_type (Word 3) depth)) :
  byte_chunks_sized (buffer_byte_chunks depth x).
Proof. apply buffer_byte_chunks_lengths. Qed.
Lemma buffer63_chunks_chain (x : Ty.tySem (buffer_type (Word 3) 5)) :
  buffer8_empty_chain (map (fun c => Z.of_nat (fst c)) (buffer_byte_chunks 5 x)).
Proof.
  rewrite <- map_map, buffer_byte_chunks_counts.
  change (buffer8_empty_chain buffer63_empty_counts). apply buffer63_empty_counts_chain.
Qed.
Lemma byte_chunks_width_counts chunks :
  byte_chunks_width chunks = buffer8_empty_bits (map (fun c => Z.of_nat (fst c)) chunks).
Proof. induction chunks; [reflexivity|]. cbn [byte_chunks_width map buffer8_empty_bits]. rewrite IHchunks; reflexivity. Qed.
Lemma buffer63_chunks_width (x : Ty.tySem (buffer_type (Word 3) 5)) :
  byte_chunks_width (buffer_byte_chunks 5 x) = 510.
Proof.
  rewrite byte_chunks_width_counts, <- map_map, buffer_byte_chunks_counts. reflexivity.
Qed.
Lemma byte_chunks_capacity_counts chunks :
  byte_chunks_capacity chunks = fold_right Nat.add 0%nat (map fst chunks).
Proof. induction chunks; [reflexivity|]. cbn [byte_chunks_capacity map fold_right]. rewrite IHchunks; reflexivity. Qed.
Lemma buffer63_chunks_capacity (x : Ty.tySem (buffer_type (Word 3) 5)) :
  byte_chunks_capacity (buffer_byte_chunks 5 x) = 63%nat.
Proof. rewrite byte_chunks_capacity_counts, buffer_byte_chunks_counts. reflexivity. Qed.

Lemma byte_chunk_values_bound c :
  (match snd c with None => True | Some xs => length xs = fst c end) ->
  (length (byte_chunk_values c) <= fst c)%nat.
Proof. destruct c as [n [xs|]]; cbn [snd fst byte_chunk_values length]; intros; lia. Qed.
Lemma byte_chunks_values_bound chunks : byte_chunks_sized chunks ->
  (length (byte_chunks_values chunks) <= byte_chunks_capacity chunks)%nat.
Proof.
  intros HS. induction HS; [reflexivity|]. cbn [byte_chunks_values byte_chunks_capacity].
  rewrite app_length. pose proof (byte_chunk_values_bound x H). lia.
Qed.
Lemma encoded_byte_list_length xs :
  length (concat (map (@encode (Word 3)) xs)) = (8 * length xs)%nat.
Proof.
  induction xs as [|x xs IH]; [reflexivity|]. change (length (encode x ++ concat (map (@encode (Word 3)) xs)) =
    (8 * length (x :: xs))%nat). rewrite app_length, encode_word_length, IH. cbn [Nat.pow length]; lia.
Qed.
Lemma byte_chunk_cells_width c :
  (match snd c with None => True | Some xs => length xs = fst c end) ->
  Z.of_nat (length (byte_chunk_cells c)) = 1 + 8 * Z.of_nat (fst c).
Proof.
  destruct c as [n [xs|]]; cbn [snd fst byte_chunk_cells]; intros HS.
  - cbn [length]. rewrite encoded_byte_list_length, HS, Nat2Z.inj_succ, Nat2Z.inj_mul. lia.
  - cbn [length]. rewrite repeat_length, Nat2Z.inj_succ, Nat2Z.inj_mul. lia.
Qed.
Lemma byte_chunks_cells_width chunks : byte_chunks_sized chunks ->
  Z.of_nat (length (concat (map byte_chunk_cells chunks))) = byte_chunks_width chunks.
Proof.
  intros HS. induction HS; [reflexivity|]. change (Z.of_nat (length (byte_chunk_cells x ++ concat (map byte_chunk_cells l))) =
    1 + 8 * Z.of_nat (fst x) + byte_chunks_width l).
  rewrite app_length, Nat2Z.inj_add, byte_chunk_cells_width by exact H. rewrite IHHS. reflexivity.
Qed.

Lemma uint8_array_at_app m bo output xs ys :
  uint8_array_at m bo output (xs ++ ys) <->
  uint8_array_at m bo output xs /\ uint8_array_at m bo (output + Z.of_nat (length xs)) ys.
Proof.
  split.
  - intros H. split.
    + intros i x Hi. apply (H i x). rewrite nth_error_app1; [exact Hi|].
      apply nth_error_Some; rewrite Hi; discriminate.
    + intros i x Hi. replace (output + Z.of_nat (length xs) + Z.of_nat i) with
        (output + Z.of_nat (length xs + i)) by lia. apply H.
      rewrite nth_error_app2 by lia. replace (length xs + i - length xs)%nat with i by lia. exact Hi.
  - intros [HX HY] i x Hi. apply nth_error_app_split in Hi. destruct Hi as [[_ Hi]|[Hlen Hi]].
    + exact (HX i x Hi).
    + pose proof (HY (i - length xs)%nat x Hi) as H.
      replace (output + Z.of_nat (length xs) + Z.of_nat (i - length xs)) with
        (output + Z.of_nat i) in H by lia. exact H.
Qed.
