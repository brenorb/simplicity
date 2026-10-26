(** Reuse the original affine writer's checked normalization and get_b32
    expressions for the two coordinate serializations in generator_save. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_rename
  C.jet_secp_fe_nv C.jet_secp_fe_b32 C.jet_secp_fe_math C.jet_secp_frame
  C.jet_secp_write_fe_wrapper C.jet_secp_write_fe_numeric
  C.jet_secp_write_fe_wide_values C.jet_secp_generator_save.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition generator_save_shift (offset n:nat) := (n-1+offset)%nat.
Definition generator_save_condition offset := sx_rename (generator_save_shift offset)
  (write_fe_condition 1%positive Ptrofs.zero).
Definition generator_save_normalized offset state :=
  map (sx_rename (fun n=>(offset+n)%nat)) (map cell_sx (cells0 state)).
Definition generator_save_bytes offset (branch:bool) :=
  map (sx_rename (generator_save_shift offset))
    (if branch then write_fe_true_bytes 1%positive Ptrofs.zero
     else write_fe_false_bytes 1%positive Ptrofs.zero).
Fixpoint generator_save_byte_cells ofs bytes : list cell :=
  match bytes with
  | []=>[] | x::xs=>mkcell ofs Mint8unsigned (Some x)::generator_save_byte_cells (ofs+1) xs end.
Definition generator_save_choice rho beta offset := truth rho (lay beta) (generator_save_condition offset).
Definition generator_save_output_regs flag (x y:bool) :=
  [mkreg (u64_cells 0 (generator_save_normalized 0 (if x then nv_a else nv_b)) ++
          u64_cells 40 (generator_save_normalized 5 (if y then nv_a else nv_b)) ++
          [mkcell 80 Mint32 (Some (XI flag))]) true (Some 88);
   mkreg (generator_save_byte_cells 0 (generator_save_bytes 0 x) ++
          generator_save_byte_cells 32 (generator_save_bytes 5 y)) true (Some 64)].
Definition generator_save_final_regs flag rho beta := generator_save_output_regs flag
  (generator_save_choice rho beta 0) (generator_save_choice rho beta 5).
Definition generator_save_leaf flag (x y:bool) :=
  let rx:=match generator_save_result flag with RIf _ a b=>if x then a else b | r=>r end in
  let ry:=match rx with RIf _ a b=>if y then a else b | r=>r end in
  match ry with RDone st _=>st | _=>mkst (Maps.PTree.empty sx) [] [] 0 end.
Lemma generator_save_leaf_regs flag x y :
  sregs (generator_save_leaf flag x y)=generator_save_output_regs flag x y.
Proof. destruct x,y;reflexivity. Qed.

Lemma generator_save_selected_regs flag rho beta :
  sregs (fst (rsel rho (lay beta) (generator_save_result flag)))=
    generator_save_final_regs flag rho beta.
Proof.
  change (sregs (fst (if generator_save_choice rho beta 0 then
      if generator_save_choice rho beta 5 then (generator_save_leaf flag true true,ONormal)
      else (generator_save_leaf flag true false,ONormal)
    else if generator_save_choice rho beta 5 then (generator_save_leaf flag false true,ONormal)
      else (generator_save_leaf flag false false,ONormal)))=generator_save_final_regs flag rho beta).
  unfold generator_save_final_regs.
  destruct (generator_save_choice rho beta 0), (generator_save_choice rho beta 5);
    apply generator_save_leaf_regs.
Qed.

Definition generator_save_coord_rho rho offset := wide_fe_rho
  (rho offset) (rho (1+offset)%nat) (rho (2+offset)%nat)
  (rho (3+offset)%nat) (rho (4+offset)%nat) 0.
Definition generator_save_value rho offset :=
  fe_val (Int64.unsigned (rho offset)) (Int64.unsigned (rho (1+offset)%nat))
    (Int64.unsigned (rho (2+offset)%nat)) (Int64.unsigned (rho (3+offset)%nat))
    (Int64.unsigned (rho (4+offset)%nat)) mod feP.

Lemma generator_save_choice_as_writer rho beta offset :
  generator_save_choice rho beta offset=
    truth (generator_save_coord_rho rho offset) (lay beta) (write_fe_condition 1%positive Ptrofs.zero).
Proof. reflexivity. Qed.
Lemma generator_save_bytes_as_writer rho beta offset branch :
  map (fun x=>ii (den rho (lay beta) x)) (generator_save_bytes offset branch)=
    map (fun x=>ii (den (generator_save_coord_rho rho offset) (lay beta) x))
      (if branch then write_fe_true_bytes 1%positive Ptrofs.zero
       else write_fe_false_bytes 1%positive Ptrofs.zero).
Proof. destruct branch;reflexivity. Qed.
Theorem generator_save_machine_bytes rho beta offset :
  (forall i,(i<5)%nat -> Int64.unsigned (rho (i+offset)%nat)<=2^60) ->
  map (fun x=>ii (den rho (lay beta) x))
    (generator_save_bytes offset (generator_save_choice rho beta offset))=
    map Int.repr (be_bytes (generator_save_value rho offset)).
Proof.
  intro Bounds;rewrite generator_save_bytes_as_writer,generator_save_choice_as_writer.
  change (map (fun x=>ii (den (generator_save_coord_rho rho offset) (lay beta) x))
    (write_fe_selected_bytes (generator_save_coord_rho rho offset) (lay beta) 1%positive Ptrofs.zero)=
    map Int.repr (be_bytes (generator_save_value rho offset))).
  apply wide_write_selected_machine_bytes.
  - exact (Bounds 0%nat ltac:(lia)).
  - exact (Bounds 1%nat ltac:(lia)).
  - exact (Bounds 2%nat ltac:(lia)).
  - exact (Bounds 3%nat ltac:(lia)).
  - exact (Bounds 4%nat ltac:(lia)).
Qed.
Lemma generator_save_bytes_length offset branch : length (generator_save_bytes offset branch)=32%nat.
Proof. destruct branch;reflexivity. Qed.

Lemma generator_save_bytes_are_int rho beta offset branch :
  Forall (fun x=>den rho (lay beta) x=Vint (ii (den rho (lay beta) x)))
    (generator_save_bytes offset branch).
Proof. destruct branch;repeat constructor;reflexivity. Qed.
Lemma generator_save_byte_value rho beta offset i expr :
  (forall j,(j<5)%nat -> Int64.unsigned (rho (j+offset)%nat)<=2^60) ->
  nth_error (generator_save_bytes offset (generator_save_choice rho beta offset)) i=Some expr ->
  den rho (lay beta) expr=
    Vint (nth i (map Int.repr (be_bytes (generator_save_value rho offset))) Int.zero).
Proof.
  intros Bounds Nth.
  assert (Typed:den rho (lay beta) expr=Vint (ii (den rho (lay beta) expr))).
  { apply (proj1 (Forall_forall _ _) (generator_save_bytes_are_int rho beta offset
      (generator_save_choice rho beta offset)) expr).
    eapply nth_error_In;exact Nth. }
  assert (Number:nth_error (map Int.repr (be_bytes (generator_save_value rho offset))) i=
      Some (ii (den rho (lay beta) expr))).
  { rewrite <- (generator_save_machine_bytes rho beta offset Bounds),nth_error_map,Nth;reflexivity. }
  rewrite Typed,(@nth_error_nth int _ _ _ Int.zero Number);reflexivity.
Qed.
Lemma generator_save_byte_cell_member bytes : forall ofs i x,
  nth_error bytes i=Some x ->
  In (mkcell (ofs+Z.of_nat i) Mint8unsigned (Some x)) (generator_save_byte_cells ofs bytes).
Proof.
  induction bytes as [|head tail IH];intros ofs [|i] x Nth;try discriminate Nth.
  - injection Nth as <-;rewrite Z.add_0_r;left;reflexivity.
  - right;replace (ofs+Z.of_nat (S i)) with (ofs+1+Z.of_nat i) by lia;apply IH;exact Nth.
Qed.
