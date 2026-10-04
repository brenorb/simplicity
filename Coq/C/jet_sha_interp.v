(** A small verified interpreter for the statement fragment used by the
    generated body of [sha256_compression_portable]: integer temporaries,
    the eight address-taken locals, reads of the two argument arrays, calls
    to sigma0/sigma1 and Round, and the final stores into the state array.
    [interp_sound] turns a successful interpretation into an actual Clight
    big-step execution in the SHA translation unit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_round.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque sha_ge.
Set Default Timeout 120.

Definition wids : list ident :=
  [_w0; _w1; _w2; _w3; _w4; _w5; _w6; _w7; _w8; _w9; _w10; _w11; _w12; _w13; _w14; _w15].
Definition lids : list ident := [_a; _b; _c; _d; _e; _f; _g; _h].

Fixpoint index_of (x : ident) (l : list ident) : option nat :=
  match l with
  | [] => None
  | y :: t => if Pos.eqb x y then Some 0%nat else option_map S (index_of x t)
  end.

Fixpoint alookup (l : list (ident * int)) (x : ident) : option int :=
  match l with
  | [] => None
  | (y, v) :: t => if Pos.eqb x y then Some v else alookup t x
  end.

Fixpoint upd {A} (l : list A) (i : nat) (v : A) : list A :=
  match l, i with
  | [], _ => []
  | _ :: t, O => v :: t
  | x :: t, S i => x :: upd t i v
  end.

Record cst : Type := mk_cst {
  wv : list int; wdef : nat; lv : list int; ldef : nat;
  scratch : list (ident * int); sarr : list int; chunk : list int }.

Definition is_tuint (ty : type) : bool := if type_eq ty tuint then true else false.
Definition is_tint (ty : type) : bool := if type_eq ty tint then true else false.
Definition is_ptuint (ty : type) : bool := if type_eq ty (tptr tuint) then true else false.

Definition arr_read (st : cst) (p : ident) (i : int) : option int :=
  let k := Z.to_nat (Int.unsigned i) in
  if Pos.eqb p _s then (if (k <? 8)%nat then Some (nth k (sarr st) Int.zero) else None)
  else if Pos.eqb p _chunk then (if (k <? 16)%nat then Some (nth k (chunk st) Int.zero) else None)
  else None.

Definition arr_expr (e : expr) : option (ident * int) :=
  match e with
  | Ebinop Oadd (Etempvar p pty) (Econst_int i ity) aty =>
      if is_ptuint pty && is_tint ity && is_ptuint aty then Some (p, i) else None
  | _ => None
  end.

Definition addr_local (e : expr) : option nat :=
  match e with
  | Eaddrof (Evar x ty) pty => if is_tuint ty && is_ptuint pty then index_of x lids else None
  | _ => None
  end.

Fixpoint eval_ie (st : cst) (e : expr) : option int :=
  match e with
  | Etempvar t ty =>
      if is_tuint ty then
        match index_of t wids with
        | Some i => if (i <? wdef st)%nat then Some (nth i (wv st) Int.zero) else None
        | None => alookup (scratch st) t
        end
      else None
  | Econst_int n ty => if is_tuint ty then Some n else None
  | Ebinop op a b ty =>
      if is_tuint ty then
        match eval_ie st a, eval_ie st b with
        | Some va, Some vb =>
            match op with Oadd => Some (Int.add va vb) | Omul => Some (Int.mul va vb) | _ => None end
        | _, _ => None
        end
      else None
  | Ecast a ty => if is_tuint ty then eval_ie st a else None
  | Evar x ty =>
      if is_tuint ty then
        match index_of x lids with
        | Some i => if (i <? ldef st)%nat then Some (nth i (lv st) Int.zero) else None
        | None => None
        end
      else None
  | Ederef a ty =>
      if is_tuint ty then
        match arr_expr a with Some (p, i) => arr_read st p i | None => None end
      else None
  | _ => None
  end.

Definition set_temp (st : cst) (t : ident) (v : int) : option cst :=
  match index_of t wids with
  | Some i =>
      if (i <=? wdef st)%nat
      then Some (mk_cst (upd (wv st) i v) (Nat.max (wdef st) (S i)) (lv st) (ldef st) (scratch st) (sarr st) (chunk st))
      else None
  | None =>
      if Pos.eqb t _s || Pos.eqb t _chunk then None
      else Some (mk_cst (wv st) (wdef st) (lv st) (ldef st) ((t, v) :: scratch st) (sarr st) (chunk st))
  end.

Definition set_local (st : cst) (i : nat) (v : int) : cst :=
  mk_cst (wv st) (wdef st) (upd (lv st) i v) (Nat.max (ldef st) (S i)) (scratch st) (sarr st) (chunk st).

Definition sigma_ty : type := Tfunction (Tcons tuint Tnil) tuint cc_default.
Definition round_ty : type :=
  Tfunction (Tcons tuint (Tcons tuint (Tcons tuint (Tcons (tptr tuint) (Tcons tuint (Tcons tuint
    (Tcons tuint (Tcons (tptr tuint) (Tcons tuint Tnil))))))))) tvoid cc_default.

Definition interp_assign (st : cst) (lhs e : expr) : option cst :=
  match lhs with
  | Evar x ty =>
      if is_tuint ty then
        match index_of x lids, eval_ie st e with
        | Some i, Some v => if (i <=? ldef st)%nat then Some (set_local st i v) else None
        | _, _ => None
        end
      else None
  | Ederef a ty =>
      if is_tuint ty then
        match arr_expr a, eval_ie st e with
        | Some (p, i), Some v =>
            let k := Z.to_nat (Int.unsigned i) in
            if Pos.eqb p _s && (k <? 8)%nat
            then Some (mk_cst (wv st) (wdef st) (lv st) (ldef st) (scratch st) (upd (sarr st) k v) (chunk st))
            else None
        | _, _ => None
        end
      else None
  | _ => None
  end.

Definition interp_sigma (st : cst) (t f : ident) (fty : type) (a : expr) : option cst :=
  if type_eq fty sigma_ty then
    match eval_ie st a with
    | Some v =>
        if Pos.eqb f _sigma0 then set_temp st t (c_sigma0 v)
        else if Pos.eqb f _sigma1 then set_temp st t (c_sigma1 v)
        else None
    | None => None
    end
  else None.

Definition interp_round (st : cst) (f : ident) (fty : type) (a b c d e f' g h k : expr) : option cst :=
  if type_eq fty round_ty then
  if Pos.eqb f _Round then
    match eval_ie st a, eval_ie st b, eval_ie st c, eval_ie st e, eval_ie st f', eval_ie st g,
          eval_ie st k, addr_local d, addr_local h with
    | Some va, Some vb, Some vc, Some ve, Some vf, Some vg, Some vk, Some id, Some ih =>
        if (id <? ldef st)%nat && (ih <? ldef st)%nat && negb (Nat.eqb id ih) then
          let dv := nth id (lv st) Int.zero in
          let hv := nth ih (lv st) Int.zero in
          let t1 := c_T1 hv ve vf vg vk in
          Some (mk_cst (wv st) (wdef st)
            (upd (upd (lv st) id (Int.add dv t1)) ih (Int.add t1 (c_T2 va vb vc)))
            (ldef st) (scratch st) (sarr st) (chunk st))
        else None
    | _, _, _, _, _, _, _, _, _ => None
    end
  else None else None.

Fixpoint interp (s : statement) (st : cst) : option cst :=
  match s with
  | Ssequence a b => match interp a st with Some st1 => interp b st1 | None => None end
  | Sset t e => match eval_ie st e with Some v => set_temp st t v | None => None end
  | Sassign lhs e => interp_assign st lhs e
  | Scall (Some t) (Evar f fty) (a :: nil) => interp_sigma st t f fty a
  | Scall None (Evar f fty) (a :: b :: c :: d :: e :: f' :: g :: h :: k :: nil) =>
      interp_round st f fty a b c d e f' g h k
  | _ => None
  end.

Definition reset (st : cst) : cst :=
  mk_cst (wv st) (wdef st) (lv st) (ldef st) [] (sarr st) (chunk st).

(** Interpretation along the right spine, forgetting scratch temporaries
    between spine elements. *)
Fixpoint interp_spine (fuel : nat) (s : statement) (st : cst) : option cst :=
  match fuel with
  | O => interp s (reset st)
  | S fuel =>
      match s with
      | Ssequence a b =>
          match interp a (reset st) with Some st1 => interp_spine fuel b st1 | None => None end
      | _ => interp s (reset st)
      end
  end.

(** * Generic list facts *)
Lemma upd_length {A} (l : list A) i v : length (upd l i v) = length l.
Proof. revert i; induction l as [|x t IH]; intros [|i]; cbn; auto. Qed.

Lemma nth_upd_same {A} (l : list A) i v d : (i < length l)%nat -> nth i (upd l i v) d = v.
Proof. revert i; induction l as [|x t IH]; intros [|i] H; cbn in *; try lia; auto. apply IH; lia. Qed.

Lemma nth_upd_other {A} (l : list A) i j v d : i <> j -> nth j (upd l i v) d = nth j l d.
Proof.
  revert i j; induction l as [|x t IH]; intros [|i] [|j] H; cbn; auto; try congruence.
Qed.

Lemma index_of_nth x l i : index_of x l = Some i -> nth_error l i = Some x.
Proof.
  revert i; induction l as [|y t IH]; intros i H; cbn in H; [discriminate|].
  destruct (Pos.eqb_spec x y) as [->|N].
  - injection H as <-. reflexivity.
  - destruct (index_of x t) as [j|]; [|discriminate]. cbn in H. injection H as <-. cbn. apply IH. reflexivity.
Qed.

Lemma index_of_lt x l i : index_of x l = Some i -> (i < length l)%nat.
Proof. intros H. apply index_of_nth in H. apply nth_error_Some. rewrite H. discriminate. Qed.

Lemma index_of_none x l : index_of x l = None -> ~ In x l.
Proof.
  induction l as [|y t IH]; intros H HI; cbn in *; [exact HI|].
  destruct (Pos.eqb_spec x y) as [->|N]; [discriminate|].
  destruct (index_of x t); [cbn in H; discriminate|]. destruct HI as [E|HI]; [congruence|]. exact (IH eq_refl HI).
Qed.

Lemma nth_error_inj_nodup {A} (l : list A) i j x :
  NoDup l -> nth_error l i = Some x -> nth_error l j = Some x -> i = j.
Proof.
  intros HN Hi Hj. apply (proj1 (NoDup_nth_error l) HN); [|congruence].
  apply nth_error_Some. rewrite Hi. discriminate.
Qed.

Lemma wids_nodup : NoDup wids.
Proof.
  apply NoDup_nth_error. intros i j Hi Hij. cbn in Hi.
  do 16 (destruct i as [|i]; [do 16 (destruct j as [|j]; [first [reflexivity|vm_compute in Hij; discriminate]|]);
    cbn in Hij; destruct j; discriminate|]). cbn in Hi. lia.
Qed.

Lemma lids_nodup : NoDup lids.
Proof.
  apply NoDup_nth_error. intros i j Hi Hij. cbn in Hi.
  do 8 (destruct i as [|i]; [do 8 (destruct j as [|j]; [first [reflexivity|vm_compute in Hij; discriminate]|]);
    cbn in Hij; destruct j; discriminate|]). cbn in Hi. lia.
Qed.
