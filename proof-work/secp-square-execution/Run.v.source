(** Execution foundation for the actual optimized C squaring implementation.
    This is not yet a complete public square-jet equivalence: its numeric
    output-to-square bridge and public lifecycle remain to be proved. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Values Memory Events.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jet_toZ C.jet_secp_fe_math C.jet_secp_negate_literal_contract
  C.jet_secp_multiply_literal_spec.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_multiply_run_run.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition square_regs : list region :=
  [mkreg (u64_cells 0 [XLv 0;XLv 1;XLv 2;XLv 3;XLv 4]) true (Some 40)].
Definition square_run := xfun (genv_cenv secp_ge) [] field_table 400
  f_secp256k1_fe_sqr [XP 0 0;XP 0 0] square_regs [] 5.
Lemma square_completes :
  match square_run with Some (RDone _ ONormal) => true | _ => false end = true.
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Definition square_state := match square_run with
  | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Lemma square_run_eq : square_run = Some (RDone square_state ONormal).
Proof.
  pose proof square_completes as H; unfold square_state.
  destruct square_run as [r|]; [|discriminate].
  destruct r; [destruct o; try discriminate; reflexivity|discriminate].
Qed.
Lemma square_return : (stemps square_state)!1%positive = None.
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Definition square_out := hd (mkreg [] false None) (sregs square_state).
Definition square_limbs := map field_cell_value (rcells square_out).
Lemma square_regions_count : length (sregs square_state) = 1%nat.
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Lemma square_out_shape : rshape square_out =
  ([(0,Mint64);(8,Mint64);(16,Mint64);(24,Mint64);(32,Mint64)], true, Some 40).
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Lemma square_out_defined : field_cells_defined (rcells square_out) = true.
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Lemma square_limbs_count : length square_limbs = 5%nat.
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Lemma square_out_rebuild : square_out = mkreg (u64_cells 0 square_limbs) true (Some 40).
Proof.
  pose proof square_out_shape as HS; pose proof square_out_defined as HD.
  change (square_out = mkreg (u64_cells 0 (map field_cell_value (rcells square_out))) true (Some 40)).
  destruct square_out as [cs writable freed]; cbn [rshape rcells rw rfree] in HS.
  injection HS as HC HW HF; subst writable freed.
  assert (HN : length cs = 5%nat).
  { apply (f_equal (@length (Z * memory_chunk))) in HC; rewrite map_length in HC; exact HC. }
  f_equal; change (cs = u64_cells 0 (map field_cell_value cs)).
  apply field_cells_rebuild; [rewrite HN; exact HC|exact HD].
Qed.
Lemma square_output : sregs square_state = [mkreg (u64_cells 0 square_limbs) true (Some 40)].
Proof.
  pose proof square_regions_count as HC.
  assert (HE : sregs square_state = [square_out]).
  { unfold square_out; destruct (sregs square_state) as [|r [|r' rest]]; cbn in HC; try discriminate; reflexivity. }
  rewrite HE, square_out_rebuild; reflexivity.
Qed.

Local Opaque secp_ge square_state square_limbs.
Theorem eval_original_square_owned_inplace rho layout m :
  rep rho layout square_regs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
       Vptr (blk layout 0) (Ptrofs.repr (bas layout 0))] E0 mf Vundef /\
    rep rho layout [mkreg (u64_cells 0 square_limbs) true (Some 40)] mf /\
    lframe (fun b ofs => ~ foot layout (map rshape square_regs) b ofs) m mf.
Proof.
  intro HR.
  destruct (field_fun_sound 400 f_secp256k1_fe_sqr [XP 0 0;XP 0 0] square_regs 5
    (RDone square_state ONormal) square_run_eq rho layout m HR)
    as (mf & vres & HC & HP & HReturn & HShape & HF).
  cbn [rsel fst] in HP, HReturn.
  rewrite square_return in HReturn; subst vres; rewrite square_output in HP.
  change (map (den rho (lay layout)) [XP 0 0;XP 0 0]) with
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + 0));
     Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + 0))] in HC.
  rewrite !Z.add_0_r in HC.
  exists mf; split; [exact HC|]; split; assumption.
Qed.

Local Open Scope term_scope.
Definition literal_fe_square {term : Alg.Core.Algebra} : term (Word 8) (Word 8) :=
  iden &&& iden >>> @literal_fe_multiply term.
Lemma literal_square_step x : @literal_fe_square Alg.CoreFunSem x =
  @literal_fe_multiply Alg.CoreFunSem (x,x).
Proof. reflexivity. Qed.
Lemma literal_square_numeric x : @toZ (WordToZ 8) (@literal_fe_square Alg.CoreFunSem x) =
  (@toZ (WordToZ 8) x * @toZ (WordToZ 8) x) mod feP.
Proof. rewrite literal_square_step; apply literal_multiply_numeric. Qed.
