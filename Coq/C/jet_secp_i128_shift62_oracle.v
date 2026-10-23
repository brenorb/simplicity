(** A proved summary for original signed rshift(62), for inverse batches.
    This is not an assumed external function: correctness executes the C body. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Events Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_mem C.jet_sx_exec C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_u128_shift64_rep.
Require Import C.jet_secp_i128_shift62_rep.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition i128_shift62_oracle : oracle := fun base log xs regs =>
  match xs with
  | [arg0; arg1] => match arg0, arg1 with
    | XP r offset, XIc count =>
      if Z.eqb offset 0 && Int.eq count (Int.repr 62) then
        match nth_error regs r with
        | Some reg => match rfree reg with
          | Some sz => if Z.eqb sz 16 then
              match xload regs r 0 tulong, xload regs r 8 tulong with
              | Some lo, Some hi => if isk KL lo && isk KL hi then
                  match xstore regs r 0 Mint64 (i128_shift62_lo_sx lo hi) with
                  | Some regs1 => match xstore regs1 r 8 Mint64 (i128_shift62_hi_sx hi) with
                    | Some regs2 => Some (regs2, None, 0%nat, 0%nat, [])
                    | None => None end
                  | None => None end
                else None
              | _, _ => None end else None
          | None => None end
        | None => None end
      else None
    | _, _ => None end
  | _ => None end.

Theorem i128_shift62_oracle_correct :
  oracle_ok secp_ge (fun _ _ => True) (fun _ _ _ => True) (fun _ => False)
    f_secp256k1_i128_rshift i128_shift62_oracle.
Proof.
  unfold oracle_ok, i128_shift62_oracle.
  intros base xs regs regs' v tag cnt eargs log rho layout m HRun HRep HSep HInv HSol HEv.
  destruct xs as [|arg0 [|arg1 [|extra tail]]]; try discriminate.
  destruct arg0; try discriminate. destruct arg1; try discriminate.
  destruct (Z.eqb d 0 && Int.eq i (Int.repr 62)) eqn:HA; [|discriminate].
  apply andb_true_iff in HA; destruct HA as [HO HC].
  apply Z.eqb_eq in HO; subst d. apply Int.same_if_eq in HC; subst i.
  destruct (nth_error regs r) as [reg|] eqn:HR; [|discriminate].
  destruct (rfree reg) as [sz|] eqn:HF; [|discriminate].
  destruct (Z.eqb sz 16) eqn:HZ; [|discriminate]. apply Z.eqb_eq in HZ; subst sz.
  destruct (xload regs r 0 tulong) as [lo|] eqn:HL; [|discriminate].
  destruct (xload regs r 8 tulong) as [hi|] eqn:HH; [|discriminate].
  destruct (isk KL lo && isk KL hi) eqn:HK; [|discriminate].
  apply andb_true_iff in HK; destruct HK as [HKL HKH].
  destruct (xstore regs r 0 Mint64 (i128_shift62_lo_sx lo hi)) as [regs1|] eqn:HS1; [|discriminate].
  destruct (xstore regs1 r 8 Mint64 (i128_shift62_hi_sx hi)) as [regs2|] eqn:HS2; [|discriminate].
  inversion HRun; subst regs' v tag cnt eargs.
  destruct (eval_i128_shift62_symbolic_stores rho layout regs m r reg lo hi regs1 regs2
    HRep HR HF HL HH HKL HKH HS1 HS2) as (mf & HCall & HFinal & HShape & HFrame).
  pose proof (rep_owned_region_base_zero rho layout regs m r reg 16 HRep HR HF) as HB.
  exists mf, Vundef; split.
  - cbn [map den]; fold (blk layout r) (bas layout r). rewrite HB; exact HCall.
  - split; [exact HFinal|]; split; [exact I|]; split; [exact HShape|]; split; [reflexivity|].
    eapply lframe_implies; [exact HFrame|]. intros b ofs [_ [HOutside _]] _; exact HOutside.
Qed.
