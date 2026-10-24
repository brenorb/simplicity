(** Actual computed-index assignment with a checked symbolic source/store. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_modinv_fg_index C.jet_secp_u128_shift64_rep.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem exec_fg_symbolic_index_store rho beta e le m st ve id r reg ix k src term regs' :
 rep rho beta (sregs st) m -> tmatch rho beta (stemps st) le -> ematch beta ve e ->
 nth_error (sregs st) r=Some reg -> rfree reg=Some 40 ->
 (stemps st)!id=Some (XP r 0) ->
 0<=k<5 -> typeof ix=tint -> typeof src=tulong ->
 eval_expr secp_ge e le m ix (Vint (Int.repr k)) ->
 xexpr (genv_cenv secp_ge) ve [] st src=Some term -> isk KL term=true ->
 xstore (sregs st) r (8*k) Mint64 term=Some regs' -> exists mf,
 Clight2.exec_stmt secp_ge e le m (Sassign (fg_index id ix) src) E0 le mf Out_normal /\
 rep rho beta regs' mf /\ map rshape regs'=map rshape (sregs st) /\
 lframe (fun b ofs=>~foot beta (map rshape (sregs st)) b ofs) m mf.
Proof.
 intros Rep Temps Env Region Owned Pointer Bound Ty Src Index Expr Kind Store.
 pose proof (rep_owned_region_base_zero rho beta (sregs st) m r reg 40 Rep Region Owned) as Base.
 pose proof (Temps id (XP r 0) Pointer) as Ptr.
 change (le!id=Some (Vptr (blk beta r) (Ptrofs.repr (bas beta r+0)))) in Ptr.
 rewrite Base,Z.add_0_l in Ptr;change (Ptrofs.repr 0) with Ptrofs.zero in Ptr.
 assert (Value : eval_expr secp_ge e le m src (den rho (lay beta) term)).
 { eapply (xexpr_sound secp_ge ve [] rho beta st m e le Rep Temps Env).
   - intros i rr ty H;discriminate.
   - exact Expr. }
 destruct (xstore_sound rho beta (sregs st) m r (8*k) Mint64 term regs' Rep Store)
  as (mf & Write & Addr & Out & Frame).
 rewrite Base,Z.add_0_l,(den_KL rho (lay beta) term Kind) in Write.
 rewrite (den_KL rho (lay beta) term Kind) in Value.
 exists mf;split.
 - eapply exec_fg_index_store;[exact Bound|exact Ty|exact Src|exact Ptr|exact Index|exact Value|exact Write].
 - split;[exact Out|];split;[eapply xstore_shape;exact Store|].
   apply lframe_unchanged;exact Frame.
Qed.
