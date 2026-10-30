(** Reuse the real generic function's eleven allocations and frees with the
    linked layout; all sizeof agreement is discharged, not assumed by callers. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_taptweak_entry
 C.jet_transport C.jet_sx_mem C.jet_elements_taptweak_pure
 C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma elements_taptweak_entry_vars_checked:
 vars_okb secp_ge elements_taptweak_ge (fn_vars f_simplicity_generic_taptweak)=true.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_entry_sizes:
 sizeof (genv_cenv elements_taptweak_ge) (Tstruct _sha256_context noattr)=88 /\
 sizeof (genv_cenv elements_taptweak_ge) (Tstruct _sha256_midstate noattr)=32 /\
 sizeof (genv_cenv elements_taptweak_ge) (Tstruct __2078 noattr)=64 /\
 sizeof (genv_cenv elements_taptweak_ge) (Tstruct __6478 noattr)=64.
Proof. vm_compute;repeat split;reflexivity. Qed.
Local Opaque secp_ge elements_taptweak_ge.
Lemma elements_taptweak_blocks bb bi bo bp bt bh bs bc bc1 br br1:
 blocks_of_env elements_taptweak_ge (taptweak_env bb bi bo bp bt bh bs bc bc1 br br1)=
 [(bs,0,32);(bo,0,64);(bc1,0,88);(bc,0,88);(bh,0,32);(bi,0,64);
 (br1,0,88);(br,0,88);(bp,0,64);(bt,0,32);(bb,0,32)].
Proof.
 change ([(bs,0,sizeof elements_taptweak_ge (Tstruct _sha256_midstate noattr));
 (bo,0,sizeof elements_taptweak_ge (Tstruct __6478 noattr));
 (bc1,0,sizeof elements_taptweak_ge (Tstruct _sha256_context noattr));
 (bc,0,sizeof elements_taptweak_ge (Tstruct _sha256_context noattr));
 (bh,0,sizeof elements_taptweak_ge (Tstruct _sha256_midstate noattr));
 (bi,0,sizeof elements_taptweak_ge (Tstruct __6478 noattr));
 (br1,0,sizeof elements_taptweak_ge (Tstruct _sha256_context noattr));
 (br,0,sizeof elements_taptweak_ge (Tstruct _sha256_context noattr));
 (bp,0,sizeof elements_taptweak_ge (Tstruct __2078 noattr));
 (bt,0,sizeof elements_taptweak_ge (Tstruct _sha256_midstate noattr));(bb,0,32)]=
 [(bs,0,32);(bo,0,64);(bc1,0,88);(bc,0,88);(bh,0,32);(bi,0,64);
 (br1,0,88);(br,0,88);(bp,0,64);(bt,0,32);(bb,0,32)]).
 destruct elements_taptweak_entry_sizes as (Context & State & Opaque & Xonly).
 rewrite Context,State,Opaque,Xonly;reflexivity.
Qed.
Theorem elements_taptweak_entry m vd vs vt vn:exists mi bb bi bo bp bt bh bs bc bc1 br br1,
 function_entry2 elements_taptweak_ge f_simplicity_generic_taptweak [vd;vs;vt;vn] m
 (taptweak_env bb bi bo bp bt bh bs bc bc1 br br1) (taptweak_temps vd vs vt vn) mi /\
 NoDup (taptweak_locals bb bi bo bp bt bh bs bc bc1 br br1) /\
 (forall b,Mem.valid_block m b ->~In b (taptweak_locals bb bi bo bp bt bh bs bc bc1 br br1)) /\
 (forall b hi,In (b,hi) (taptweak_storage bb bi bo bp bt bh bs bc bc1 br br1) ->Mem.range_perm mi b 0 hi Cur Freeable) /\
 lframe (fun _ _=>True) m mi /\keeps_permissions m mi /\readonly_preserved m mi.
Proof.
 destruct (taptweak_entry m vd vs vt vn) as
 (mi & bb & bi & bo & bp & bt & bh & bs & bc & bc1 & br & br1 & Entry & Memory).
 exists mi,bb,bi,bo,bp,bt,bh,bs,bc,bc1,br,br1;split;[|exact Memory].
 inversion Entry as [Vars Params Disjoint Alloc Bind];subst.
 constructor;[exact Vars|exact Params|exact Disjoint| |exact Bind].
 eapply (alloc_variables_transport secp_ge elements_taptweak_ge);
 [exact Alloc|exact elements_taptweak_entry_vars_checked].
Qed.
Theorem elements_taptweak_free m bb bi bo bp bt bh bs bc bc1 br br1:
 NoDup (taptweak_locals bb bi bo bp bt bh bs bc bc1 br br1) ->
 (forall b hi,In (b,hi) (taptweak_storage bb bi bo bp bt bh bs bc bc1 br br1) ->Mem.range_perm m b 0 hi Cur Freeable) ->
 exists mf,Mem.free_list m (blocks_of_env elements_taptweak_ge (taptweak_env bb bi bo bp bt bh bs bc bc1 br br1))=Some mf /\
 lframe (fun b _=>~In b (taptweak_locals bb bi bo bp bt bh bs bc bc1 br br1)) m mf /\readonly_preserved m mf.
Proof.
 intros Separate Owned;destruct(taptweak_free m bb bi bo bp bt bh bs bc bc1 br br1 Separate Owned)
 as(mf & Frees & Memory);exists mf;split;[|exact Memory].
 rewrite elements_taptweak_blocks,taptweak_blocks in *;exact Frees.
Qed.
