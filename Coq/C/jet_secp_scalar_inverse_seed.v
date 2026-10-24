(** Establish scalar inverse initialization from the real packed caller.
    This stops before divsteps: no matrix result, CTZ or loop execution is
    assumed. The actual five new objects and fourteen statements are proved. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_exec C.jet_sx_eval C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_modinv_entry_modulus
 C.jet_secp_modinv_copies_modulus C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_copies
 C.jet_secp_modinv_var_seed C.jet_secp_modinv_de_numeric C.jet_secp_modinv_de_correction_numeric
 C.jet_secp_modinv_normalize62_modulus C.jet_secp_modinv_normalize62_words
 C.jet_secp_scalar_de_ranges C.jet_secp_scalar_de_invariant C.jet_secp_scalar_normalize62
 C.jet_secp_modinfo_scalar_global C.jet_secp_scalar_inverse_caller C.jet_secp_scalar_inverse_result
 C.jet_secp_canonical_scalar C.jet_secp_signed62_numeric C.jet_secp_scalar_signed62
 C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_add_initial C.jet_secp_scalar_overflow_numeric
 C.jet_secp_fe_nv C.jet_secp_point_mul_storage C.jet_secp_multiply_finish_product
 C.jet_secp_multiply_normalize_bridge C.jet_secp_u128_shift64_rep C.divstep.
Require Import C.jet_secp_b32_exec.
Require Import C.jet_secp_modinv_seed_modulus C.jet_secp_modinv_var_de C.jet_secp_modinv_var_fg
 C.jet_secp_modinv_var_invariant C.jet_secp_modinv_var_ranges.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma scalar_inv_start_words : inv_mod_words modinfo_scalar_limb=modinfo_scalar_words.
Proof. reflexivity. Qed.
Lemma scalar_inv_start_rep w m bs : bs<>scalar_inv_modinfo_block -> fe_at m bs 0 (words5 w) ->
 Mem.range_perm m bs 0 40 Cur Freeable -> modinfo_scalar_global_rep m ->
 rep w [(bs,0);(scalar_inv_modinfo_block,0)] (inv_mod_start_regs modinfo_scalar_limb) m.
Proof.
 intros Sep Field Free(Valid & Read & Loads).
 apply two_region_rep_separate;[reflexivity|exact Sep| |].
 - apply owned_field_slice_region;[reflexivity|lia|lia|exact Field|exact Free].
 - change(region_ok w [(bs,0);(scalar_inv_modinfo_block,0)] m 1
    (mkreg(u64_cells 0 (map XLc(inv_mod_words modinfo_scalar_limb))) false None)).
   rewrite scalar_inv_start_words;apply region_u64;cbn [bas blk lay nth fst snd].
   + lia.
   + exists 0;reflexivity.
   + change(48<=18446744073709551615);lia.
   + exact Valid.
   + exact Read.
   + intros i x At;rewrite nth_error_map in At.
     destruct(nth_error modinfo_scalar_words i) as[v|] eqn:Word;[|discriminate].
     injection At as <-;split;[exact(Loads i v Word)|reflexivity].
Qed.

Definition scalar_inv_seed_state w := init canonical_group_order (signed62_unsigned_value w) scalar_inv_modulus_odd.
Lemma scalar_inv_seed_de_bounds later : scalar_de62_state_bounds(inv_initial_de_rho later).
Proof.
 split.
 - intros high i I;rewrite inv_initial_de_word by exact I.
   unfold inv_init_word;destruct(high && Nat.eqb i 0);
    [change(-(2^62-1)<=1<=2^62-1)|change(-(2^62-1)<=0<=2^62-1)];lia.
 - intro high;rewrite inv_initial_de_value;destruct high;unfold canonical_group_order;lia.
Qed.
Lemma scalar_inv_seed_link w later : scalar_de62_coefficient_link (signed62_unsigned_value w)
 (inv_initial_de_rho later) (scalar_inv_seed_state w).
Proof.
 intro high;rewrite inv_initial_de_value;destruct high.
 - rewrite Z.mul_1_r;reflexivity.
 - rewrite Z.mul_0_r,Zmod_0_l;change(0=canonical_group_order mod canonical_group_order).
   rewrite Z.mod_same by exact scalar_inv_modulus_nonzero;reflexivity.
Qed.
Lemma scalar_inv_seed_zero later : de62_input_value (inv_initial_de_rho later) false mod canonical_group_order=0.
Proof. rewrite inv_initial_de_value,Zmod_0_l;reflexivity. Qed.
Lemma scalar_inv_seed_values w : signed62_normalized w ->
 norm62_value_z 4 (fun i=>Int64.signed(modinfo_scalar_limb i))=f(scalar_inv_seed_state w) /\
 norm62_value_z 4 (fun i=>Int64.signed(w i))=g(scalar_inv_seed_state w) /\
 delta(scalar_inv_seed_state w)=1 /\ eta(scalar_inv_seed_state w)= -1 /\
 Z.abs(f(scalar_inv_seed_state w))<=2^256 /\ Z.abs(g(scalar_inv_seed_state w))<=2^256.
Proof.
 intro Bounds;pose proof(inv_seed_input_range w Bounds) as Range.
 split;[exact scalar_norm62_modulus_value|];split;[apply inv_seed_input_value;exact Bounds|].
 change(1=1 /\ -1= -1 /\ Z.abs canonical_group_order<=2^256 /\ Z.abs(signed62_unsigned_value w)<=2^256).
 rewrite !Z.abs_eq by(unfold canonical_group_order in *;lia);unfold canonical_group_order;repeat split;lia.
Qed.

Lemma scalar_inv_seed_fg_bounds w : signed62_normalized w -> forall (high : bool) i,(i<5)%nat ->
 Z.abs(Int64.signed(if high then w i else modinfo_scalar_limb i))<=2^62.
Proof.
 intros Normal high i I;destruct high.
 - rewrite inv_seed_input_signed by assumption;rewrite Z.abs_eq by apply Int64.unsigned_range.
   pose proof(Normal i I);destruct(Nat.eqb i 4);lia.
 - pose proof(scalar_norm62_modulus_bound i I);apply Z.abs_le;lia.
Qed.

Lemma scalar_inv_ready_loads w beta m : rep w beta (inv_mod_fg_regs modinfo_scalar_limb) m ->
 (forall (high : bool) i,(i<5)%nat ->
  Mem.load Mint64 m (blk beta (if high then 3 else 2)) (bas beta (if high then 3 else 2)+8*Z.of_nat i)=
   Some(Vlong(inv_init_word high i))) /\
 (forall (high : bool) i,(i<5)%nat ->
  Mem.load Mint64 m (blk beta (if high then 5 else 4)) (bas beta (if high then 5 else 4)+8*Z.of_nat i)=
   Some(Vlong(if high then w i else modinfo_scalar_limb i))).
Proof.
 intro Rep;split;intros high i I.
 - assert(Load:xload (inv_mod_fg_regs modinfo_scalar_limb) (if high then 3 else 2)
    (8*Z.of_nat i) tulong=Some(inv_init_sx high i)).
   { destruct high;destruct i as [|[|[|[|[|i]]]]];try lia;reflexivity. }
   pose proof(xload_u64_defined_sound w beta _ m _ _ _ Rep Load) as L;rewrite inv_init_den in L;exact L.
 - assert(Load:xload (inv_mod_fg_regs modinfo_scalar_limb) (if high then 5 else 4)
    (8*Z.of_nat i) tulong=Some(if high then XLv i else XLc(modinfo_scalar_limb i))).
   { destruct high;destruct i as [|[|[|[|[|i]]]]];try lia;reflexivity. }
   pose proof(xload_u64_defined_sound w beta _ m _ _ _ Rep Load) as L;destruct high;exact L.
Qed.

Lemma scalar_inv_represented_seed_bounds w : signed62_normalized w ->
 scalar_de62_state_bounds(inv_de_rho(inv_mod_seed_rho modinfo_scalar_limb w)) /\
 scalar_de62_coefficient_link (signed62_unsigned_value w) (inv_de_rho(inv_mod_seed_rho modinfo_scalar_limb w)) (scalar_inv_seed_state w) /\
 inv_state_matches 5 (inv_mod_seed_rho modinfo_scalar_limb w) (scalar_inv_seed_state w) /\
 inv_fg_limb_bounds(inv_mod_seed_rho modinfo_scalar_limb w) /\
 inv_fg_value_capacity 5 (inv_mod_seed_rho modinfo_scalar_limb w) /\
 de62_input_value(inv_de_rho(inv_mod_seed_rho modinfo_scalar_limb w)) false mod canonical_group_order=0.
Proof.
 intro Normal.
 assert(DE:scalar_de62_state_bounds(inv_de_rho(inv_mod_seed_rho modinfo_scalar_limb w))).
 { destruct(scalar_inv_seed_de_bounds (inv_de_rho(inv_mod_seed_rho modinfo_scalar_limb w))) as(Limbs & Values);split.
   - intros high i I;rewrite inv_mod_seed_de_word by exact I.
     rewrite <-(inv_initial_de_word (inv_de_rho(inv_mod_seed_rho modinfo_scalar_limb w)) high i I);apply Limbs;exact I.
   - intro high;rewrite inv_mod_seed_de_value;specialize(Values high);rewrite inv_initial_de_value in Values;exact Values. }
 assert(Link:scalar_de62_coefficient_link (signed62_unsigned_value w) (inv_de_rho(inv_mod_seed_rho modinfo_scalar_limb w)) (scalar_inv_seed_state w)).
 { intro high;pose proof(scalar_inv_seed_link w (inv_de_rho(inv_mod_seed_rho modinfo_scalar_limb w)) high) as L.
   rewrite inv_initial_de_value in L;rewrite inv_mod_seed_de_value;exact L. }
 assert(State:inv_state_matches 5 (inv_mod_seed_rho modinfo_scalar_limb w) (scalar_inv_seed_state w)).
 { split;rewrite inv_mod_seed_fg_value.
   - symmetry;exact scalar_norm62_modulus_value.
   - symmetry;apply inv_seed_input_value;exact Normal. }
 assert(Limbs:inv_fg_limb_bounds(inv_mod_seed_rho modinfo_scalar_limb w)).
 { intros high i I;rewrite inv_mod_seed_fg_word by exact I;exact(scalar_inv_seed_fg_bounds w Normal high i I). }
 assert(Capacity:inv_fg_value_capacity 5 (inv_mod_seed_rho modinfo_scalar_limb w)).
 { destruct(scalar_inv_seed_values w Normal) as(_ & _ & _ & _ & FBound & GBound).
   intro high;destruct high;[rewrite <-(proj2 State)|rewrite <-(proj1 State)];
   change(2^(62*Z.of_nat 5)) with(2^310);lia. }
 split;[exact DE|];split;[exact Link|];split;[exact State|];split;[exact Limbs|];split;[exact Capacity|].
 rewrite inv_mod_seed_de_value,Zmod_0_l;reflexivity.
Qed.

(** The prefix is derived from the original scalar caller's actual output
    buffer and metadata, not an assumed fresh-frame or initialized-loop rep. *)
Theorem scalar_inv_entry_establishes_seed w m bd bx : modinfo_scalar_state m ->
 scalar_at m bx 0 (scalar_add_values w 0) ->
 Mem.range_perm m bx 0 32 Cur Freeable -> Mem.range_perm m bd 0 32 Cur Freeable ->
 exists bs mi mp betaN e le mc lef mf,
 function_entry2 secp_ge f_secp256k1_scalar_inverse_var [Vptr bd Ptrofs.zero;Vptr bx Ptrofs.zero]
  m (scalar_inv_env bs) (scalar_inv_temps bd bx) mi /\
 Clight2.exec_stmt secp_ge (scalar_inv_env bs) (scalar_inv_temps bd bx) mi scalar_inv_pack
  E0 (scalar_inv_temps bd bx) mp Out_normal /\
 function_entry2 secp_ge f_secp256k1_modinv64_var [Vptr bs Ptrofs.zero;Vptr scalar_inv_modinfo_block Ptrofs.zero]
  mp e le mc /\ Clight2.exec_stmt secp_ge e le mc inv_ready_prefix E0 lef mf Out_normal /\
 rep (scalar62_words true w) ([(bs,0);(scalar_inv_modinfo_block,0)]++betaN)
  (inv_mod_fg_regs modinfo_scalar_limb) mf /\
 rep (inv_mod_seed_rho modinfo_scalar_limb (scalar62_words true w)) ([(bs,0);(scalar_inv_modinfo_block,0)]++betaN)
  (inv_mod_seed_regs modinfo_scalar_limb) mf /\
 scalar_de62_state_bounds(inv_de_rho(inv_mod_seed_rho modinfo_scalar_limb (scalar62_words true w))) /\
 scalar_de62_coefficient_link (scalar_limb_value w) (inv_de_rho(inv_mod_seed_rho modinfo_scalar_limb (scalar62_words true w)))
  (scalar_inv_seed_state(scalar62_words true w)) /\
 inv_state_matches 5 (inv_mod_seed_rho modinfo_scalar_limb (scalar62_words true w)) (scalar_inv_seed_state(scalar62_words true w)) /\
 inv_fg_limb_bounds(inv_mod_seed_rho modinfo_scalar_limb (scalar62_words true w)) /\
 inv_fg_value_capacity 5 (inv_mod_seed_rho modinfo_scalar_limb (scalar62_words true w)) /\
 de62_input_value(inv_de_rho(inv_mod_seed_rho modinfo_scalar_limb (scalar62_words true w))) false mod canonical_group_order=0 /\
 ematch ([(bs,0);(scalar_inv_modinfo_block,0)]++betaN) (snd inv_start_alloc) e /\
 tmatch (scalar62_words true w) ([(bs,0);(scalar_inv_modinfo_block,0)]++betaN) inv_loop_start_temps lef /\
 lef!_len=Some(Vint(Int.repr 5)) /\ lef!_eta=Some(Vlong(Int64.repr(-1))) /\
 signed62_normalized(scalar62_words true w) /\ signed62_unsigned_value(scalar62_words true w)=scalar_limb_value w /\
 (forall later,scalar_de62_state_bounds(inv_initial_de_rho later) /\
  scalar_de62_coefficient_link (scalar_limb_value w) (inv_initial_de_rho later) (scalar_inv_seed_state(scalar62_words true w)) /\
  de62_input_value(inv_initial_de_rho later) false mod canonical_group_order=0) /\
 (forall (high : bool) i,(i<5)%nat ->
  Mem.load Mint64 mf (blk ([(bs,0);(scalar_inv_modinfo_block,0)]++betaN) (if high then 3 else 2))
   (bas ([(bs,0);(scalar_inv_modinfo_block,0)]++betaN) (if high then 3 else 2)+8*Z.of_nat i)=
   Some(Vlong(inv_init_word high i))) /\
 (forall (high : bool) i,(i<5)%nat ->
  Mem.load Mint64 mf (blk ([(bs,0);(scalar_inv_modinfo_block,0)]++betaN) (if high then 5 else 4))
   (bas ([(bs,0);(scalar_inv_modinfo_block,0)]++betaN) (if high then 5 else 4)+8*Z.of_nat i)=
   Some(Vlong(if high then scalar62_words true w i else modinfo_scalar_limb i))) /\
 norm62_value_z 4 (fun i=>Int64.signed(modinfo_scalar_limb i))=f(scalar_inv_seed_state(scalar62_words true w)) /\
 norm62_value_z 4 (fun i=>Int64.signed(scalar62_words true w i))=g(scalar_inv_seed_state(scalar62_words true w)) /\
 delta(scalar_inv_seed_state(scalar62_words true w))=1 /\ eta(scalar_inv_seed_state(scalar62_words true w))= -1 /\
 Z.abs(f(scalar_inv_seed_state(scalar62_words true w)))<=2^256 /\
 Z.abs(g(scalar_inv_seed_state(scalar62_words true w)))<=2^256 /\
 (forall (high : bool) i,(i<5)%nat ->
  Z.abs(Int64.signed(if high then scalar62_words true w i else modinfo_scalar_limb i))<=2^62) /\
 Forall(fun p=>~Mem.valid_block mp (fst p)) betaN /\
 lframe(fun b ofs=>~foot ([(bs,0);(scalar_inv_modinfo_block,0)]++betaN)
   (map rshape(sregs(inv_mod_start_state modinfo_scalar_limb))) b ofs) mp mf.
Proof.
 intros Global Input FX FD.
 destruct(scalar_inv_entry_with_modinfo w m bd bx Global Input FX FD)
  as(bs & mi & mp & Outer & Pack & Args & Metadata & Packed & Normal & Value & Source & FS & FXP & FDP & SX & DS & Fresh & Frame).
 assert(Sep:bs<>scalar_inv_modinfo_block).
 { intro Same;apply Fresh;rewrite Same;exact(proj1(proj1 Global)). }
 pose proof(scalar_inv_start_rep (scalar62_words true w) mp bs Sep Packed FS Metadata) as Start.
 destruct(inv_mod_entry_to_loop modinfo_scalar_limb (scalar62_words true w) [(bs,0);(scalar_inv_modinfo_block,0)] mp Start eq_refl)
  as(betaN & e & le & mc & lef & mf & Entry & Run & Objects & Temps & Env & Len & Eta & FreshN & FrameN).
 change(function_entry2 secp_ge f_secp256k1_modinv64_var
   [Vptr bs Ptrofs.zero;Vptr scalar_inv_modinfo_block Ptrofs.zero] mp e le mc) in Entry.
 destruct(scalar_inv_ready_loads (scalar62_words true w) _ mf Objects) as(DE & FG).
 destruct(scalar_inv_seed_values (scalar62_words true w) Normal) as(FValue & GValue & Delta & MathEta & FBound & GBound).
 pose proof(scalar_inv_seed_fg_bounds (scalar62_words true w) Normal) as StoredBounds.
 pose proof(inv_mod_seed_rep modinfo_scalar_limb (scalar62_words true w) _ mf Objects) as SeedRep.
 destruct(scalar_inv_represented_seed_bounds (scalar62_words true w) Normal) as(SeedDE & SeedLink & SeedState & SeedLimbs & SeedCapacity & SeedZero).
 rewrite Value in SeedLink.
 assert(Invariant:forall later,scalar_de62_state_bounds(inv_initial_de_rho later) /\
   scalar_de62_coefficient_link (scalar_limb_value w) (inv_initial_de_rho later) (scalar_inv_seed_state(scalar62_words true w)) /\
   de62_input_value(inv_initial_de_rho later) false mod canonical_group_order=0).
 { intro later;split;[apply scalar_inv_seed_de_bounds|];split;[rewrite <-Value;apply scalar_inv_seed_link|apply scalar_inv_seed_zero]. }
 exists bs,mi,mp,betaN,e,le,mc,lef,mf;repeat first[assumption|split].
Qed.
