(** Derive a readonly int64 scalar from an actual CompCert initializer.
    Kept independent of the large generated program for cheap specialization. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Memory Globalenvs.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma readonly_int64_global_initialized {F V} (p : AST.program F V) b info x m :
  Genv.find_var_info (Genv.globalenv p) b = Some
    {| gvar_info := info; gvar_init := [Init_int64 x]; gvar_readonly := true; gvar_volatile := false |} ->
  Genv.init_mem p = Some m ->
  Mem.load Mint64 m b 0 = Some (Vlong x) /\ (forall ofs, ~ Mem.perm m b ofs Cur Writable).
Proof.
  intros HInfo HInit.
  destruct (Genv.init_mem_characterization p b HInfo HInit) as [HRange [HOnly [HLoad HBytes]]].
  split.
  - specialize (HLoad eq_refl); exact (proj1 HLoad).
  - intros ofs HW. destruct (HOnly ofs Cur Writable HW) as [_ HOrder].
    change (perm_order Readable Writable) in HOrder; inversion HOrder.
Qed.
