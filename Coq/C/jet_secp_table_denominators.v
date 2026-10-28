(** Concrete, untrusted certificates for the odd table, in t=x^3.
    Closed equalities are checked with ordinary VM conversion. The theorem
    discharges the cube and curve conditions from the original input point.
    No C execution or jet coverage is asserted by this module. *)
From Coq Require Import ZArith List Lia.
Require Import C.jet_secp_fe_math C.jet_secp_polynomial C.jet_secp_curve_polynomial C.jet_secp_fast_polynomial.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.

Definition table_q3 : list Z := [28;1].
Definition table_power3 : list Z := [1].
Definition table_factor3 : list Z := [28;1].
Definition table_bezout_left3 : list Z := [1].
Definition table_bezout_right3 : list Z := [].
Lemma table_power3_checked :
 polynomial_power feP [0;1] secp_cubic_exponent table_q3=table_power3.
Proof. rewrite <-fast_polynomial_power_correct. Time vm_compute;reflexivity. Qed.
Lemma table_bezout3_checked :
 polynomial_add feP (polynomial_mul feP table_bezout_left3 table_q3)
  (polynomial_mul feP table_bezout_right3 (polynomial_sub feP table_power3 [1]))=table_factor3.
Proof.
 rewrite <-fast_polynomial_add_correct.
 repeat rewrite <-fast_polynomial_mul_correct.
 rewrite <-fast_polynomial_sub_correct;vm_compute;reflexivity.
Qed.
Lemma table_euler3_checked :
 polynomial_power feP secp_cubic_curve_polynomial secp_euler_exponent table_factor3=[feP-1].
Proof. rewrite <-fast_polynomial_power_correct. Time vm_compute;reflexivity. Qed.
Theorem table_denominator3_nonzero x y :
 (x*x*x+7) mod feP=(y*y) mod feP ->
 polynomial_value table_q3 (x*x*x) mod feP<>0.
Proof.
 intro Curve;apply (secp_cubic_polynomial_excludes_root table_q3 table_power3 table_factor3
  table_bezout_left3 table_bezout_right3 x y).
 - exact table_power3_checked.
 - exact table_bezout3_checked.
 - right;exact table_euler3_checked.
 - exact Curve.
Qed.

Definition table_q5 : list Z := [46316835694926478169428394003475163141307993866256225615783033603163533745734;115792089237316195423570985008687907853269984665640564039457584007908834561903;115792089237316195423570985008687907853269984665640564039457584007908834669311;532;1].
Definition table_power5 : list Z := [97380337474690556681970268844358938395277663720584101655855343830214348643043;100907101480807348702285310182505290589066765132769054642034264574382406988852;103995681924973218495537020563472464301292500615670474445612460735885084011962;16301899032869119698946973517305221138051261965926827468732093378423193326532].
Definition table_factor5 : list Z := [1].
Definition table_bezout_left5 : list Z := [43278572329917339109014191580634909206163775526875483735724267884479780462897;54982776636358415789812069475063360618958946847822110292787590591916027193274;94102466585509862853205485201694505407623375408048662631821704430713147362378].
Definition table_bezout_right5 : list Z := [109291419246137104687927395795717164936951889755382988499583916782761052400721;46787046032729281751067970492209969010018484441625870001933879945980319827293;15748578231672678756928063280076856951155431051818084324720947345712132175188;101348472174614064517258432973579664173987909307573628370626878506118395422506].
Lemma table_power5_checked :
 polynomial_power feP [0;1] secp_cubic_exponent table_q5=table_power5.
Proof. rewrite <-fast_polynomial_power_correct. Time vm_compute;reflexivity. Qed.
Lemma table_bezout5_checked :
 polynomial_add feP (polynomial_mul feP table_bezout_left5 table_q5)
  (polynomial_mul feP table_bezout_right5 (polynomial_sub feP table_power5 [1]))=table_factor5.
Proof.
 rewrite <-fast_polynomial_add_correct.
 repeat rewrite <-fast_polynomial_mul_correct.
 rewrite <-fast_polynomial_sub_correct;vm_compute;reflexivity.
Qed.
Theorem table_denominator5_nonzero x y :
 (x*x*x+7) mod feP=(y*y) mod feP ->
 polynomial_value table_q5 (x*x*x) mod feP<>0.
Proof.
 intro Curve;apply (secp_cubic_polynomial_excludes_root table_q5 table_power5 table_factor5
  table_bezout_left5 table_bezout_right5 x y).
 - exact table_power5_checked.
 - exact table_bezout5_checked.
 - left;reflexivity.
 - exact Curve.
Qed.

Definition table_q7 : list Z := [53971714048;115792089237316195423570985008687907853269984665640564039457584007814384172079;115792089237316195423570985008687907853269984665640564039457584007861609421871;115792089237316195423570985008687907853269984665640564039457584007905100021807;115792089237316195423570985008687907853269984665640564039457584007908516279855;115792089237316195423570985008687907853269984665640564039457584007908794016559;115792089237316195423570985008687907853269984665640564039457584007908834371391;3944;1].
Definition table_power7 : list Z := [55594575648329892869085402983802832744385952214688224221778511981742606582254].
Definition table_factor7 : list Z := [1].
Definition table_bezout_left7 : list Z := [].
Definition table_bezout_right7 : list Z := [20065837862995434184828527341628358369628010816984113272559690675388742696469].
Lemma table_power7_checked :
 polynomial_power feP [0;1] secp_cubic_exponent table_q7=table_power7.
Proof.
 rewrite <-fast_polynomial_power_correct.
 Set Default Timeout 240.
 Time vm_compute;reflexivity.
Qed.
Set Default Timeout 60.
Lemma table_bezout7_checked :
 polynomial_add feP (polynomial_mul feP table_bezout_left7 table_q7)
  (polynomial_mul feP table_bezout_right7 (polynomial_sub feP table_power7 [1]))=table_factor7.
Proof.
 rewrite <-fast_polynomial_add_correct.
 repeat rewrite <-fast_polynomial_mul_correct.
 rewrite <-fast_polynomial_sub_correct;vm_compute;reflexivity.
Qed.
Theorem table_denominator7_nonzero x y :
 (x*x*x+7) mod feP=(y*y) mod feP ->
 polynomial_value table_q7 (x*x*x) mod feP<>0.
Proof.
 intro Curve;apply (secp_cubic_polynomial_excludes_root table_q7 table_power7 table_factor7
  table_bezout_left7 table_bezout_right7 x y).
 - exact table_power7_checked.
 - exact table_bezout7_checked.
 - left;reflexivity.
 - exact Curve.
Qed.

