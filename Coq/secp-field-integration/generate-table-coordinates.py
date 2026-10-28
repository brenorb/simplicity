#!/usr/bin/env python3
"""Regenerate untrusted odd-table coordinate witnesses and checked equations.

The arithmetic here chooses coefficient data only. Coq checks the coefficient
identities and proves their evaluation bridge; this script is not trusted.
"""

from functools import lru_cache
P=2**256-2**32-977

def trim(a):
 while a and a[-1]==0: a.pop()
 return a

def add(a,b):
 c=[0]*max(len(a),len(b))
 for i in range(len(c)): c[i]=((a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0))%P
 return trim(c)

def neg(a): return [(-x)%P for x in a]
def sub(a,b): return add(a,neg(b))
def scale(a,k): return trim([(k*x)%P for x in a])
def mul(a,b):
 if not a or not b:return []
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  if x:
   for j,y in enumerate(b):
    if y:c[i+j]+=x*y
 return trim([x%P for x in c])

F=[7,0,0,1];F16=scale(mul(F,F),16)
@lru_cache(None)
def witness_d(n):
 if n==0:return []
 if n in (1,2):return [1]
 if n==3:return [0,84,0,0,3]
 if n==4:return [(-784)%P,0,0,280,0,0,2]
 m=n//2
 if n%2:
  a=mul(witness_d(m+2),mul(mul(witness_d(m),witness_d(m)),witness_d(m)))
  b=mul(witness_d(m-1),mul(mul(witness_d(m+1),witness_d(m+1)),witness_d(m+1)))
  return sub(mul(F16,a),b) if m%2==0 else sub(a,mul(F16,b))
 return mul(witness_d(m),sub(mul(witness_d(m+2),mul(witness_d(m-1),witness_d(m-1))),mul(witness_d(m-2),mul(witness_d(m+1),witness_d(m+1)))))


from pathlib import Path
lines=['''(** Untrusted coordinate witnesses. Closed coefficient equations below
are kernel-checked; their evaluation bridge to the literal table is separate. *)
From Coq Require Import ZArith List Lia.
Require Import C.jet_secp_fe_math C.jet_secp_polynomial C.jet_secp_fast_polynomial
 C.jet_secp_table_denominators C.jet_secp_table_denominator9
 C.jet_secp_table_denominator11 C.jet_secp_table_denominator13 C.jet_secp_table_denominator15
 C.jet_secp_table_witnesses C.jet_secp_curve_polynomial.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.
Definition table_witness_d (n:nat) : list Z :=
 match n with
''']
for n in range(18):
 if n in [3,5,7,9,11,13,15]:
  rhs=f'table_odd_witness {n} {str(n%3==0).lower()} table_q{n}'
 else:rhs='['+';'.join(map(str,witness_d(n)))+']'
 lines.append(f' | {n}%nat=>{rhs}\n')
lines+=[''' | _=>[] end.
Definition table_witness_s : list Z := [7;0;0;1].
Definition table_witness_sq p := fast_polynomial_mul p p.
Definition table_witness_cube p := fast_polynomial_mul (table_witness_sq p) p.
Definition table_witness_phi n :=
 if Nat.eqb n 1 then [0;1] else
 fast_polynomial_sub (fast_polynomial_mul [0;1] (table_witness_sq (table_witness_d n)))
  (fast_polynomial_scale 4 (fast_polynomial_mul table_witness_s
   (fast_polynomial_mul (table_witness_d (n-1)%nat) (table_witness_d (n+1)%nat)))).
Definition table_witness_omega n :=
 if Nat.eqb n 1 then [1] else
 fast_polynomial_sub
  (fast_polynomial_mul (table_witness_d (n+2)%nat) (table_witness_sq (table_witness_d (n-1)%nat)))
  (fast_polynomial_mul (table_witness_d (n-2)%nat) (table_witness_sq (table_witness_d (n+1)%nat))).
Definition table_witness_x n := fast_polynomial_mul table_witness_s (table_witness_phi n).
Definition table_witness_y n := fast_polynomial_mul (table_witness_sq table_witness_s) (table_witness_omega n).
Definition table_witness_slope := fast_polynomial_scale ((3*((feP+1)/2)) mod feP) [0;0;1].
Definition table_witness_bx := fast_polynomial_sub (table_witness_sq table_witness_slope)
 (fast_polynomial_scale 2 (fast_polynomial_mul [0;1] table_witness_s)).
Definition table_witness_by := fast_polynomial_sub
 (fast_polynomial_mul table_witness_slope
  (fast_polynomial_sub (fast_polynomial_scale 3 (fast_polynomial_mul [0;1] table_witness_s))
   (table_witness_sq table_witness_slope))) (table_witness_sq table_witness_s).
Definition table_witness_h n := fast_polynomial_sub
 (fast_polynomial_mul table_witness_bx (table_witness_sq (table_witness_d n))) (table_witness_x n).
Definition table_witness_i n := fast_polynomial_sub
 (fast_polynomial_mul table_witness_by (table_witness_cube (table_witness_d n))) (table_witness_y n).
Definition table_witness_f n := fast_polynomial_scale ((((feP+1)/2)*((feP+1)/2)) mod feP)
 (fast_polynomial_mul (table_witness_d n)
  (if Nat.eqb n 1 then [feP-1] else table_witness_d (n-2)%nat)).
Definition table_witness_next_x n := fast_polynomial_sub
 (fast_polynomial_sub (table_witness_sq (table_witness_i n)) (table_witness_cube (table_witness_h n)))
 (fast_polynomial_scale 2 (fast_polynomial_mul (table_witness_x n) (table_witness_sq (table_witness_h n)))).
Definition table_witness_next_y n := fast_polynomial_sub
 (fast_polynomial_mul (table_witness_i n)
  (fast_polynomial_sub (fast_polynomial_mul (table_witness_x n) (table_witness_sq (table_witness_h n)))
   (table_witness_next_x n)))
 (fast_polynomial_mul (table_witness_y n) (table_witness_cube (table_witness_h n))).
Definition table_witness_step n :=
 (table_witness_h n,table_witness_next_x n,table_witness_next_y n,
  fast_polynomial_mul (table_witness_d n) (table_witness_h n)).
Definition table_witness_scaled_next n :=
 (fast_polynomial_scale ((((feP+1)/2)*((feP+1)/2)) mod feP)
   (fast_polynomial_mul (table_witness_d (n+2)%nat)
    (if Nat.eqb n 1 then [feP-1] else table_witness_d (n-2)%nat)),
  fast_polynomial_mul (table_witness_sq (table_witness_f n)) (table_witness_x (n+2)%nat),
  fast_polynomial_mul (table_witness_cube (table_witness_f n)) (table_witness_y (n+2)%nat),
  fast_polynomial_mul (table_witness_f n) (table_witness_d (n+2)%nat)).
''']
lines.append("""Lemma table_witness_d_nonzero n x y :
 In n [1%nat;3%nat;5%nat;7%nat;9%nat;11%nat;13%nat;15%nat] ->
 (x*x*x+7) mod feP=(y*y) mod feP ->
 polynomial_value (table_witness_d n) x mod feP<>0.
Proof.
 intros Member Curve.
""")
for n in [1,3,5,7,9,11,13,15]:
 lines.append(' destruct Member as [Equal|Member].\n { subst n.\n')
 if n==1:
  lines.append('   cbn [table_witness_d polynomial_value];rewrite Z.mul_0_r,Z.add_0_r;vm_compute;discriminate. }\n')
 else:
  lines.append(f'   change (polynomial_value (table_odd_witness {n} {str(n%3==0).lower()} table_q{n}) x mod feP<>0).\n')
  lines.append(f'   apply table_odd_witness_nonzero.\n   - vm_compute;discriminate.\n   - exact (secp_curve_x_nonzero x y Curve).\n   - exact (table_denominator{n}_nonzero x y Curve). }}\n')
lines.append(' contradiction.\nQed.\n')
out=Path(__file__).resolve().parents[1]/'C'
def write_changed(path, source):
 if not path.exists() or path.read_text()!=source:
  path.write_text(source)
write_changed(out/'jet_secp_table_coordinates.v', ''.join(lines))
for n in [1,3,5,7,9,11,13]:
 timeout=60 if n<=9 else (240 if n==11 else 360)
 source=f"""(** Checked coefficient identity for the original odd-table step {n} to {n+2}.
    Its use for literal word operations requires the separate residue bridge. *)
Require Import C.jet_secp_table_coordinates.
Set Default Timeout {timeout}.
Lemma table_step{n}_coefficients :
 table_witness_step {n}%nat=table_witness_scaled_next {n}%nat.
Proof. Time vm_compute;reflexivity. Qed.
"""
 write_changed(out/f'jet_secp_table_step{n}.v', source)
