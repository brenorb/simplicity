#!/usr/bin/env python3
"""Generate the event log and integer model of the original secp256k1_fe_mul
symbolic run (Coq/C/jet_parallel_fe_mul_model.v).  The event list below is the
one printed by the executor; the generated module re-checks it against the
actual run (fe_mul_log_eq), so a transcription error cannot go unnoticed."""
import sys
R = "68719492368"; M = "4503599627370495"
# (tag, base, args); args: ('v', j) | ('R',) | ('R12',) | ('R4',) | ('and', j) | ('u0', j48, j36)
EV = [
 (1,10,[('v',0),('v',8)]), (2,12,[('v',10),('v',11),('v',1),('v',7)]),
 (2,14,[('v',12),('v',13),('v',2),('v',6)]), (2,16,[('v',14),('v',15),('v',3),('v',5)]),
 (1,18,[('v',4),('v',9)]), (2,20,[('v',16),('v',17),('R',),('v',18)]),
 (5,22,[('v',18),('v',19)]), (4,24,[('v',20),('v',21)]),
 (2,26,[('v',24),('v',25),('v',0),('v',9)]), (2,28,[('v',26),('v',27),('v',1),('v',8)]),
 (2,30,[('v',28),('v',29),('v',2),('v',7)]), (2,32,[('v',30),('v',31),('v',3),('v',6)]),
 (2,34,[('v',32),('v',33),('v',4),('v',5)]), (2,36,[('v',34),('v',35),('R12',),('v',22)]),
 (4,38,[('v',36),('v',37)]), (1,40,[('v',0),('v',5)]),
 (2,42,[('v',38),('v',39),('v',1),('v',9)]), (2,44,[('v',42),('v',43),('v',2),('v',8)]),
 (2,46,[('v',44),('v',45),('v',3),('v',7)]), (2,48,[('v',46),('v',47),('v',4),('v',6)]),
 (4,50,[('v',48),('v',49)]), (2,52,[('v',40),('v',41),('u0',48,36),('R4',)]),
 (4,54,[('v',52),('v',53)]), (2,56,[('v',54),('v',55),('v',0),('v',6)]),
 (2,58,[('v',56),('v',57),('v',1),('v',5)]), (2,60,[('v',50),('v',51),('v',2),('v',9)]),
 (2,62,[('v',60),('v',61),('v',3),('v',8)]), (2,64,[('v',62),('v',63),('v',4),('v',7)]),
 (2,66,[('v',58),('v',59),('and',64),('R',)]), (4,68,[('v',64),('v',65)]),
 (4,70,[('v',66),('v',67)]), (2,72,[('v',70),('v',71),('v',0),('v',7)]),
 (2,74,[('v',72),('v',73),('v',1),('v',6)]), (2,76,[('v',74),('v',75),('v',2),('v',5)]),
 (2,78,[('v',68),('v',69),('v',3),('v',9)]), (2,80,[('v',78),('v',79),('v',4),('v',8)]),
 (2,82,[('v',76),('v',77),('R',),('v',80)]), (5,84,[('v',80),('v',81)]),
 (4,86,[('v',82),('v',83)]), (2,88,[('v',86),('v',87),('R12',),('v',84)]),
 (3,90,[('v',88),('v',89),('and',20)]), (4,92,[('v',90),('v',91)]),
]
INPUTS = ['a0','a1','a2','a3','a4','b0','b1','b2','b3','b4']
TAG = {1:'tMUL',2:'tACC',3:'tADD',4:'tSHR52',5:'tSHR64'}

def sx(a):
    k = a[0]
    if k == 'v': return f"XLv {a[1]}"
    if k == 'R': return f"XLc (Int64.repr {R})"
    if k == 'R12': return f"XLsh Hshl (XLc (Int64.repr {R})) 12"
    if k == 'R4': return f"XLsh Hshru (XLc (Int64.repr {R})) 4"
    if k == 'and': return f"XLb Band (XLv {a[1]}) (XLc (Int64.repr {M}))"
    if k == 'u0':
        return (f"XLb Bor (XLsh Hshl (XLb Band (XLv {a[1]}) (XLc (Int64.repr {M}))) 4) "
                f"(XLsh Hshru (XLb Band (XLv {a[2]}) (XLc (Int64.repr {M}))) 48)")
def word(j):
    if j < 10: return INPUTS[j]
    return f"(fm_lo W{j})" if j % 2 == 0 else f"(fm_hi W{j-1})"
def mz(a):
    k = a[0]
    if k == 'v': return f"Int64.unsigned {word(a[1])}"
    if k == 'R': return f"Int64.unsigned (Int64.repr {R})"
    if k == 'R12': return f"Int64.unsigned (Int64.shl (Int64.repr {R}) (Int64.repr 12))"
    if k == 'R4': return f"Int64.unsigned (Int64.shru (Int64.repr {R}) (Int64.repr 4))"
    if k == 'and': return f"Int64.unsigned (Int64.and {word(a[1])} (Int64.repr {M}))"
    if k == 'u0':
        return (f"Int64.unsigned (Int64.or (Int64.shl (Int64.and {word(a[1])} (Int64.repr {M})) (Int64.repr 4)) "
                f"(Int64.shru (Int64.and {word(a[2])} (Int64.repr {M})) (Int64.repr 48)))")
def wdef(t, args):
    z = [mz(a) for a in args]
    if t == 1: return f"{z[0]} * {z[1]}"
    if t == 2: return f"({z[1]} * 2 ^ 64 + {z[0]} + {z[2]} * {z[3]}) mod 2 ^ 128"
    if t == 3: return f"({z[1]} * 2 ^ 64 + {z[0]} + {z[2]}) mod 2 ^ 128"
    if t == 4: return f"({z[1]} * 2 ^ 64 + {z[0]}) / 2 ^ 52"
    if t == 5: return f"({z[1]} * 2 ^ 64 + {z[0]}) / 2 ^ 64"

out = []
out.append("Definition fe_mul_log : list event := [")
out.append(";\n".join(f"  mkev {TAG[t]} {b} 2 [{'; '.join(sx(a) for a in args)}]" for t,b,args in EV))
out.append("].\n")
out.append("Section MODEL.\nVariables a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : int64.")
for t,b,args in EV:
    out.append(f"Definition W{b} : Z := {wdef(t,args)}.")
out.append("Definition fm_rho (n : nat) : int64 :=\n  match n with")
for j in range(10): out.append(f"  | {j} => {INPUTS[j]}")
for t,b,args in EV:
    out.append(f"  | {b} => fm_lo W{b} | {b+1} => fm_hi W{b}")
out.append("  | _ => Int64.zero end%nat.")
out.append("Definition fm_ws : list Z := [" + "; ".join(f"W{b}" for _,b,_ in EV) + "].")
out.append("End MODEL.")
sys.stdout.write("\n".join(out) + "\n")
