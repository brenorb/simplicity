#!/usr/bin/env python3
"""Extract the matching RFC8554 appendix-F H10/W4 subkey certificate KAT.
Only parses the vendored specification as data; never executes source in it.
"""
import re,hashlib
from pathlib import Path
root=Path(__file__).resolve().parents[1]
source=root/'vendor-specs/eprint/rfc8554.txt'
s=source.read_text()
pub=s.split('   Test Case 2 Public Key',1)[1].split('   Test Case 2 Message',1)[0]
sig=s.split('   Test Case 2 Signature',1)[1].split('   final_signature:',1)[0]
child=sig.split('   LMS public key',1)[1]
sig=sig.split('   LMS public key',1)[0]
# Lines labeled C,K,y,path wrap 32-byte values over two 16-byte halves.
def value(text,label,nbytes):
 m=re.search(r'^   '+re.escape(label)+r' +([0-9a-f]+)(?:[^\n]*)\n(?: {15}([0-9a-f]{32})\n)?',text,re.M)
 if not m: raise ValueError(label)
 v=m[1]+(m[2] or '')
 if len(v)!=2*nbytes: raise ValueError((label,len(v),nbytes))
 return v
lines=['# RFC8554 appendix F test case2 first LMS signature (H10/W4), signs child LMS public key',
       '# source_sha256='+hashlib.sha256(source.read_bytes()).hexdigest(),
       'parent_I='+value(pub,'I',16),'parent_K='+value(pub,'K',32),
       'q='+value(sig,'q',4),'C='+value(sig,'C',32),
       'child_I='+value(child,'I',16),'child_K='+value(child,'K',32)]
lines += [f'y{i}='+value(sig,f'y[{i}]',32) for i in range(67)]
lines += [f'path{i}='+value(sig,f'path[{i}]',32) for i in range(10)]
(root/'vendor-specs/eprint/rfc8554-testcase2-lms.txt').write_text('\n'.join(lines)+'\n')
print('extracted67chainvalues+10authenticationnodes; parentH10/W4; childH5/W8')
