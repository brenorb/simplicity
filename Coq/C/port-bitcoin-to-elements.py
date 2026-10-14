import re,sys
def port(text):
    t=text
    t=t.replace("Simplicity.Primitive.Bitcoin","C.jet_elements_prim")
    t=t.replace("jets_bitcoin","jets_elements").replace("jet_bitcoin_","jet_elements_")
    t=t.replace("f_simplicity_bitcoin_","f_simplicity_")
    t=t.replace("_bitcoinTransaction","_elementsTransaction").replace("_bitcoinTapEnv","_elementsTapEnv")
    t=t.replace("Bitcoin.envScriptCMR environment","tapScriptCMR (Elements.envTap environment)")
    t=t.replace("ebase + 56","ebase + 88").replace("pdelta + 8 <= 56","pdelta + 8 <= 88")
    t=t.replace("_txEnv _ix 48","_txEnv _ix 80")
    t=t.replace("bitcoin_","elements_")
    t=t.replace("Bitcoin.","Elements.")
    t=re.sub(r"\b488\b","760",t)
    t=re.sub(r"\b464\b","720",t)
    t=re.sub(r"\b472\b","728",t)
    t=t.replace("Bitcoin Clight jet","Elements Clight jet").replace("Bitcoin translation unit","Elements translation unit").replace("Bitcoin","Elements")
    return t
for name in sys.argv[1:]:
    src=open('C/jet_bitcoin_%s.v'%name).read()
    open('C/jet_elements_%s.v'%name,'w').write(port(src))
