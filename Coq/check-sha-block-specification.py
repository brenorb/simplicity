"""Source correspondence for SHA block, supplementing the formal C proof.

Compare Core expression trees (application, pairing, composition and
projections), not only selected names. Constant wiring has separate closed
Coq program equalities; this check never certifies execution or startup.
"""
import importlib.util
import os
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
COQ = Path(__file__).resolve().parent
REPO = Path(os.environ.get("JET_C_REPO", COQ.parent))
sp = importlib.util.spec_from_file_location("sha_source", COQ / "check-secp-predicates-specification.py")
p = importlib.util.module_from_spec(sp)
sp.loader.exec_module(p)


def expression(text, rename=None):
    """The reviewed Core fragment; reject every unparsed token."""
    rename = {"a32": "add32", "x32": "xor_xorWord32", "xor3": "xor_xor",
              "bitwise_tri": "bitwiseTri", "match": "case", **(rename or {})}
    tokens = re.findall(r">>>|&&&|[()]|-?\d+|[A-Za-z_]\w*", text)
    if "".join(tokens) != p.compact(text):
        raise ValueError("unsupported Core expression: " + text)
    pos = 0

    def atom():
        nonlocal pos
        if pos == len(tokens):
            raise ValueError("missing Core operand")
        token = tokens[pos]
        pos += 1
        if token == "(":
            result = comp()
            if pos == len(tokens) or tokens[pos] != ")":
                raise ValueError("unclosed Core expression")
            pos += 1
            return result
        if token in {"O", "I"}:
            return ("take" if token == "O" else "drop", atom())
        if token in {"H", "iden"}:
            return ("iden",)
        if re.fullmatch(r"[oi]+h", token):
            result = ("iden",)
            for letter in reversed(token[:-1]):
                result = ("take" if letter == "o" else "drop", result)
            return result
        return ("name", rename.get(token, token))

    def app():
        nonlocal pos
        result = atom()
        while pos < len(tokens) and tokens[pos] not in {">>>", "&&&", ")"}:
            arg = atom()
            if result in {("name", "take"), ("name", "drop")}:
                result = (result[1], arg)
            elif result[0] == "name" and re.fullmatch(r"[oi]+", result[1]):
                result_name, result = result[1], arg
                for letter in reversed(result_name):
                    result = ("take" if letter == "o" else "drop", result)
            else:
                result = ("app", result, arg)
        return result

    def pair():
        nonlocal pos
        result = app()
        if pos < len(tokens) and tokens[pos] == "&&&":
            pos += 1
            return ("pair", result, pair())
        return result

    def comp():
        nonlocal pos
        result = pair()
        if pos < len(tokens) and tokens[pos] == ">>>":
            pos += 1
            return ("comp", result, comp())
        return result

    result = comp()
    if pos != len(tokens):
        raise ValueError("trailing Core tokens")
    return result


def hbody(source, lhs):
    matches = list(re.finditer(r"^([ ]*)" + re.escape(lhs) + r"\s*=\s*([^\n]*)", source, re.M))
    if len(matches) != 1:
        raise ValueError("missing/duplicate Haskell binding: " + lhs)
    match = matches[0]
    indent = len(match[1])
    lines = [match[2]]
    for line in source[match.end():].splitlines()[1:]:
        if line.strip() == "where" or (line.strip() and len(line) - len(line.lstrip()) <= indent):
            break
        lines.append(line)
    return "\n".join(lines).strip()


def same(left, right, label, rename=None):
    if expression(left, rename) != expression(right):
        raise ValueError("Core tree differs: " + label)


def word_dependencies(s):
    for hs_name, coq_name in [("false", "false"), ("true", "true"), ("cond thn els", "cond"),
                              ("ch", "ch"), ("not t", "not"), ("maj", "maj"), ("xor_xor", "xor3")]:
        same(hbody(s["hs_bit"], hs_name), p.definition(s["coq_bit"], coq_name), "Bit." + coq_name)
    same(hbody(s["hs_arith"], "full_add SingleV"), p.definition(s["word"], "fullAdderBit"), "full_add base")
    same(hbody(s["hs_arith"], "full_add (DoubleV w)"), p.definition(s["word"], "buildFullAdder"), "full_add recursion")
    p.require(s["hs_arith"], "rec = full_add w", "full_add recursive binding")
    p.require(s["hs_arith"], "add w = false &&& iden >>> full_add w", "literal add")
    for name, expected in {
        "fullAdder": "match n with | 0 => fullAdderBit | S n => buildFullAdder fullAdder end",
        "bitwiseTri": "match n with | 0 => op | S n => buildBitwiseTri (bitwiseTri op) end",
        "full_left_shift1": "match n with | 0 => iden | S n => build_full_left_shift1 full_left_shift1 end",
        "full_right_shift1": "match n with | 0 => iden | S n => build_full_right_shift1 full_right_shift1 end",
        "leftmost": "match n with | 0 => iden | S n => build_leftmost leftmost end",
        "rightmost": "match n with | 0 => iden | S n => build_rightmost rightmost end",
        "foldr_comp": "match l with | [] => iden | i::[] => i | i::l => i >>> foldr_comp l end",
    }.items():
        if p.compact(p.definition(s["word"], name)) != p.compact(expected):
            raise ValueError("word recursion differs: " + name)
    tri = s["hs_word"].split("bitwise_tri op = go", 1)[1].split("bitwise_and ::", 1)[0]
    p.require(tri, "go SingleV = op", "bitwise base")
    p.require(tri, "rec = go w", "bitwise recursive binding")
    same(hbody(tri, "go (DoubleV w)"), p.definition(s["word"], "buildBitwiseTri"), "bitwise recursion")
    for hs_name, coq_name in [("bitwise_xor_xor", "xor3Word32"), ("bitwise_ch", "chWord32"), ("bitwise_maj", "majWord32")]:
        same(hbody(s["hs_word"], hs_name), p.definition(s["sha"], coq_name), coq_name)
    for direction in ["left", "right"]:
        full = "full_" + direction + "_shift1"
        if hbody(s["hs_word"], full + " SingleV") != "iden":
            raise ValueError("full shift base differs")
        same(hbody(s["hs_word"], full + " (DoubleV v)"), p.definition(s["word"], "build_" + full), full)
        move = direction + "most"
        if hbody(s["hs_word"], move + " SingleV") != "iden":
            raise ValueError("projection base differs")
        same(hbody(s["hs_word"], move + " (DoubleV v)").replace(move + " v", "rec"),
             p.definition(s["word"], "build_" + move), move)
        body = re.sub(r"\b(leftmost|rightmost|full_left_shift1|full_right_shift1) v\b", r"\1",
                      hbody(s["hs_word"], direction + "_rotate1 v"))
        same(body, p.definition(s["word"], direction + "_rotate1"), "rotate wire")
    same("(unit >>> t) &&& iden >>> full_right_shift1 >>> oh",
         p.definition(s["word"], "right_shift1"), "right shift wire")
    if p.compact(p.definition(s["add"], "canonical_add_word")) != "Bit.false&&&iden>>>@Word.fullAddernterm":
        raise ValueError("canonical add adapter differs")
    for name, expected in {"scribe32": "scribe (fromZ z)", "xor3Word32": "bitwiseTri xor3"}.items():
        if p.compact(p.definition(s["sha"], name)) != p.compact(expected):
            raise ValueError("SHA basic specialization differs: " + name)
    p.require(s["hs"], "scribe32 x = scribe (toWord32 x)", "scribe specialization")
    p.require(s["hs_types"], "toWord32 = toWord word32", "Word32 conversion")
    p.require(s["port"], "Require C.jet_haskell_word_conversion.", "checked conversion foundation")


def constant_wiring(s):
    rotate = s["hs_word"].split("rotate_const v n =", 1)[1].split("left_rotate ::", 1)[0]
    expected_rotate = '''compose (go v n)
 where
  compose [] = iden
  compose l = foldr1 (>>>) l
  go :: (Core term, TyC a, TyC b) => Vector a b -> Int -> [term b b]
  go SingleV n = []
  go v@(DoubleV v') n | even n = rec (n `div` 2)
                    | 1 == n `mod` 4 = left_rotate1 v : rec ((n-1) `div` 2)
                    | 3 == n `mod` 4 = right_rotate1 v : rec ((n+1) `div` 2)
   where
    rec = go (vectorPromote v')'''
    if p.compact(rotate) != p.compact(expected_rotate):
        raise ValueError("Haskell rotation generator differs")
    shift_entry = s["hs_word"].split("shift_const_by t v n |", 1)[1].split("where", 1)[0]
    if p.compact(shift_entry) != p.compact('''vectorSize v <= n = unit >>> fill t v
                     | n < 0 = right_shift_const_by t v (-n)
                     | otherwise = compose (go t v n)'''):
        raise ValueError("Haskell signed-shift dispatch differs")
    shift = s["hs_word"].split("right_shift_const_by t v n |", 1)[1].split("itemsOf ::", 1)[0]
    expected_shift = '''vectorSize v <= n = unit >>> fill t v
                           | n < 0 = shift_const_by t v (-n)
                           | otherwise = compose (go t v n)
 where
  compose [] = iden
  compose l = foldr1 (>>>) l
  go :: (Core term, TyC a, TyC b) => term () a -> Vector a b -> Int -> [term b b]
  go t SingleV 0 = []
  go t v@(DoubleV v') n | even n = rec (n `div` 2)
                      | otherwise = right_shift1 : rec ((n-1) `div` 2)
   where
    right_shift1 = (unit >>> t) &&& iden >>> full_right_shift1 v >>> oh
    rec = go (t &&& t) (vectorPromote v')'''
    if p.compact(shift) != p.compact(expected_shift):
        raise ValueError("Haskell right-shift generator differs")
    bodies = {
        "sha_haskell_rotate_list": '''match n with | 0%nat => [] | S k =>
          if Z.even z then eq_rect _ (fun T => list (term T T)) (sha_haskell_rotate_list (Z.div z 2)) _ (eq_sym VectorPromote)
          else if Z.eqb (z mod 4) 1 then left_rotate1 :: eq_rect _ (fun T => list (term T T))
            (sha_haskell_rotate_list (Z.div (z-1) 2)) _ (eq_sym VectorPromote)
          else if Z.eqb (z mod 4) 3 then right_rotate1 :: eq_rect _ (fun T => list (term T T))
            (sha_haskell_rotate_list (Z.div (z+1) 2)) _ (eq_sym VectorPromote)
          else [] end''',
        "sha_haskell_right_shift_list": '''match n with | 0%nat => [] | S k =>
          if Z.even amount then eq_rect _ (fun T => list (term T T))
            (sha_haskell_right_shift_list (t &&& t) (amount / 2)) _ (eq_sym VectorPromote)
          else right_shift1 t :: eq_rect _ (fun T => list (term T T))
            (sha_haskell_right_shift_list (t &&& t) ((amount-1) / 2)) _ (eq_sym VectorPromote) end''',
        "literal_sha_rotate32": "foldr_comp (@sha_haskell_rotate_list Bit 5 term z)",
        "literal_sha_right_shift32": '''if Z.leb 32 amount then unit >>> @fill Ty.Unit Bit 5 term Bit.false
          else foldr_comp (@sha_haskell_right_shift_list Bit 5 term Bit.false amount)''',
    }
    for name, expected in bodies.items():
        if p.compact(p.definition(s["wiring"], name)) != p.compact(expected):
            raise ValueError("literal constant wiring differs: " + name)


def check(s):
    need = lambda key, text: p.require(s[key], text, "SHA " + key)
    need("catalog", "Sha256Block :: HashJet (Sha256.Hash, Sha256.Block) Sha256.Hash")
    need("catalog", "specificationHash Sha256Block = Sha256.hashBlock")
    need("hs", "type Block = Word512")
    need("hs", "type Hash = Word256")
    need("core", "infixr 1 >>>")
    need("core", "infixr 3 &&&")
    word_dependencies(s)
    constant_wiring(s)
    hs = s["hs"].split("l@Lib{..} = Lib", 1)[1].split("buffer63Empty =", 1)[0]
    round_part = hs.split("    round =", 1)[1].split("    schedule =", 1)[0]
    schedule_part = hs.split("    schedule =", 1)[1]
    bindings = dict(re.findall(r"\blet\s+(\w+)\b.*?:=\s*(.*?)\s+in\b", p.definition(s["port"], "sha_block_tree"), re.S))
    if p.compact(bindings["x32"]) != "@SHA256.xor3Word32term":
        raise ValueError("SHA xor specialization differs")
    aliases = {"part1Round": "part1", "part2Round": "part2", "part1Schedule": "part1"}
    special = {"x32", "k0", "ks", "compression"}
    for key, value in bindings.items():
        if key in special:
            continue
        part = round_part if key in {"t1", "t12", "t1d", "part1Round", "part2Round", "bigSigma0", "bigSigma1"} else hs
        if key in {"smallSigma", "smallSigma0", "smallSigma1", "part1Schedule"}:
            part = schedule_part
        lhs = "collate x" if key == "collate" else aliases.get(key, key)
        value = re.sub(r"@literal_sha_rotate32\s+(\(-\d+\))\s+term", r"rotateW32 \1", value)
        value = re.sub(r"@literal_sha_right_shift32\s+(\d+)\s+term", r"shiftW32 (-\1)", value)
        value = re.sub(r"@SHA256\.(chWord32|majWord32)\s+term", r"\1", value)
        rename = {"part1": "part1Schedule"} if key == "schedule" else {"part1": "part1Round", "part2": "part2Round"}
        same(hbody(part, lhs), value, key, rename)
    root = p.definition(s["port"], "sha_block_tree").rsplit(" in\n", 1)[1]
    hs_root = re.search(r"\bhashBlock\s*=(.*?)\n\s*,\s*ctx8Init", hs, re.S)[1]
    same(hs_root, root, "feed-forward")
    p.require(hs, "collate x = take x &&& drop x >>> add32", "collate")
    p.require(hs, "compression = scribe32 k0 &&& iden >>> foldr (\\k rec -> scribe32 k &&& step >>> rec) round ks", "64-round fold")
    coq_compression = "@SHA256.scribe32 k0 _ term &&& iden >>> fold_right (fun k (rec : term (Ty.Prod Word32 (Ty.Prod Word256 Word512)) Word256) => @SHA256.scribe32 k _ term &&& step >>> rec) round ks"
    if p.compact(bindings["compression"]) != p.compact(coq_compression):
        raise ValueError("Coq compression fold differs")
    hs_constants = [int(x, 16) for x in re.search(r"k0:ks\s*=\s*\[(.*?)\]", hs, re.S)[1].replace("\n", "").split(",")]
    coq_constants = [int(bindings["k0"].replace("%Z", ""))] + [int(x) for x in bindings["ks"].replace("%Z", "").strip("[] ").split(";")]
    if len(hs_constants) != 64 or hs_constants != coq_constants:
        raise ValueError("SHA round constants differ")
    for text in ["oo x = take (take x)", "io x = drop (take x)", "iio x = drop (io x)",
                 "add32 = add word32 >>> ih", "xor_xorWord32 = bitwise_xor_xor word32",
                 "chWord32 = bitwise_ch word32", "majWord32 = bitwise_maj word32",
                 "rotateW32 = rotate_const word32", "shiftW32 = shift_const_by false word32"]:
        p.require(hs, text, "SHA alias")
    for name, expected in {
        "literal_sha_add32": "@canonical_add_word 5 term >>> I H",
        "literal_sha_256_block": "@sha_block_tree term (@literal_sha_add32 term)",
    }.items():
        if p.compact(p.definition(s["port"], name)) != p.compact(expected):
            raise ValueError("literal SHA boundary differs: " + name)
    for theorem, contract in [("sha_256_block_literal_local_spec", "sha_jet_local_spec"),
                              ("sha_256_block_literal_lifecycle_spec", "sha_jet_local_spec_pre (fun m => exists owned, sha_lifecycle m owned)"),
                              ("sha_256_block_literal_startup_spec", "sha_startup_total_spec")]:
        statement = re.search(r"Theorem " + theorem + r"\s*:(.*?)\bProof\.", s["jet"], re.S)
        expected = contract + " f_simplicity_sha_256_block (Ty.Prod Word256 Word512) Word256 (@literal_sha_256_block Alg.CoreFunSem)."
        if not statement or p.compact(statement[1]) != p.compact(expected):
            raise ValueError("SHA public boundary differs: " + theorem)


def sources():
    return {key: p.read_code(path) for key, path in {
        "catalog": REPO / "Haskell/Core/Simplicity/CoreJets.hs",
        "hs": REPO / "Haskell/Core/Simplicity/Programs/Sha256.hs",
        "core": REPO / "Haskell/Core/Simplicity/Term/Core.hs",
        "port": COQ / "C/jet_sha_block_literal.v",
        "sha": COQ / "Simplicity/SHA256.v",
        "word": COQ / "Simplicity/Word.v",
        "coq_bit": COQ / "Simplicity/Bit.v",
        "add": COQ / "C/jet_canonical_add_adapter.v",
        "hs_bit": REPO / "Haskell/Core/Simplicity/Programs/Bit.hs",
        "hs_word": REPO / "Haskell/Core/Simplicity/Programs/Word.hs",
        "hs_types": REPO / "Haskell/Core/Simplicity/Ty/Word.hs",
        "hs_arith": REPO / "Haskell/Core/Simplicity/Programs/Arith.hs",
        "wiring": COQ / "C/jet_sha_block_literal_word.v",
        "jet": COQ / "C/jet_sha_block_literal_local.v",
    }.items()}


def test():
    s = sources()
    check(s)
    # Fixity, routing, every round constant, reused primitives, literal wiring
    # and exact final contracts are independent correspondence obligations.
    mutations = [
        ("catalog", "specificationHash Sha256Block = Sha256.hashBlock", "specificationHash Sha256Block = Sha256.iv"),
        ("hs", "type Block = Word512", "type Block = Word256"),
        ("core", "infixr 3 &&&", "infixl 3 &&&"),
        ("hs", "hashBlock = oh &&& compression", "hashBlock = ih &&& compression"),
        ("hs", "step = round &&& (drop (drop schedule))", "step = round &&& (drop (take schedule))"),
        ("hs", "collate ioih", "collate iioh"),
        ("hs", "foldr (\\k rec", "foldl (\\k rec"),
        ("hs", "add32 = add word32 >>> ih", "add32 = add word32 >>> oh"),
        ("hs_bit", "maj = cond (cond true iden)", "maj = cond (cond false iden)"),
        ("hs_arith", "full_add SingleV = maj &&& xor_xor", "full_add SingleV = xor_xor &&& maj"),
        ("hs_word", "1 == n `mod` 4", "3 == n `mod` 4"),
        ("hs_word", "right_shift1 = (unit >>> t) &&& iden", "right_shift1 = iden &&& (unit >>> t)"),
        ("port", "@literal_sha_right_shift32 3 term", "@literal_sha_right_shift32 10 term"),
        ("port", "@canonical_add_word 5 term", "@Word.adder 5 term"),
        ("wiring", "Z.eqb (z mod 4) 1", "Z.eqb (z mod 4) 3"),
        ("wiring", "Z.div (z+1) 2", "Z.div (z-1) 2"),
        ("wiring", "(amount-1) / 2", "(amount+1) / 2"),
        ("jet", "sha_jet_local_spec f_simplicity_sha_256_block", "False -> sha_jet_local_spec f_simplicity_sha_256_block"),
        ("jet", "f_simplicity_sha_256_block", "f_simplicity_sha_256_ctx_8_init"),
        ("jet", "sha_startup_total_spec", "sha_jet_local_spec"),
        ("jet", "exists owned, sha_lifecycle m owned", "exists owned, sha_lifecycle m owned /\\ False"),
        ("word", "full_right_shift1 >>> O H", "full_right_shift1 >>> I H"),
    ]
    constants = re.search(r"k0:ks\s*=\s*\[(.*?)\]", s["hs"], re.S)[1]
    mutations += [("hs", k.strip(), hex(int(k, 16) ^ 1)) for k in constants.split(",")]
    for key, old, new in mutations:
        if old not in s[key]:
            raise ValueError("inactive SHA mutation fixture: " + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            check(changed)
        except ValueError:
            continue
        raise ValueError("SHA source mutation escaped: " + old)
    print("SHA block Core trees, word/bit dependencies and 64 constants match;", len(mutations), "mutations rejected")


if __name__ == "__main__":
    test()
