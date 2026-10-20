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


def context_add(s):
    """Canonical one-byte path, including failure branches and its dependencies.

    Typed AC ports are frozen explicitly where the small Core parser does not
    read Coq type applications. Their canonical trees are reviewed alongside
    the actual Haskell trees; the Coq bridges prove program/semantic equality.
    """
    def definition(key, name, expected):
        if p.compact(p.definition(s[key], name)) != p.compact(expected):
            raise ValueError("context dependency differs: " + name)

    def replace(text, old, new):
        return re.sub(r"\s*".join(re.escape(c) for c in p.compact(old)), new, text)

    def names(text):
        for old, new in [
            ("@buffer_empty_spec (Word 3) 5 Ty.Unit (Alg.Assertion.toCore term)", "buffer63Empty"),
            ("@buffer_snoc_spec (Word 3) 5 term", "buffer63Snoc"),
            ("@literal_ctx8_increment64 (Alg.Assertion.toCore term)", "increment64"),
            ("@literal_ctx8_no_carry term", "noCarry"),
            ("@literal_sha_256_block (Alg.Assertion.toCore term)", "hashBlock"),
            ("@literal_ctx8_verify_count term", "verifyNumCompression"),
            ("@lt_word_spec term 6", "lt64"),
            ("Alg.scribe sha256_count_limit", "scribe limit"),
        ]:
            text = replace(text, old, new)
        return text

    hs = s["hs"].split("mkLibAssert Lib{..}  = l", 1)[1]
    entry = re.search(r"\bctx8Add1\s*=(.*?)\n\s*,\s*ctx8Addn", hs, re.S)[1]
    entry = replace(entry, "increment word64", "increment64")
    entry = replace(entry, "assertl ih cmrFail0", "noCarry")
    port = p.definition(s["ctx"], "literal_ctx8_add1")
    for name, args in [("literal_ctx8_snoc", "(Alg.Assertion.toCore term)"),
                       ("literal_ctx8_add1_full", "term")]:
        port = replace(port, "@" + name + " " + args, "(" + p.definition(s["ctx"], name) + ")")
    same(entry, names(port), "ctx8Add1 tree and assertion order")
    check_count = hbody(hs, "verifyNumCompression")
    check_count = replace(check_count, "scribe (toWord64 (2^55))", "scribe limit")
    check_count = replace(check_count, "lt word64", "lt64")
    same(check_count, "assert (" + names(p.definition(s["ctx"], "literal_ctx8_count_check")) + ")", "compression-count assertion")
    definition("ctx", "literal_ctx8_no_carry", '''@Alg.Assertion.Combinators.assertl
      Ty.Unit Ty.Unit (Word 6) (Word 6) term (I H) assertion_cmr_fail0''')
    definition("ctx", "literal_ctx8_verify_count", '''
      (@literal_ctx8_count_check (Alg.Assertion.toCore term) &&& unit) >>>
      @Alg.Assertion.Combinators.assertr Ty.Unit Ty.Unit Ty.Unit Ty.Unit term assertion_cmr_fail0 (O H)''')
    same(hbody(s["hs_bit"], "assert t"), "t &&& unit >>> assertr cmrFail0 oh", "assert combinator")
    definition("count", "sha256_count_limit", "@fromZ (WordToZ 6) 36028797018963968")
    p.require(s["ctx"], "sha256_count_limit = @fromZ (WordToZ 6) (2^55)%Z", "checked count constant bridge")
    definition("assert", "assertion_hash0", '''Simplicity.Digest.Hash256
      [Int.zero; Int.zero; Int.zero; Int.zero; Int.zero; Int.zero; Int.zero; Int.zero] eq_refl''')
    definition("assert", "assertion_cmr_fail0", '''@Alg.Assertion.Combinators.fail Ty.Unit Ty.Unit
      Simplicity.MerkleRoot.CommitmentRoot_Assertion_alg (assertion_hash0, assertion_hash0)''')
    p.require(s["merkle"], "cmrFail0 = commitmentRoot (fail0 :: CommitmentRoot () ())", "pruned assertion root")
    p.require(s["core"], "fail0 = fail (hash0, hash0)", "fail root payload")
    p.require(s["digest"], "hash0 = review (over be256) 0", "zero root payload")
    increment = p.definition(s["ctx"], "literal_ctx8_increment64")
    increment = replace(increment, "@Word.zero 6 term", "zero64")
    increment = replace(increment, "@Word.fullAdder 6 term", "fullAdd64")
    increment = replace(increment, "Bit.true", "true")
    full = hbody(s["hs_arith"], "full_increment w")
    full = replace(replace(full, "zero w", "zero64"), "full_add w", "fullAdd64")
    same(increment, "true &&& iden >>> (" + full + ")", "literal increment64")
    same(hbody(s["hs_arith"], "increment w"), "true &&& iden >>> full_increment w", "increment wrapper")
    p.require(s["hs_arith"], "zero = low", "zero alias")
    p.require(s["hs_word"], "low = fill false", "low alias")
    same(hbody(s["hs_word"], "fill t SingleV"), "t", "fill base")
    same(hbody(s["hs_word"], "fill t (DoubleV w)"), "rec &&& rec", "fill recursion")
    p.require(s["hs_word"], "rec = fill t w", "fill recursive binding")
    definition("word", "zero", "match n with | 0 => false | S n => zero &&& zero end")
    same(hbody(s["hs_arith"], "lt w"), "subtract w >>> oh", "lt tree")
    same(hbody(s["hs_arith"], "subtract w"), "false &&& iden >>> full_subtract w", "subtract tree")
    same(hbody(s["hs_arith"], "full_subtract w"), '''
      not oh &&& drop (oh &&& (ih >>> complement w)) >>> full_add w >>> not oh &&& ih''', "full subtraction tree")
    definition("order", "lt_word_spec", "AC.comp (@subtract_word_spec term n) (AC.take AC.iden)")
    definition("subtract", "subtract_word_spec", "AC.comp (AC.pair Bit.false AC.iden) (@full_subtract_word_spec term n)")
    definition("subtract", "full_subtract_word_spec", '''AC.comp
      (AC.pair (Bit.not (AC.take AC.iden))
        (AC.drop (AC.pair (AC.take AC.iden) (AC.comp (AC.drop AC.iden) (@complement_spec n term)))))
      (AC.comp (@Word.fullAdder n term) (AC.pair (Bit.not (AC.take AC.iden)) (AC.drop AC.iden)))''')
    same(hbody(s["hs_word"], "complement SingleV"), "not iden", "complement base")
    same(hbody(s["hs_word"], "complement (DoubleV w)"), "take rec &&& drop rec", "complement recursion")
    p.require(s["hs_word"], "rec = complement w", "complement recursive binding")
    definition("complement", "complement_spec", '''match n with
      | O => @Bit.not Bit term (@Alg.Core.Combinators.iden Bit term)
      | S n => @Alg.Core.Combinators.pair (Word (S n)) (Word n) (Word n) term
          (@Alg.Core.Combinators.take (Word n) (Word n) (Word n) term (complement_spec n))
          (@Alg.Core.Combinators.drop (Word n) (Word n) (Word n) term (complement_spec n)) end''')
    definition("buffer", "buffer_type", '''match depth with
      | Datatypes.O => Ty.Sum Ty.Unit X
      | Datatypes.S d => Ty.Prod (Ty.Sum Ty.Unit (Vector X (Datatypes.S d))) (buffer_type X d) end''')
    definition("buffer", "buffer_empty_spec", '''match depth with
      | Datatypes.O => AC.injl AC.unit
      | Datatypes.S d => AC.pair (AC.injl AC.unit) (buffer_empty_spec X d A) end''')
    same(hbody(s["hs_word"], "bufferEmpty SingleB"), "injl unit", "buffer empty base")
    same(hbody(s["hs_word"], "bufferEmpty (DoubleB b)"), "injl unit &&& bufferEmpty b", "buffer empty recursion")
    definition("ctx_old", "buffer_snoc_spec", '''match depth with
      | O => AC.case (AC.injr (AC.injr (AC.drop AC.iden))) (AC.injl AC.iden)
      | S d => AC.comp
          (AC.pair (AC.comp (AC.pair (AC.take (AC.drop AC.iden)) (AC.drop AC.iden)) (buffer_snoc_spec X d))
                   (AC.take (AC.take AC.iden)))
          (AC.case
            (AC.comp (AC.pair (AC.drop AC.iden) (AC.take AC.iden))
              (AC.case (AC.injr (AC.pair (AC.injr (AC.drop AC.iden)) (buffer_empty_spec X d _)))
                       (AC.injl AC.iden)))
            (AC.injr (AC.pair (AC.drop AC.iden) (AC.take AC.iden)))) end''')
    same(hbody(s["hs_word"], "bufferSnoc SingleB"), "match (injr (injr ih)) (injl iden)", "buffer snoc base")
    same(hbody(s["hs_word"], "bufferSnoc (DoubleB b)"), '''
      (oih &&& ih >>> bufferSnoc b) &&& ooh >>>
      match (ih &&& oh >>> match (injr (injr ih &&& bufferEmpty b)) (injl iden))
            (injr (ih &&& oh))''', "buffer snoc recursive tree")
    definition("ctx_init", "sha256_ctx8_type", "Ty.Prod (buffer_type (Word 3) 5) (Ty.Prod (Word 6) (Word 8))")
    p.require(s["hs"], "type Ctx8 = (Buffer63 Word8, (Word64, Word256))", "context type")
    for size, half in [(2, 1), (4, 2), (8, 4), (16, 8), (32, 16), (64, 32), (128, 64), (256, 128)]:
        p.require(s["hs_types"], f"vector{size} = DoubleV vector{half}", "word vector depth")
    for size in [8, 64, 256]:
        p.require(s["hs_types"], f"type Word{size} = Vector{size} Bit", "context word carrier")
        p.require(s["hs_types"], f"word{size} = vector{size}", "context word witness")
    p.require(s["hs_types"], "buffer1 = SingleB", "buffer base")
    p.require(s["hs_types"], "type Buffer1 x = S x", "buffer base carrier")
    for size, half in [(3, 1), (7, 3), (15, 7), (31, 15), (63, 31)]:
        p.require(s["hs_types"], f"buffer{size} = DoubleB buffer{half}", "buffer depth")
        p.require(s["hs_types"], f"type Buffer{size} x = (S (Vector{(size+1)//2} x), Buffer{half} x)", "buffer carrier")
    p.require(s["hs"], "libAssert = mkLibAssert lib", "canonical assertion library")
    p.require(s["catalog"], "Sha256Ctx8Add1 :: HashJet (Sha256.Ctx8, Word8) Sha256.Ctx8", "context-add type")
    p.require(s["catalog"], "specificationHash Sha256Ctx8Add1 = Sha256.ctx8Add1", "context-add dispatch")
    addn = re.search(r"\bctx8Addn\s*=(.*?)\n\s*,\s*ctx8AddBuffer", hs, re.S)[1]
    expected_addn = r'''\v -> case v of SingleV -> ctx8Add1
      (DoubleV v) -> let rec = ctx8Addn v in (oh &&& ioh >>> rec) &&& iih >>> rec'''
    if p.compact(addn) != p.compact(expected_addn):
        raise ValueError("Haskell context vector recursion differs")
    definition("ctx", "literal_ctx8_addn", '''match n with
      | Datatypes.O => @literal_ctx8_add1 term
      | Datatypes.S k => (O H &&& I O H >>> @literal_ctx8_addn k term) &&& I I H >>> @literal_ctx8_addn k term end''')
    same(addn.rsplit(" in", 1)[1], "(O H &&& I O H >>> rec) &&& I I H >>> rec", "vector sequencing tree")
    p.require(s["hs_types"], "type Vector1 x = x", "vector base type")
    p.require(s["hs_types"], "type Vector2 x = (x,x)", "vector pair type")
    p.require(s["hs_types"], "vector1 = SingleV", "vector base witness")
    for level in range(2, 13):
        size, half = 2**level, 2**(level-1)
        p.require(s["hs_types"], f"type Vector{size} x = Vector2 (Vector{half} x)", "vector carrier recursion")
    for k in range(10):
        size, bits = 2**k, 8 * 2**k
        p.require(s["catalog"], f"Sha256Ctx8Add{size} :: HashJet (Sha256.Ctx8, Word{bits}) Sha256.Ctx8", "context width type")
        target = "Sha256.ctx8Add1" if k == 0 else f"Sha256.ctx8Addn vector{size}"
        p.require(s["catalog"], f"specificationHash Sha256Ctx8Add{size} = " + target, "context width dispatch")
        p.require(s["hs_types"], f"type Word{bits} = Vector{bits} Bit", "context width carrier")
        p.require(s["hs_types"], f"vector{2*size} = DoubleV vector{size}", "context width witness")
        port_arg = "(Word 3)" if k == 0 else f"(Vector (Word 3) {k})"
        port_program = "@literal_ctx8_add1 optalg" if k == 0 else f"@literal_ctx8_addn {k} optalg"
        for suffix in ["local", "startup"]:
            contract = "sha_jet_partial_local_spec" if suffix == "local" else "sha_startup_partial_spec"
            name = f"sha_256_ctx_8_add_{size}_literal_{suffix}_spec"
            statement = re.search(r"Theorem " + name + r"\s*:(.*?)\bProof\.", s["ctx_jet"], re.S)
            expected = (f"memcpy_model -> {contract} f_simplicity_sha_256_ctx_8_add_{size} "
                        f"(Ty.Prod sha256_ctx8_type {port_arg}) sha256_ctx8_type ({port_program}).")
            if not statement or p.compact(statement[1]) != p.compact(expected):
                raise ValueError("context-add public contract differs: " + name)


def buffer_finalize(s):
    """The remaining context programs, including empty input and padding."""
    def definition(key, name, expected):
        if p.compact(p.definition(s[key], name)) != p.compact(expected):
            raise ValueError("buffer/finalizer dependency differs: " + name)

    def replace(text, old, new):
        return re.sub(r"\s*".join(re.escape(c) for c in p.compact(old)), new, text)

    hs = s["hs"].split("mkLibAssert Lib{..}  = l", 1)[1]
    buf = re.search(r"\bctx8AddBuffer\s*=(.*?)\n\s*,\s*ctx8Finalize", hs, re.S)[1]
    p.require(s["hs_types"], "toWord64 = toWord word64", "64-bit constant conversion")
    same(hbody(s["core"], "elimS r s t"), "r &&& unit >>> match (take s) (take t)", "sum elimination tree")
    same(hbody(s["core"], "copair"), "elimS iden", "copair wrapper")
    definition("coq_alg", "elimS", "comp (pair r unit) (case (take s) (take t))")
    definition("coq_alg", "copair", "elimS iden")
    cases = re.fullmatch(r"\s*\\b\s*->\s*case\s+b\s+of\s+SingleB\s*->(.*?)\(DoubleB b\)\s*->(.*)", buf, re.S)
    if not cases:
        raise ValueError("canonical buffer recursion shape differs")
    definition("buf_port", "literal_ctx8_add_buffer", '''match d with
      | Datatypes.O => I H &&& O H >>>
          case (I (iden &&& @literal_ctx8_verify_count term >>> O H))
               (I H &&& O H >>> @literal_ctx8_add1 term)
      | Datatypes.S k =>
          (I O H &&& O H >>> case (I H) (I H &&& O H >>> @literal_ctx8_addn (S k) term))
            &&& I I H >>> @literal_ctx8_add_buffer k term end''')
    same(cases[1], "I H &&& O H >>> case (I (iden &&& verifyNumCompression >>> O H)) (I H &&& O H >>> ctx8Add1)", "empty/single buffer tree")
    same(cases[2], "(I O H &&& O H >>> case (I H) (I H &&& O H >>> ctx8Addn (bufferVector b))) &&& I I H >>> ctx8AddBuffer b", "buffer sequence tree")
    p.require(s["hs_types"], "bufferVector SingleB = vector2", "buffer vector base")
    p.require(s["hs_types"], "bufferVector (DoubleB buf) = DoubleV (bufferVector buf)", "buffer vector recursion")
    for size, half in [(127, 63), (255, 127), (511, 255)]:
        p.require(s["hs_types"], f"buffer{size} = DoubleB buffer{half}", "extended buffer depth")
        p.require(s["hs_types"], f"type Buffer{size} x = (S (Vector{(size+1)//2} x), Buffer{half} x)", "extended buffer carrier")

    def names(text):
        leaves = [
            ("@literal_ctx8_verify_count term", "verifyNumCompression"),
            ("@Word.zero 6 (Alg.Assertion.toCore term)", "zero word64"),
            ("@literal_ctx8_addn 3 term", "ctx8Add8"),
            ("@literal_sha_pad063 (Alg.Assertion.toCore term)", "pad063"),
            ("@literal_sha_buffer63_size term", "buffer63Size"),
            ("@left_pad_low_spec term 3 3", "left_pad_low word8 vector8"),
            ("@literal_sha_left_shift64 6 term", "shift_const_by false word64 6"),
            ("@literal_sha_left_shift64 3 term", "shift_const_by false word64 3"),
            ("@literal_sha_add64 term", "add64"),
            ("@literal_sha_256_block (Alg.Assertion.toCore term)", "hashBlock"),
            ("Alg.scribe pad_word64", "scribe pad64"),
        ]
        for old, new in leaves:
            text = replace(text, old, new)
        return text

    port = p.definition(s["final_port"], "literal_ctx8_finalize")
    for name, arg in [("literal_ctx8_finalize_pad", "term"), ("literal_ctx8_clear_count", "term"),
                      ("literal_ctx8_bitlen", "(Alg.Assertion.toCore term)"),
                      ("literal_ctx8_finalize_block", "(Alg.Assertion.toCore term)")]:
        port = replace(port, "@" + name + " " + arg, "(" + p.definition(s["final_port"], name) + ")")
    entry = re.search(r"\bctx8Finalize\s*=(.*?)\n\s*\}", hs, re.S)[1]
    entry = replace(entry, "scribe (toWord64 (2^63))", "scribe pad64")
    same(entry, names(port), "finalizer complete tree")
    same(hbody(hs, "buffer63Size"), p.definition(s["final_port"], "literal_sha_buffer63_size").replace("Bit.", ""), "six buffer flags")
    for suffix, prev, zero in [("03", "01", 4), ("07", "03", 5), ("015", "07", 6), ("031", "015", 7), ("063", "031", 8)]:
        body = p.definition(s["final_port"], "literal_sha_pad" + suffix)
        body = replace(body, "@literal_sha_pad" + prev + " term", "pad" + prev)
        body = replace(body, f"@Word.zero {zero} term", f"zero word{2**zero}")
        same(hbody(hs, "pad" + suffix), body, "padding stage " + suffix)
    body = p.definition(s["final_port"], "literal_sha_pad01")
    body = replace(replace(body, "@Word.zero 4 term", "zero word16"), "@Word.zero 3 term", "zero word8")
    same(hbody(hs, "pad01"), body, "padding base")
    same(hbody(hs, "ctx8Add8"), "ctx8Addn vector8", "padding append width")
    body = replace(p.definition(s["final_word"], "literal_sha_add64"), "@canonical_add_word 6 term", "add word64")
    same(hbody(hs, "add64"), body, "literal finalizer addition")
    definition("final_old", "pad_word64", "@fromZ (WordToZ 6) 9223372036854775808")
    p.require(s["final_port"], "pad_word64 = @fromZ (WordToZ 6) (2^63)%Z", "checked padding constant bridge")
    definition("pad", "left_pad_low_spec", "left_pad_pad (AC.comp AC.unit (low_word w)) k")
    definition("pad", "low_word", "fill (n := w) (@Bit.false Ty.Unit term)")
    definition("pad", "left_pad_pad", "match k with | O => AC.iden | S k => AC.pair (fill (n := k) t) (left_pad_pad t k) end")
    same(hbody(s["hs_word"], "left_pad_low w v"), "left_pad_pad (unit >>> low w) v", "left padding wrapper")
    same(hbody(s["hs_word"], "left_pad_pad _ SingleV"), "iden", "left padding base")
    same(hbody(s["hs_word"], "left_pad_pad t (DoubleV v)"), "fill t v &&& left_pad_pad t v", "left padding recursion")
    definition("word", "build_fill", "rec &&& rec")
    definition("word", "fill", "match n with | 0 => t | (S n) => build_fill (fill t) end")
    same("iden &&& (unit >>> t) >>> full_left_shift1 >>> ih", p.definition(s["word"], "left_shift1"), "left shift wire")
    shift = s["hs_word"].split("shift_const_by t v n |", 1)[1].split("--", 1)[0]
    # Active-source reader removes comments, so end at the next declaration.
    shift = shift.split("right_shift_const_by ::", 1)[0]
    expected_shift = '''vectorSize v <= n = unit >>> fill t v
      | n < 0 = right_shift_const_by t v (-n) | otherwise = compose (go t v n)
      where compose [] = iden compose l = foldr1 (>>>) l
      go :: (Core term, TyC a, TyC b) => term () a -> Vector a b -> Int -> [term b b]
      go t SingleV 0 = []
      go t v@(DoubleV v') n | even n = rec (n `div` 2)
                          | otherwise = left_shift1 : rec ((n-1) `div` 2)
       where left_shift1 = iden &&& (unit >>> t) >>> full_left_shift1 v >>> ih
             rec = go (t &&& t) (vectorPromote v')'''
    if p.compact(shift) != p.compact(expected_shift):
        raise ValueError("Haskell left-shift generator differs")
    definition("final_word", "sha_haskell_left_shift_list", '''match n with
      | Datatypes.O => [] | Datatypes.S k =>
        if Z.even amount then eq_rect _ (fun T => list (term T T))
          (sha_haskell_left_shift_list (t &&& t) (amount / 2)) _ (eq_sym VectorPromote)
        else left_shift1 t :: eq_rect _ (fun T => list (term T T))
          (sha_haskell_left_shift_list (t &&& t) ((amount-1) / 2)) _ (eq_sym VectorPromote) end''')
    definition("final_word", "literal_sha_left_shift64", '''
      if Z.leb 64 amount then unit >>> @fill Ty.Unit Bit 6 term Bit.false
      else foldr_comp (@sha_haskell_left_shift_list Bit 6 term Bit.false amount)''')
    for tag, key, stem, args, program in [
        ("Sha256Ctx8AddBuffer511", "buf_jet", "sha_256_ctx_8_add_buffer_511",
         "(Ty.Prod sha256_ctx8_type (buffer_type (Word 3) 8)) sha256_ctx8_type", "@literal_ctx8_add_buffer 8 optalg"),
        ("Sha256Ctx8Finalize", "final_jet", "sha_256_ctx_8_finalize",
         "sha256_ctx8_type (Word 8)", "@literal_ctx8_finalize optalg"),
    ]:
        canonical = "Sha256.ctx8AddBuffer buffer511" if key == "buf_jet" else "Sha256.ctx8Finalize"
        source_type = "(Sha256.Ctx8, Buffer511 Word8) Sha256.Ctx8" if key == "buf_jet" else "Sha256.Ctx8 Sha256.Hash"
        p.require(s["catalog"], f"{tag} :: HashJet {source_type}", "tail jet type")
        p.require(s["catalog"], f"specificationHash {tag} = {canonical}", "tail jet dispatch")
        for suffix in ["local", "startup"]:
            contract = "sha_jet_partial_local_spec" if suffix == "local" else "sha_startup_partial_spec"
            name = f"{stem}_literal_{suffix}_spec"
            statement = re.search(r"Theorem " + name + r"\s*:(.*?)\bProof\.", s[key], re.S)
            expected = f"memcpy_model -> {contract} f_simplicity_{stem} {args} ({program})."
            if not statement or p.compact(statement[1]) != p.compact(expected):
                raise ValueError("buffer/finalizer public contract differs: " + name)


def tapdata(s):
    """Fixed host recipe and canonical initializer, not an arbitrary decoder proof."""
    def need(key, text):
        p.require(s[key], text, "TapData " + key)

    def definition(key, name, expected):
        if p.compact(p.definition(s[key], name)) != p.compact(expected):
            raise ValueError("TapData port differs: " + name)

    need("catalog", "TapdataInit :: BitcoinJet () Sha256.Ctx8")
    need("catalog", "specificationBitcoin TapdataInit = Sha256.tapdataInit")
    need("hs", 'tapdataPrefix = scribe . toWord256 . integerHash256 . ivHash . tagIv $ fromString "TapData"')
    need("digest", "noTagIv = IV sha256Incremental")
    need("digest", "tagIv tag = compress noTagIv (tagDigest, tagDigest)")
    need("digest", "tagDigest = bsHash . BSC.pack $ tag")
    need("digest", "bsHash = bslHash . BSL.fromStrict")
    need("digest", "bslHash = ivHash . IV . pushChunks sha256Incremental . padSHA1")
    need("digest", '''ivHash (IV state) = case pushEndOfInput state of
      Done _ _ x -> Hash256 . BSS.toShort . BSL.toStrict . Binary.encode $ x
      _ -> error "getHash256 unexpected decoder state"''')
    need("digest", "compress (IV state) (h1, h2) = IV $ state `pushChunk` BSS.fromShort (hash256 h1) `pushChunk` BSS.fromShort (hash256 h2)")
    need("digest", "integerHash256 h = toInteger $ h^.be256_")
    need("digest", "be256_ = under be256")
    need("digest", '''be256 = adapter to fro where
      fro w = Hash256 $ BSS.toShort (encode w)
      to h = foldl' go 0 . BSS.unpack $ hash256 h where
        go n w = (n `shiftL` 8) .|. fromIntegral w''')
    # The vendored module uses Data.Binary's Word32 get/put interface.
    need("pure", "import Data.Binary")
    need("pure", "data SHA256State = SHA256S !Word32 !Word32 !Word32 !Word32 !Word32 !Word32 !Word32 !Word32")
    need("pure", "sha256Incremental = runSHAIncremental initialSHA256State processSHA256Block")
    need("pure", '''runSHAIncremental s nextChunk = runGetIncremental (getAll s) where
      getAll s_in = do done <- isEmpty
                      if done then return s_in else nextChunk s_in >>= getAll''')
    need("pure", "instance Binary SHA256State where put = synthesizeSHA256 get = getSHA256")
    need("pure", "synthesizeSHA256 (SHA256S a b c d e f g h) = do " + " ".join("putWord32be " + x for x in "abcdefgh"))
    for name, body in {
        "ch x y z": "(x .&. y) `xor` (complement x .&. z)",
        "maj x y z": "(x .&. (y .|. z)) .|. (y .&. z)",
        "bsig256_0 x": "rotateR x 2 `xor` rotateR x 13 `xor` rotateR x 22",
        "bsig256_1 x": "rotateR x 6 `xor` rotateR x 11 `xor` rotateR x 25",
        "lsig256_0 x": "rotateR x 7 `xor` rotateR x 18 `xor` shiftR x 3",
        "lsig256_1 x": "rotateR x 17 `xor` rotateR x 19 `xor` shiftR x 10",
    }.items():
        if p.compact(hbody(s["pure"], name)) != p.compact(body):
            raise ValueError("host SHA word function differs: " + name)
    schedule = s["pure"].split("getSHA256Sched = do", 1)[1].split("data SHA512Sched", 1)[0]
    expected = " ".join(f"w{j:02} <- getWord32be" for j in range(16)) + " let "
    expected += " ".join(f"w{j:02} = lsig256_1 w{j-2:02} + w{j-7:02} + lsig256_0 w{j-15:02} + w{j-16:02}" for j in range(16, 64))
    expected += " return $! SHA256Sched " + " ".join(f"w{j:02}" for j in range(64))
    if p.compact(schedule) != p.compact(expected):
        raise ValueError("host schedule/read order differs")
    process = s["pure"].split("processSHA256Block !s00@", 1)[1].split("step256 ::", 1)[0]
    rounds = re.findall(r"s(\d\d)\s*=\s*step256\s+s(\d\d)\s+(0x[0-9a-f]+)\s+w(\d\d)", process)
    constants = [int(k, 16) for k in re.search(r"k0:ks\s*=\s*\[(.*?)\]", s["hs"], re.S)[1].split(",")]
    if len(rounds) != 64 or [(int(a), int(b), int(k, 16), int(w)) for a,b,k,w in rounds] != [(j+1,j,k,j) for j,k in enumerate(constants)]:
        raise ValueError("host round constants/order differ")
    expected = "(SHA256S " + " ".join(x+"00" for x in "abcdefgh") + ") = do (SHA256Sched "
    expected += " ".join(f"w{j:02}" for j in range(64)) + ") <- getSHA256Sched let "
    expected += " ".join(f"s{j+1:02} = step256 s{j:02} {k} w{j:02}" for j, (_,_,k,_) in enumerate(rounds))
    expected += " SHA256S " + " ".join(x+"64" for x in "abcdefgh") + " = s64 return $! SHA256S "
    expected += " ".join(f"({x}00 + {x}64)" for x in "abcdefgh")
    if p.compact(process) != p.compact(expected):
        raise ValueError("host compression/feedforward differs")
    step = s["pure"].split("step256 !(SHA256S", 1)[1].split("processSHA512Block ::", 1)[0]
    expected = '''a b c d e f g h) k w = SHA256S a' b' c' d' e' f' g' h' where
      t1 = h + bsig256_1 e + ch e f g + k + w t2 = bsig256_0 a + maj a b c
      h' = g g' = f f' = e e' = d + t1 d' = c c' = b b' = a a' = t1 + t2'''
    if p.compact(step) != p.compact(expected):
        raise ValueError("host SHA step differs")
    iv = [int(x, 16) for x in re.findall(r"0x[0-9a-f]+", hbody(s["pure"], "initialSHA256State"))]
    if iv != [int(x, 16) for x in re.findall(r"0x[0-9a-f]+", p.definition(s["host"], "tap_host_iv"))] or len(iv) != 8:
        raise ValueError("host SHA initial state differs")
    ws = [f"Int.repr {hex(x)}" for x in iv]
    definition("host", "tap_host_iv", f"((({ws[0]}, {ws[1]}), ({ws[2]}, {ws[3]})), (({ws[4]}, {ws[5]}), ({ws[6]}, {ws[7]})))")
    statement = re.search(r"Lemma tap_host_round_constants\s*:\s*map Int.unsigned SHA256.K256\s*=\s*\[(.*?)\]", s["host"], re.S)
    if not statement or [int(x, 16) for x in statement[1].split(";")] != constants:
        raise ValueError("checked host constant bridge differs")
    for fragment in [
        "padSHA1 = generic_pad 448 512 64",
        "generic_pad a b lSize bs = BS.fromChunks $! go 0 chunks where chunks = BS.toChunks bs go !len [] = generic_pad_chunks a b lSize len go !len (c:cs) = c : go (len + SBS.length c) cs",
        "generic_pad_chunks a b lSize len = let lenBits = fromIntegral $ len * 8 k = calc_k a b lenBits kBytes = (k + 1) `div` 8 nZeroBytes = fromIntegral $! kBytes - 1 padLength = toBigEndianSBS lSize lenBits in [SBS.singleton 0x80, SBS.replicate nZeroBytes 0, padLength]",
        "calc_k a b l = if r <= -1 then fromIntegral r + b else fromIntegral r where r = toInteger a - toInteger l `mod` toInteger b - 1",
        "toBigEndianSBS s val = SBS.pack $ map getBits [s - 8, s - 16 .. 0] where getBits x = fromIntegral $ (val `shiftR` x) .&. 0xFF",
    ]:
        need("pure", fragment)
    ports = {
        "tap_host_state": "(((Int.int * Int.int) * (Int.int * Int.int)) * ((Int.int * Int.int) * (Int.int * Int.int)))%type",
        "tap_host_ror": "Int.ror x (Int.repr n)",
        "tap_host_bsig0": "Int.xor (Int.xor (tap_host_ror x 2) (tap_host_ror x 13)) (tap_host_ror x 22)",
        "tap_host_bsig1": "Int.xor (Int.xor (tap_host_ror x 6) (tap_host_ror x 11)) (tap_host_ror x 25)",
        "tap_host_lsig0": "Int.xor (Int.xor (tap_host_ror x 7) (tap_host_ror x 18)) (Int.shru x (Int.repr 3))",
        "tap_host_lsig1": "Int.xor (Int.xor (tap_host_ror x 17) (tap_host_ror x 19)) (Int.shru x (Int.repr 10))",
        "tap_host_ch": "Int.xor (Int.and x y) (Int.and (Int.not x) z)",
        "tap_host_maj": "Int.or (Int.and x (Int.or y z)) (Int.and y z)",
        "tap_host_step": "let '(((a,b),(c,d)),((e,f),(g,h))) := s in let '(k,w) := kw in let t1 := Int.add (Int.add (Int.add (Int.add h (tap_host_bsig1 e)) (tap_host_ch e f g)) k) w in let t2 := Int.add (tap_host_bsig0 a) (tap_host_maj a b c) in (((Int.add t1 t2,a),(b,c)),((Int.add d t1,e),(f,g)))",
        "tap_host_schedule_word": "Int.add (Int.add (Int.add (tap_host_lsig1 (nth (j-2) ws Int.zero)) (nth (j-7) ws Int.zero)) (tap_host_lsig0 (nth (j-15) ws Int.zero))) (nth (j-16) ws Int.zero)",
        "tap_host_be32": "fold_left (fun a b => Int.add (Int.shl a (Int.repr 8)) b) (firstn 4 (skipn (4*j) bs)) Int.zero",
        "tap_host_compress": "let first16 := map (tap_host_be32 bs) (seq 0 16) in let ws := fold_left (fun ws j => ws ++ [tap_host_schedule_word ws j]) (seq 16 48) first16 in tap_host_feedforward s (fold_left tap_host_step (combine SHA256.K256 ws) s)",
        "tap_host_feedforward": "let '(((a,b),(c,d)),((e,f),(g,h))) := s in let '(((a',b'),(c',d')),((e',f'),(g',h'))) := t in (((Int.add a a',Int.add b b'),(Int.add c c',Int.add d d')), ((Int.add e e',Int.add f f'),(Int.add g g',Int.add h h')))",
        "tap_host_state_words": "let '(((a,b),(c,d)),((e,f),(g,h))) := s in [a;b;c;d;e;f;g;h]",
        "tap_host_hash": "let '(((a,b),(c,d)),((e,f),(g,h))) := s in Digest.Hash256 [a;b;c;d;e;f;g;h] eq_refl",
        "tap_host_put32": "map (fun k => Int.and (Int.shru x (Int.repr k)) (Int.repr 255)) [24;16;8;0]",
        "tap_host_tag_bytes": 'map (fun b => Int.repr (Byte.unsigned b)) (SHA256.str_to_bytes "TapData"%string)',
        "tap_host_pad": "let bits := 8 * len in let r := 448 - bits mod 512 - 1 in let k := if Z.leb r (-1) then r + 512 else r in [Int.repr 128] ++ repeat Int.zero (Z.to_nat ((k+1)/8-1)) ++ map (fun s => Int.repr (Z.land (Z.shiftr bits s) 255)) [56;48;40;32;24;16;8;0]",
        "tap_host_tag_state": "tap_host_compress tap_host_iv (tap_host_tag_bytes ++ tap_host_pad 7)",
        "tap_host_tag_digest": "flat_map tap_host_put32 (tap_host_state_words tap_host_tag_state)",
        "tap_host_prefix_state": "tap_host_compress tap_host_iv (tap_host_tag_digest ++ tap_host_tag_digest)",
        "tap_host_prefix": "from_hash256 (tap_host_hash tap_host_prefix_state)",
    }
    for name, body in ports.items():
        definition("host", name, body)
    definition("tap_port", "literal_tapdata_one64", "Bit.true >>> @left_pad_low_spec term 0 6")
    need("hs_types", "type Word1 = Vector1 Bit")
    need("hs_types", "word1 = vector1")
    definition("tap_port", "literal_tapdata_init", "@buffer_empty_spec (Word 3) 5 Ty.Unit term &&& (@literal_tapdata_one64 term &&& Alg.scribe tap_host_prefix)")
    same(hbody(s["hs_arith"], "one w"), "true >>> left_pad_low word1 w", "TapData one word")
    need("hs", "tapdataInit = buffer63Empty &&& (one word64 &&& tapdataPrefix)")
    for suffix in ["local", "startup"]:
        contract = "sha_jet_local_spec_pre (fun m => sha_globals_ok m /\\ sha_tag_ok m)" if suffix == "local" else "sha_startup_total_spec"
        statement = re.search(r"Theorem tapdata_init_literal_" + suffix + r"_spec\s*:(.*?)\bProof\.", s["tap_jet"], re.S)
        expected = f"memcpy_model -> {contract} f_simplicity_tapdata_init Ty.Unit sha256_ctx8_type (@literal_tapdata_init Alg.CoreFunSem)."
        if not statement or p.compact(statement[1]) != p.compact(expected):
            raise ValueError("TapData complete public contract differs")


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
        "ctx": COQ / "C/jet_sha_ctx8_literal.v",
        "ctx_old": COQ / "C/jet_sha_ctx8_spec.v",
        "ctx_init": COQ / "C/jet_sha256_ctx8_init_spec.v",
        "ctx_jet": COQ / "C/jet_sha_ctx8_literal_local.v",
        "buffer": COQ / "C/jet_buffer_empty_spec.v",
        "count": COQ / "C/jet_sha256_count_assertion.v",
        "assert": COQ / "C/jet_assertion_spec.v",
        "merkle": REPO / "Haskell/Core/Simplicity/MerkleRoot/Impl.hs",
        "digest": REPO / "Haskell/Core/Simplicity/Digest.hs",
        "order": COQ / "C/jet_order_spec.v",
        "subtract": COQ / "C/jet_subtract_spec.v",
        "complement": COQ / "C/jet_complement_spec.v",
        "buf_port": COQ / "C/jet_sha_buffer_literal.v",
        "buf_jet": COQ / "C/jet_sha_buffer_literal_local.v",
        "final_word": COQ / "C/jet_sha_finalize_literal_word.v",
        "final_port": COQ / "C/jet_sha_finalize_literal.v",
        "final_jet": COQ / "C/jet_sha_finalize_literal_local.v",
        "final_old": COQ / "C/jet_sha_finalize_spec.v",
        "pad": COQ / "C/jet_core_pad_spec.v",
        "coq_alg": COQ / "Simplicity/Alg.v",
        "pure": REPO / "Haskell/Core/Simplicity/Digest/Pure/SHA.hs",
        "host": COQ / "C/jet_tapdata_host_recipe.v",
        "tap_port": COQ / "C/jet_tapdata_literal.v",
        "tap_jet": COQ / "C/jet_tapdata_literal_local.v",
    }.items()}


def test():
    s = sources()
    check(s)
    context_add(s)
    buffer_finalize(s)
    tapdata(s)
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
    context_mutations = [
        ("catalog", "specificationHash Sha256Ctx8Add1 = Sha256.ctx8Add1", "specificationHash Sha256Ctx8Add1 = Sha256.ctx8Init"),
        ("hs", "type Ctx8 = (Buffer63 Word8, (Word64, Word256))", "type Ctx8 = (Buffer31 Word8, (Word64, Word256))"),
        ("hs", "assertl ih cmrFail0", "assertl oh cmrFail0"),
        ("hs", "(verifyNumCompression &&& iden)", "(iden &&& verifyNumCompression)"),
        ("hs", "(2^55)", "(2^54)"),
        ("hs_word", "bufferSnoc SingleB = match (injr (injr ih))", "bufferSnoc SingleB = match (injl (injr ih))"),
        ("hs_arith", "full_increment w = oh &&&", "full_increment w = ih &&&"),
        ("hs_arith", "lt w = subtract w >>> oh", "lt w = subtract w >>> ih"),
        ("ctx", "(I H) assertion_cmr_fail0", "(O H) assertion_cmr_fail0"),
        ("ctx", "(I I H &&& O H >>>", "(O H &&& I I H >>>"),
        ("ctx", "case (@literal_ctx8_add1_full term) iden", "case iden (@literal_ctx8_add1_full term)"),
        ("count", "36028797018963968", "36028797018963969"),
        ("ctx_old", "AC.injr (AC.injr (AC.drop AC.iden))", "AC.injr (AC.injr (AC.take AC.iden))"),
        ("order", "AC.comp (@subtract_word_spec term n) (AC.take AC.iden)", "AC.comp (@subtract_word_spec term n) (AC.drop AC.iden)"),
        ("ctx_jet", "memcpy_model ->", "False -> memcpy_model ->"),
        ("ctx_jet", "f_simplicity_sha_256_ctx_8_add_1", "f_simplicity_sha_256_ctx_8_add_2"),
        ("hs", "(oh &&& ioh >>> rec) &&& iih >>> rec", "(oh &&& iih >>> rec) &&& ioh >>> rec"),
        ("ctx", "@literal_ctx8_addn k term) &&& I I H", "@literal_ctx8_addn k term) &&& O I H"),
        ("catalog", "specificationHash Sha256Ctx8Add512 = Sha256.ctx8Addn vector512", "specificationHash Sha256Ctx8Add512 = Sha256.ctx8Addn vector256"),
        ("ctx_jet", "(@literal_ctx8_addn 9 optalg)", "(@literal_ctx8_addn 8 optalg)"),
    ]
    for key, old, new in context_mutations:
        if old not in s[key]:
            raise ValueError("inactive context mutation: " + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            context_add(changed)
        except ValueError:
            continue
        raise ValueError("context source mutation escaped: " + old)
    print("SHA context-add canonical tree, buffer, counter and assertion dependencies match;", len(context_mutations), "mutations rejected")
    tail_mutations = [
        ("hs", "drop (iden &&& verifyNumCompression >>> oh)", "drop (iden &&& iden >>> oh)"),
        ("hs", "ctx8Addn (bufferVector b)", "ctx8Add1"),
        ("hs_types", "bufferVector SingleB = vector2", "bufferVector SingleB = vector1"),
        ("catalog", "specificationHash Sha256Ctx8AddBuffer511 = Sha256.ctx8AddBuffer buffer511", "specificationHash Sha256Ctx8AddBuffer511 = Sha256.ctx8AddBuffer buffer255"),
        ("buf_port", "@literal_ctx8_verify_count term", "iden"),
        ("buf_port", "@literal_ctx8_addn (S k) term", "@literal_ctx8_addn k term"),
        ("buf_jet", "memcpy_model ->", "False -> memcpy_model ->"),
        ("hs", "verifyNumCompression >>> zero word64", "zero word64 >>> verifyNumCompression"),
        ("hs", "take (take iioh) &&& ih", "take (take ioih) &&& ih"),
        ("hs", "pad063 = oh &&& drop pad031 >>> match (ih &&& take (zero word256))", "pad063 = oh &&& drop pad031 >>> match (ih &&& take (zero word128))"),
        ("hs", "scribe (toWord64 (2^63))", "scribe (toWord64 (2^62))"),
        ("final_port", "@literal_sha_left_shift64 6 term", "@literal_sha_left_shift64 3 term"),
        ("final_port", "Bit.false &&& Bit.false", "Bit.true &&& Bit.false"),
        ("final_port", "(2^63)%Z", "(2^62)%Z"),
        ("final_old", "9223372036854775808", "9223372036854775807"),
        ("final_word", "@canonical_add_word 6 term", "@Word.adder 6 term"),
        ("final_word", "(amount-1) / 2", "(amount+1) / 2"),
        ("pad", "AC.pair (fill (n := k) t) (left_pad_pad t k)", "AC.pair (left_pad_pad t k) (fill (n := k) t)"),
        ("word", "full_left_shift1 >>> I H", "full_left_shift1 >>> O H"),
        ("final_jet", "memcpy_model ->", "False -> memcpy_model ->"),
        ("final_jet", "f_simplicity_sha_256_ctx_8_finalize", "f_simplicity_sha_256_ctx_8_add_buffer_511"),
        ("hs_types", "toWord64 = toWord word64", "toWord64 = toWord word32"),
        ("core", "copair = elimS iden", "copair = elimS unit"),
        ("core", "elimS r s t = r &&& unit", "elimS r s t = unit &&& r"),
    ]
    for key, old, new in tail_mutations:
        if old not in s[key]:
            raise ValueError("inactive buffer/finalizer mutation: " + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            buffer_finalize(changed)
        except ValueError:
            continue
        raise ValueError("buffer/finalizer source mutation escaped: " + old)
    print("SHA buffer-add/finalizer Core trees, padding and word dependencies match;", len(tail_mutations), "mutations rejected")
    tag_mutations = [
        ("hs", 'tagIv $ fromString "TapData"', 'tagIv $ fromString "TapLeaf"'),
        ("digest", "compress noTagIv (tagDigest, tagDigest)", "compress noTagIv (tagDigest, hash0)"),
        ("digest", "tagDigest = bsHash . BSC.pack $ tag", "tagDigest = bsHash . BSC.pack $ reverse tag"),
        ("digest", "bslHash = ivHash . IV . pushChunks sha256Incremental . padSHA1", "bslHash = ivHash . IV . pushChunks sha256Incremental"),
        ("pure", "maj x y z = (x .&. (y .|. z)) .|. (y .&. z)", "maj x y z = (x .&. (y .|. z)) `xor` (y .&. z)"),
        ("pure", "bsig256_0 x = rotateR x 2", "bsig256_0 x = rotateR x 3"),
        ("pure", "h' = g", "h' = f"),
        ("pure", "(a00 + a64)", "(a00 + b64)"),
        ("pure", "putWord32be h", "putWord32be g"),
        ("pure", "padSHA1 = generic_pad 448 512 64", "padSHA1 = generic_pad 448 512 32"),
        ("pure", "len * 8", "len * 7"),
        ("host", "tap_host_tag_digest ++ tap_host_tag_digest", "tap_host_tag_bytes ++ tap_host_tag_digest"),
        ("host", "(seq 16 48)", "(seq 16 47)"),
        ("host", "[24;16;8;0]", "[0;8;16;24]"),
        ("host", 'str_to_bytes "TapData"', 'str_to_bytes "tapdata"'),
        ("tap_port", "@left_pad_low_spec term 0 6", "@left_pad_low_spec term 0 5"),
        ("tap_port", "Alg.scribe tap_host_prefix", "Alg.scribe tapdata_prefix"),
        ("tap_jet", "sha_globals_ok m /\\ sha_tag_ok m", "sha_globals_ok m"),
        ("tap_jet", "memcpy_model ->", "False -> memcpy_model ->"),
    ]
    pure_rounds = re.findall(r"step256 s\d\d (0x[0-9a-f]+) w\d\d", s["pure"])
    tag_mutations += [("pure", k, hex(int(k, 16) ^ 1)) for k in pure_rounds]
    tag_mutations += [("pure", f"w{j:02} = lsig256_1 w{j-2:02}", f"w{j:02} = lsig256_1 w{j-1:02}") for j in range(16,64)]
    for key, old, new in tag_mutations:
        if old not in s[key]:
            raise ValueError("inactive TapData mutation: " + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            tapdata(changed)
        except ValueError:
            continue
        raise ValueError("TapData source mutation escaped: " + old)
    print("TapData fixed host recipe and complete canonical/C boundary match;", len(tag_mutations), "mutations rejected")


if __name__ == "__main__":
    test()
