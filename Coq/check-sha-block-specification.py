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


def bitcoin_taproot(s):
    """Whole Core trees, fixed tag recipes and unchanged original-C boundaries."""
    def definition(key, name, expected):
        if p.compact(p.definition(s[key], name)) != p.compact(expected):
            raise ValueError("Bitcoin taproot dependency differs: " + name)

    def replace(text, old, new):
        return re.sub(r"\s*".join(re.escape(c) for c in p.compact(old)), lambda _: new, text)

    def binding(key, lhs, expected):
        if p.compact(hbody(s[key], lhs)) != p.compact(expected):
            raise ValueError("Bitcoin library binding differs: " + lhs)

    p.require(s["bitcoin_catalog"], "import qualified Simplicity.Programs.Bitcoin.Lib as Prog", "actual Bitcoin library import")
    p.require(s["bitcoin_catalog"], "import Simplicity.Programs.Sha256.Lib (Ctx8)", "actual Bitcoin context import")
    p.require(s["bitcoin_lib"], "import qualified Simplicity.Programs.Bitcoin as Bitcoin", "Bitcoin library wrapper import")
    for name, instance in [("buildTapleafSimplicity", "lib"), ("buildTapbranch", "lib"),
                           ("outpointHash", "libAssert"), ("annexHash", "libAssert")]:
        binding("bitcoin_lib", name, f"Bitcoin.{name} Bitcoin.{instance}")
    binding("bitcoin_prog", "lib", "mkLib Sha256.lib")
    binding("bitcoin_prog", "libAssert", "mkLibAssert Sha256.lib Sha256.libAssert LibSecp256k1.lib")
    p.require(s["hs"], "type Hash = Word256", "Bitcoin hash carrier")
    # The SHA word operations, all rounds, padding and binary serialization
    # are checked by tapdata(s). The hash/word converter also has its existing
    # shared source gate and general Coq haskell_hash_word256 theorem.
    for name, expected in {
        "literal_short_tag_bytes": "map (fun b => Int.repr (Byte.unsigned b)) (SHA256.str_to_bytes tag)",
        "literal_short_tag_state": "tap_host_compress tap_host_iv (literal_short_tag_bytes tag ++ tap_host_pad (Z.of_nat (String.length tag)))",
        "literal_short_tag_digest": "flat_map tap_host_put32 (tap_host_state_words (literal_short_tag_state tag))",
        "literal_short_tag_prefix_state": "tap_host_compress tap_host_iv (literal_short_tag_digest tag ++ literal_short_tag_digest tag)",
        "literal_short_tag_prefix": "haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist (tap_host_hash (literal_short_tag_prefix_state tag))))",
    }.items():
        definition("bt_port", name, expected)
    for label in ["TapLeaf", "TapBranch"]:
        prefix = "tapleafPrefix" if label == "TapLeaf" else "tapbranchPrefix"
        binding("bitcoin_prog", prefix, 'scribe . toWord256 . integerHash256 . ivHash . tagIv $ fromString "' + label + '"')
    binding("bitcoin_prog", "simplicityVersion", "scribe . toWord8 $ 0xbe")
    for size in [8, 16, 32, 64, 128, 256, 512]:
        p.require(s["hs_types"], f"toWord{size} = toWord word{size}", "Bitcoin constant converter")
        p.require(s["hs_types"], f"word{size} = vector{size}", "Bitcoin word witness")
        p.require(s["hs_types"], f"type Word{size} = Vector{size} Bit", "Bitcoin word carrier")
        p.require(s["hs_types"], f"vector{size} = DoubleV vector{size//2}", "Bitcoin balanced vector")
    for line in [
        "full_shift wa wb = go (compareVectorSize wb wa)",
        "go (Left v) = full_right_shift1 (vectorComp vector2 v)",
        "go (Right (Left Refl)) = iden",
        "go (Right (Right v)) = full_left_shift1 (vectorComp vector2 v)",
    ]:
        p.require(s["hs_word"], line, "Bitcoin full_shift direction")
    # In compareVectorSize word256 word16 the first four double/double
    # steps promote, then four double/single steps choose Left. Composition
    # with vector2 therefore gives sixteen Word16s (Coq depth 4).
    p.require(s["hs_types"], '''compareVectorSize SingleV SingleV = Right (Left Refl)
      compareVectorSize (DoubleV n) SingleV =
        case compareVectorSize n SingleV of
          Left v -> Left (DoubleV v)
          Right (Left Refl) -> Left SingleV
      compareVectorSize SingleV (DoubleV m) =
        case compareVectorSize SingleV m of
          Right (Left Refl) -> Right (Right SingleV)
          Right (Right v) -> Right (Right (DoubleV v))
      compareVectorSize (DoubleV n) (DoubleV m) =
        case compareVectorSize n m of
          Left v -> Left (vectorPromote v)
          Right (Left Refl) -> Right (Left Refl)
          Right (Right v) -> Right (Right (vectorPromote v))''', "Bitcoin relative vector size")
    p.require(s["hs_types"], "vectorComp v SingleV = v", "vector composition base")
    p.require(s["hs_types"], "vectorComp v (DoubleV w) = DoubleV (vectorComp v w)", "vector composition step")
    p.require(s["hs_types"], "vectorPromote SingleV = SingleV", "vector promotion base")
    p.require(s["hs_types"], "vectorPromote (DoubleV v) = DoubleV (vectorPromote v)", "vector promotion step")
    body = s["bitcoin_prog"].split("mkLib Sha256.Lib{..} = lib", 1)[1].split("} where", 1)[0]
    leaf = re.search(r"buildTapleafSimplicity\s*=(.*?)\n\s*,\s*buildTapbranch", body, re.S)
    branch = re.search(r"\bbuildTapbranch\s*=(.*)", body, re.S)
    if not leaf or not branch:
        raise ValueError("missing Bitcoin canonical builder tree")
    for name, hs_body in [("literal_build_tapleaf", leaf[1]), ("literal_build_tapbranch", branch[1])]:
        port = p.definition(s["bt_port"], name)
        port = replace(port, "@literal_build_tapleaf_block term", "(" + p.definition(s["bt_port"], "literal_build_tapleaf_block") + ")")
        for old, new in [
            ('Alg.scribe (literal_short_tag_prefix "TapLeaf"%string)', "tapleafPrefix"),
            ('Alg.scribe (literal_short_tag_prefix "TapBranch"%string)', "tapbranchPrefix"),
            ("@literal_sha_256_block term", "hashBlock"),
            ("@Word.full_right_shift1 (Word 4) 4 term", "full_shift word16 word256"),
            ("@Word.zero 5 term", "zero word32"), ("@Word.zero 6 term", "zero word64"),
            ("@lt_word_spec term 8", "lt word256"),
            ("Alg.scribe (haskell_to_word 3 0xbe)", "simplicityVersion"),
            ("Alg.scribe (haskell_to_word 3 32)", "scribe (toWord8 32)"),
            ("Alg.scribe (haskell_to_word 4 0x8000)", "scribe (toWord16 32768)"),
            ("Alg.scribe (haskell_to_word 7 (512+16+256))", "length128"),
            ("Alg.scribe (haskell_to_word 9 (2^511+1024))", "pad512"),
            ("Bit.cond", "cond"),
        ]:
            port = replace(port, old, new)
        hs_body = replace(hs_body, "scribe (toWord16 0x8000)", "scribe (toWord16 32768)")
        hs_body = replace(hs_body, "scribe (toWord128 (512+16+256))", "length128")
        hs_body = replace(hs_body, "scribe (toWord512 $ 2^511 + 1024)", "pad512")
        same(hs_body, port, "Bitcoin " + name)
    for tag, stem, f_name, input_type, program in [
        ("BuildTapleafSimplicity", "tapleaf", "build_tapleaf_simplicity", "Word256", "literal_build_tapleaf"),
        ("BuildTapbranch", "tapbranch", "build_tapbranch", "(Word256, Word256)", "literal_build_tapbranch"),
    ]:
        target = "buildTapleafSimplicity" if stem == "tapleaf" else "buildTapbranch"
        p.require(s["bitcoin_catalog"], f"{tag} :: SigHashJet {input_type} Word256", "Bitcoin builder type")
        binding("bitcoin_catalog", f"specificationSigHash {tag}", f"Prog.{target}")
        definition(stem + "_c", "sha_" + stem + "_pre", "sha_globals_ok m /\\ sha_" + stem + "_tag_ok m")
        in_depth = 8 if stem == "tapleaf" else 9
        for suffix in ["local", "startup"]:
            contract = "sha_jet_local_spec_pre sha_" + stem + "_pre" if suffix == "local" else "sha_startup_total_spec"
            statement = re.search(r"Theorem bitcoin_build_" + stem + "_literal_" + suffix + r"_spec\s*:(.*?)\bProof\.", s["bt_jet"], re.S)
            expected = f"memcpy_model -> {contract} f_simplicity_bitcoin_{f_name} (Word {in_depth}) (Word 8) (@{program} Alg.CoreFunSem)."
            if not statement or p.compact(statement[1]) != p.compact(expected):
                raise ValueError("Bitcoin builder complete public contract differs")


def bitcoin_context_hash(s):
    def replace(text, old, new):
        return re.sub(r"\s*".join(re.escape(c) for c in p.compact(old)), lambda _: new, text)

    body = s["bitcoin_prog"].split("mkLibAssert Sha256.Lib{..}", 1)[1]
    outpoint = re.search(r"\boutpointHash\s*=(.*?)\n\s*,\s*annexHash", body, re.S)
    annex = re.search(r"\bannexHash\s*=(.*?)\n\s*,\s*buildTaptweak", body, re.S)
    if not outpoint or not annex:
        raise ValueError("missing Bitcoin context hash tree")
    p.require(s["hs_ty"], "type S a = Either () a", "Bitcoin annex sum carrier")
    for size in [4, 32]:
        p.require(body, f"ctx8Add{size} = ctx8Addn vector{size}", "Bitcoin context-add width binding")
    for tag, stem, hs_body, input_type, coq_type in [
        ("OutpointHash", "outpoint", outpoint[1], "(Ctx8, (Word256, Word32))", "(Ty.Prod sha256_ctx8_type (Ty.Prod (Word 8) (Word 5)))"),
        ("AnnexHash", "annex", annex[1], "(Ctx8, S Word256)", "(Ty.Prod sha256_ctx8_type (Ty.Sum Ty.Unit (Word 8)))"),
    ]:
        program = "literal_bitcoin_" + stem + "_hash"
        p.require(s["bitcoin_catalog"], f"{tag} :: SigHashJet {input_type} Ctx8", "Bitcoin context hash type")
        p.require(s["bitcoin_catalog"], f"specificationSigHash {tag} = Prog.{stem}Hash", "Bitcoin context hash catalog")
        port = p.definition(s["bctx_port"], program)
        for old, new in [
            ("@literal_ctx8_addn 5 term", "ctx8Add32"),
            ("@literal_ctx8_addn 2 term", "ctx8Add4"),
            ("@literal_ctx8_add1 term", "ctx8Add1"),
            ("@Word.zero 3 (Alg.Assertion.toCore term)", "zero word8"),
            ("Alg.scribe (haskell_to_word 3 0x01)", "scribe (toWord8 1)"),
        ]:
            port = replace(port, old, new)
        hs_body = replace(hs_body, "scribe (toWord8 0x01)", "scribe (toWord8 1)")
        same(hs_body, port, "Bitcoin " + stem + " context hash")
        for suffix in ["local", "startup"]:
            contract = "sha_jet_partial_local_spec" if suffix == "local" else "sha_startup_partial_spec"
            theorem = f"bitcoin_{stem}_hash_literal_{suffix}_spec"
            statement = re.search(r"Theorem " + theorem + r"\s*:(.*?)\bProof\.", s["bctx_jet"], re.S)
            expected = f"memcpy_model -> {contract} f_simplicity_bitcoin_{stem}_hash {coq_type} sha256_ctx8_type (@{program} optalg)."
            if not statement or p.compact(statement[1]) != p.compact(expected):
                raise ValueError("Bitcoin context hash complete public contract differs")


def primitive_hash_words(s):
    """Canonical array traversal and the existing Tappath primitive interface."""
    def definition(key, name, expected):
        if p.compact(p.definition(s[key], name)) != p.compact(expected):
            raise ValueError("primitive SHA dependency differs: " + name)

    def binding(key, lhs, expected):
        if p.compact(hbody(s[key], lhs)) != p.compact(expected):
            raise ValueError("primitive SHA binding differs: " + lhs)

    def replace(text, old, new):
        return re.sub(r"\s*".join(re.escape(c) for c in p.compact(old)), lambda _: new, text)

    p.require(s["bitcoin_catalog"], "import qualified Simplicity.Bitcoin.Programs.SigHash.Lib as SigHash", "SigHash catalog import")
    p.require(s["bitcoin_catalog"], "TappathHash :: SigHashJet () Word256", "TappathHash catalog type")
    binding("bitcoin_catalog", "specificationSigHash TappathHash", "SigHash.tappathHash")
    p.require(s["sighash_lib"], "import qualified Simplicity.Bitcoin.Programs.SigHash as SigHash", "SigHash wrapper import")
    binding("sighash_lib", "tappathHash", "SigHash.tappathHash SigHash.lib")
    binding("sighash", "lib", "mkLib Sha256.lib Sha256.libAssert Transaction.lib")
    body = s["sighash"].split("mkLib Sha256.Lib{..} Sha256.LibAssert{..} Transaction.Lib{..} = lib", 1)[1]
    selected = re.search(r"\btappathHash\s*=(.*?)\n\s*,\s*tapEnvHash", body, re.S)
    if not selected:
        raise ValueError("missing canonical tappathHash")
    same(selected[1], "hashWord256s8 (drop (primitive Tappath))", "tappath primitive routing")
    binding("sighash", "hashWord256s8", "hashWord256s word8")
    binding("sighash", "hashLoop256", "Sha256.hashLoop vector32")
    port = p.definition(s["hash_words_port"], "literal_sha_hash_words")
    for old, new in [
        ("@literal_sha_hash_ctx_init (Alg.Assertion.toCore term)", "ctx8Init"),
        ("@literal_sha_hash_loop k w term C array", "hashLoop256 w array"),
        ("@literal_ctx8_finalize term", "ctx8Finalize"),
    ]:
        port = replace(port, old, new)
    same(hbody(s["sighash"], "hashWord256s w array"), port, "hashWord256s composition")
    loop = hbody(s["hs"], "hashLoop v")
    parts = re.fullmatch(r"\s*\\w\s+array\s*->\s*let\s+body\s*=(.*?)\bin\b(.*)", loop, re.S)
    if not parts:
        raise ValueError("canonical hashLoop binding differs")
    binding("hs", "ctx8Addv", "ctx8Addn libAssert v")
    port_body = replace(p.definition(s["hash_words_port"], "literal_sha_hash_loop_body"),
                        "@literal_ctx8_addn k term", "ctx8Addv")
    same(parts[1], port_body, "hashLoop body and stop/continue branches")
    port_loop = replace(p.definition(s["hash_words_port"], "literal_sha_hash_loop"),
        "@for_while_program w C sha256_ctx8_type sha256_ctx8_type (Alg.Assertion.toCore term) (@literal_sha_hash_loop_body k term C (Word w) array)",
        "forWhile w body")
    same(parts[2], port_loop, "hashLoop completion")
    definition("forwhile", "for_while_program", '''match n as k return alg ((C * Word k) * A) (B + A) -> alg (C * A) (B + A) with
      | 0 => fun body =>
          ((((O H &&& Bit.false) &&& I H) >>> body) &&& O H) >>>
            case (injl (O H)) (((I H &&& Bit.true) &&& O H) >>> body)
      | S k => fun body => for_while_program k (for_while_program k
          (((O O O H &&& (O O I H &&& O I H)) &&& I H) >>> body)) end body''')
    same(hbody(s["hs_word"], "forWhile SingleV body").replace("monobody", "body"), '''
      ((((oh &&& false) &&& ih) >>> body) &&& oh) >>>
      match (injl oh) (((ih &&& true) &&& oh) >>> body)''', "forWhile base")
    binding("hs_word", "monobody", "body")
    same(hbody(s["hs_word"], "forWhile (DoubleV n) body"),
         "forWhile n (forWhile n ((oooh &&& (ooih &&& oih)) &&& ih >>> body))", "forWhile nesting")
    # Literal initializer, including the host toWord conversion. Its general
    # Coq equality composes the already-proved converter, not a new assumption.
    sha_lib = s["hs"].split("lib = l", 1)[1]
    iv = re.search(r"\biv\s*=(.*?)\n\s*,\s*hashBlock", sha_lib, re.S)
    init = re.search(r"\bctx8Init\s*=(.*?)\n\s*,\s*tapdataInit", sha_lib, re.S)
    value = "0x6a09e667bb67ae853c6ef372a54ff53a510e527f9b05688c1f83d9ab5be0cd19"
    if not iv or p.compact(iv[1]) != p.compact("scribe . toWord256 $ " + value):
        raise ValueError("canonical SHA initializer IV differs")
    if not init:
        raise ValueError("missing canonical context initializer")
    definition("hash_words_port", "literal_sha_hash_ctx_init", '''
      @buffer_empty_spec (Word 3) 5 Ty.Unit term &&&
      (@Word.zero 6 term &&& Alg.scribe (haskell_to_word 8 ''' + value + "))")
    same(init[1], "buffer63Empty &&& (zero word64 &&& iv)", "context initializer")
    p.require(s["hs"], "buffer63Empty = bufferEmpty buffer63", "initializer buffer alias")
    p.require(s["hs_types"], "word8 = vector8", "8-bit counter")
    p.require(s["hs_types"], "vector8 = DoubleV vector4", "8-bit counter vector")
    p.require(s["hs_types"], "vector32 = DoubleV vector16", "32-byte array element")
    definition("tappath_port", "literal_bitcoin_tappath_hash", '''
      let term := PF.CanonicalStructures.toAssertion alg in
      @literal_sha_hash_words 5 3 term Ty.Unit
        (@Alg.Core.Combinators.drop Ty.Unit (Word 3) (Ty.Sum Ty.Unit (Vector (Word 3) 5))
          (Alg.Assertion.toCore term) (@PF.Combinators.prim _ _ alg (BitcoinFull.Ext BitcoinExt.Tappath)))''')
    # Retain the existing formal primitive, its names and interpretation.
    # The host interpretation is source-reviewed; no general Haskell
    # interpreter theorem is claimed by this checker.
    p.require(s["btc_primitive"], "Tappath :: Prim Word8 (S Word256)", "Tappath primitive type")
    binding("btc_primitive", "primName Tappath", '"tappath"')
    binding("btc_primitive", "interpret Tappath", "return . cast . fmap encodeHash . listToMaybe . flip drop (tappath (envTap env)) . fromInteger . fromWord8")
    binding("btc_primitive", "cast (Just x)", "Right x")
    binding("btc_primitive", "cast Nothing", "Left ()")
    binding("btc_primitive", "encodeHash", "toWord256 . integerHash256")
    binding("hs_types", "fromWord8", "fromWord word8")
    p.require(s["ext_primitive"], '| Tappath => "tappath"', "formal Tappath identity")
    p.require(s["ext_primitive"], '''| Tappath => fun i =>
      Some (cast (option_map (fun h => from_hash256 h) (nth_error (extTappath e) (Z.to_nat (toZ i)))))
      | InternalKey''', "formal Tappath interpreter")
    p.require(s["ext_primitive"], "extTappath_len : (length extTappath <= 128)%nat", "unchanged formal path domain")
    p.require(s["btc_env_c"], "if (128 < rawEnv->pathLen) return NULL;", "C builder path bound")
    statement = re.search(r"Theorem bitcoin_tappath_hash_literal_local_spec\s*:(.*?)\bProof\.", s["tappath_port"], re.S)
    expected = '''application_jet_local_spec_sep f_simplicity_bitcoin_tappath_hash bitcoin_ge ext_environment
      Ty.Unit Word256 (hash_getter_rep (fun e => words_hash_of 5 3 (tappath_of e)) 8 40 176)
      (fun a environment => @literal_bitcoin_tappath_hash fullalg a environment).'''
    if not statement or p.compact(statement[1]) != p.compact(expected):
        raise ValueError("TappathHash complete C contract differs")


def bitcoin_array_hashes(s):
    """Check literal specializations, selected primitive projections and full
    cached-getter contracts. Caller cache construction is not certified here.
    Shared SHA traversal is checked separately by primitive_hash_words.
    """
    def binding(key, lhs, expected):
        if p.compact(hbody(s[key], lhs)) != p.compact(expected):
            raise ValueError("Bitcoin array hash binding differs: " + lhs)

    def definition(name, expected):
        if p.compact(p.definition(s["array_port"], name)) != p.compact(expected):
            raise ValueError("Bitcoin array hash program differs: " + name)

    body = s["sighash"].split("mkLib Sha256.Lib{..} Sha256.LibAssert{..} Transaction.Lib{..} = lib", 1)[1]
    binding("sighash", "hashWord256s32", "hashWord256s word32")
    binding("sighash", "hashWord32s array", '''iden &&& (unit >>> ctx8Init)
      >>> Sha256.hashLoop vector4 word32 array >>> ctx8Finalize''')
    for lhs, rhs in [("word32", "vector32"), ("vector4", "DoubleV vector2"),
                     ("vector2", "DoubleV vector1"), ("vector1", "SingleV")]:
        binding("hs_types", lhs, rhs)
    definition("literal_bitcoin_array_hash", '''
      let term := PF.CanonicalStructures.toAssertion alg in
      @literal_sha_hash_words k 5 term Ty.Unit
        (@Alg.Core.Combinators.drop Ty.Unit (Word 5) (Ty.Sum Ty.Unit (Vector (Word 3) k))
          (Alg.Assertion.toCore term) (@PF.Combinators.prim _ _ alg p))''')
    cases = [
        ("OutputScriptsHash", "outputScriptsHash", "output_scripts", "OutputScriptHash", "Base Bitcoin", 5, 48),
        ("InputScriptsHash", "inputScriptsHash", "input_scripts", "InputScriptHash", "Ext BitcoinExt", 5, 176),
        ("InputSequencesHash", "inputSequencesHash", "input_sequences", "InputSequence", "Base Bitcoin", 2, 240),
        ("InputScriptSigsHash", "inputScriptSigsHash", "input_script_sigs", "InputScriptSigHash", "Ext BitcoinExt", 5, 304),
    ]
    for tag, hs_name, stem, prim, signature, k, offset in cases:
        p.require(s["bitcoin_catalog"], f"{tag} :: SigHashJet () Word256", "array hash catalog type")
        binding("bitcoin_catalog", "specificationSigHash " + tag, "SigHash." + hs_name)
        binding("sighash_lib", hs_name, "SigHash." + hs_name + " SigHash.lib")
        selected = re.search(r"\b" + hs_name + r"\s*=(.*?)\n\s*[,}]", body, re.S)
        if not selected:
            raise ValueError("missing canonical array hash: " + hs_name)
        helper = "hashWord32s" if k == 2 else "hashWord256s32"
        same(selected[1], f"{helper} (drop (primitive {prim}))", hs_name + " primitive routing")
        program = "literal_bitcoin_" + stem + "_hash"
        definition(program, f"@literal_bitcoin_array_hash {k} (BitcoinFull.{signature}.{prim}) alg")
        statement = re.search(r"Theorem bitcoin_" + stem + r"_hash_literal_local_spec\s*:(.*?)\bProof\.",
                              s["array_port"], re.S)
        expected = f'''application_jet_local_spec_sep f_simplicity_bitcoin_{stem}_hash bitcoin_ge ext_environment
          Ty.Unit Word256 (hash_getter_rep (fun e => words_hash_of {k} 5 ({stem}_of e)) 0 {offset} 432)
          (fun a environment => @{program} fullalg a environment).'''
        if not statement or p.compact(statement[1]) != p.compact(expected):
            raise ValueError("array hash complete C contract differs: " + stem)
    # These are source-reviewed projections, not a general interpreter proof.
    for lhs, rhs in {
        "lookupInput": "(sigTxIn tx !?) . fromIntegral",
        "lookupOutput": "(sigTxOut tx !?) . fromIntegral",
        "atInput f": "cast . fmap f . lookupInput . fromInteger . fromWord32",
        "atOutput f": "cast . fmap f . lookupOutput . fromInteger . fromWord32",
        "interpret InputSequence": "return . (atInput $ toWord32 . toInteger . sigTxiSequence)",
        "interpret OutputScriptHash": "return . (atOutput $ encodeHash . bslHash . txoScript)",
        "interpret InputScriptHash": "return . (atInput $ encodeHash . bslHash . sigTxiScript)",
        "interpret InputScriptSigHash": "return . (atInput $ encodeHash . bslHash . sigTxiScriptSig)",
    }.items():
        binding("btc_primitive", lhs, rhs)
    p.require(s["base_primitive"], '''| InputSequence => atInput (fun txi => fromZ (Int.unsigned (sigTxiSequence txi)))''', "formal sequence projection")
    p.require(s["base_primitive"], '''| OutputScriptHash => atOutput (fun txout => from_hash256 (byteStringHash (txoScript txout)))''', "formal output script projection")
    for prim, field in [("InputScriptHash", "extInScriptHash"), ("InputScriptSigHash", "extInScriptSigHash")]:
        p.require(s["ext_primitive"], f'''| {prim} => fun i =>
          Some (cast (option_map (fun h => from_hash256 h) (nth_error ({field} e) (Z.to_nat (toZ i)))))''', "formal script projection")
    p.require(s["full_primitive"], "| Base q => fun a => Bitcoin.sem q a (extBase e)", "base primitive dispatch")
    p.require(s["full_primitive"], "| Ext q => fun a => BitcoinExt.sem q a e", "extended primitive dispatch")


def bitcoin_raw_hashes(s):
    """Keep raw interpretation, its represented-memory boundary and all five
    complete C conclusions explicit. This does not prove caller cache creation.
    """
    for key, name, expected in [
        ("raw_program", "raw_full_sem", '''
          (match p in BitcoinFull.prim A B return Ty.tySem A -> option (Ty.tySem B) with
           | BitcoinFull.Base q => fun a => Bitcoin.sem q a (raw_base environment)
           | BitcoinFull.Ext q => fun a => raw_ext_sem q a environment end) a'''),
        ("raw_program", "raw_fullalg", '''
          @PF._Pack (fun A B => Ty.tySem A -> raw_bitcoin_environment -> option (Ty.tySem B))
            (@PF.Class _
              (Alg.Assertion.class_of (Alg.AssertionSem (ReaderT_CIMonadZero raw_bitcoin_environment option_Monad_Zero)))
              (@PF.Mixin _ (@raw_full_sem)))'''),
        ("raw_program", "raw_program_relation", '''forall a environment Hpath,
          f a (project_raw_environment environment Hpath) = g a environment'''),
        ("raw_jets", "raw_env_rep", '''exists Hpath : (length (raw_tap_path logical) <= 128)%nat,
          rep m env (project_raw_environment logical Hpath) fp'''),
    ]:
        if p.compact(p.definition(s[key], name)) != p.compact(expected):
            raise ValueError("raw program/representation differs: " + name)
    p.require(s["raw_env"], "raw_base : Bitcoin.environment", "unchanged raw base domain")
    for prim, field, script in [
        ("InputScriptHash", "extInScriptHash", "raw_redeemed_script"),
        ("InputScriptSigHash", "extInScriptSigHash", "raw_script_sig"),
    ]:
        p.require(s["raw_env"], f'''{field} := map (fun i => byteStringHash ({script} i)) (raw_inputs environment)''', "raw script projection")
        p.require(s["raw_env"], f'''| BitcoinExt.{prim} => fun i =>
          Some (cast (option_map (fun data => from_hash256 (byteStringHash ({script} data)))
            (nth_error (raw_inputs environment) (Z.to_nat (toZ i)))))''', "raw script primitive")
    p.require(s["raw_env"], '''| BitcoinExt.Tappath => fun i =>
      Some (cast (option_map from_hash256 (nth_error (raw_tap_path environment) (Z.to_nat (toZ i)))))''', "raw path primitive")
    for stem, k, w, ptr, offset, size in [
        ("output_scripts", 5, 5, 0, 48, 432),
        ("input_scripts", 5, 5, 0, 176, 432),
        ("input_sequences", 2, 5, 0, 240, 432),
        ("input_script_sigs", 5, 5, 0, 304, 432),
        ("tappath", 5, 3, 8, 40, 176),
    ]:
        statement = re.search(r"Theorem bitcoin_" + stem + r"_hash_raw_literal_local_spec\s*:(.*?)\bProof\.", s["raw_hash"], re.S)
        expected = f'''application_jet_local_spec_sep f_simplicity_bitcoin_{stem}_hash bitcoin_ge raw_bitcoin_environment
          Ty.Unit Word256
          (raw_env_rep (hash_getter_rep (fun e => words_hash_of {k} {w} ({stem}_of e)) {ptr} {offset} {size}))
          (fun a environment => @literal_bitcoin_{stem}_hash raw_fullalg a environment).'''
        if not statement or p.compact(statement[1]) != p.compact(expected):
            raise ValueError("raw literal whole C contract differs: " + stem)


def bitcoin_tap_environment(s):
    """Compare actual canonical trees with the explicit algebra applications;
    the reused fixed-tag recipe and SHA subtrees are checked separately.
    """
    def replace(text, old, new):
        return re.sub(r"\s*".join(re.escape(c) for c in p.compact(old)), lambda _: new, text)

    def binding(key, lhs, expected):
        if p.compact(hbody(s[key], lhs)) != p.compact(expected):
            raise ValueError("tap environment binding differs: " + lhs)

    binding("hs", "prefix", "scribe . toWord256 . integerHash256 . ivHash . tagIv $ tag")
    init = p.definition(s["tap_hash_port"], "literal_sha_tag_ctx")
    for old, new in [
        ("@buffer_empty_spec (Word 3) 5 Ty.Unit term", "buffer63Empty"),
        ("@literal_tapdata_one64 term", "one word64"), ("Alg.scribe prefix", "prefix"),
    ]:
        init = replace(init, old, new)
    same(hbody(s["hs"], "ctx8InitTag tag"), init, "tagged context initializer")
    aliases = [
        ('@literal_sha_tag_ctx (literal_short_tag_prefix "TapLeaf"%string) core', "tagInit"),
        ("@literal_sha_hash_ctx_init core", "ctx8Init"),
        ("@literal_bitcoin_tapleaf_hash alg", "tapleafHash"),
        ("@literal_bitcoin_tappath_hash alg", "tappathHash"),
        ("@PF.Combinators.prim _ _ alg (BitcoinFull.Ext BitcoinExt.TapleafVersion)", "primVersion"),
        ("@PF.Combinators.prim _ _ alg (BitcoinFull.Base Bitcoin.ScriptCMR)", "primCMR"),
        ("@PF.Combinators.prim _ _ alg (BitcoinFull.Ext BitcoinExt.InternalKey)", "primKey"),
        ("@Alg.scribe Ty.Unit (Word 3) (haskell_to_word 3 32) core", "leafSize"),
        ("@literal_ctx8_addn 1 term", "add2"), ("@literal_ctx8_addn 5 term", "add32"),
        ("@literal_ctx8_addn 6 term", "add64"), ("@literal_ctx8_finalize term", "ctx8Finalize"),
    ]
    atoms = {new for _, new in aliases}

    def explicit_tree(node):
        if node[0] == "name" and node[1] in atoms:
            return node
        if (node[0] == "app" and node[1][0] == "app"
                and node[1][1] in [("name", "compNode"), ("name", "pairNode")]):
            op = "comp" if node[1][1][1] == "compNode" else "pair"
            return (op, explicit_tree(node[1][2]), explicit_tree(node[2]))
        raise ValueError("unsupported explicit tap-hash algebra tree")

    body = s["sighash"].split("mkLib Sha256.Lib{..} Sha256.LibAssert{..} Transaction.Lib{..} = lib", 1)[1]
    for tag, hs_name, stem, offset in [
        ("TapleafHash", "tapleafHash", "tapleaf", 8), ("TapEnvHash", "tapEnvHash", "tap_env", 72),
    ]:
        p.require(s["bitcoin_catalog"], f"{tag} :: SigHashJet () Word256", "tap environment catalog type")
        binding("bitcoin_catalog", "specificationSigHash " + tag, "SigHash." + hs_name)
        binding("sighash_lib", hs_name, "SigHash." + hs_name + " SigHash.lib")
        hs = re.search(r"\b" + hs_name + r"\s*=(.*?)\n\s*[,}]", body, re.S)
        if not hs:
            raise ValueError("missing canonical tap environment program")
        hs = hs[1]
        for old, new in [
            ('Sha256.ctx8InitTag "TapLeaf"', "tagInit"),
            ("primitive TapleafVersion", "primVersion"), ("primitive ScriptCMR", "primCMR"),
            ("primitive InternalKey", "primKey"), ("scribe (toWord8 32)", "leafSize"),
            ("ctx8Addn vector2", "add2"), ("ctx8Addn vector32", "add32"),
            ("ctx8Addn vector64", "add64"),
        ]:
            hs = replace(hs, old, new)
        program = "literal_bitcoin_" + stem + "_hash"
        coq = p.definition(s["tap_hash_port"], program)
        matched = re.fullmatch(r"\s*let term := PF\.CanonicalStructures\.toAssertion alg in\s*"
                               r"let core := Alg\.Assertion\.toCore term in\s*(.*)", coq, re.S)
        if not matched:
            raise ValueError("tap program algebra binding differs")
        coq = matched[1]
        for old, new in aliases + [("@AC.comp _ _ _ core", "compNode"), ("@AC.pair _ _ _ core", "pairNode")]:
            coq = replace(coq, old, new)
        if expression(hs) != explicit_tree(expression(coq)):
            raise ValueError("canonical tap environment Core tree differs: " + stem)
        for suffix, env, pre, alg in [
            ("literal_local", "ext_environment", f"(hash_getter_rep {stem}_hash_of 8 {offset} 176)", "fullalg"),
            ("raw_literal_local", "raw_bitcoin_environment", f"(raw_env_rep (hash_getter_rep {stem}_hash_of 8 {offset} 176))", "raw_fullalg"),
        ]:
            statement = re.search(r"Theorem bitcoin_" + stem + "_hash_" + suffix + r"_spec\s*:(.*?)\bProof\.", s["tap_hash_port"], re.S)
            expected = f'''application_jet_local_spec_sep f_simplicity_bitcoin_{stem}_hash bitcoin_ge {env}
              Ty.Unit Word256 {pre} (fun a environment => @{program} {alg} a environment).'''
            if not statement or p.compact(statement[1]) != p.compact(expected):
                raise ValueError("tap environment complete C contract differs")
    for lhs, expected in {
        "interpret TapleafVersion": "element . return . toWord8 . toInteger . tapleafVersion $ envTap env",
        "interpret ScriptCMR": "element . return . toWord256 . integerHash256 . tapScriptCMR $ envTap env",
        "interpret InternalKey": "element . return . encodeKey . tapInternalKey $ envTap env",
        "encodeKey (Schnorr.PubKey x)": "toWord256 . toInteger $ x",
    }.items():
        binding("btc_primitive", lhs, expected)
    p.require(s["base_primitive"], "| ScriptCMR => fun _ => Some (from_hash256 (envScriptCMR e))", "formal CMR primitive")
    p.require(s["ext_primitive"], "| TapleafVersion => fun _ => Some (fromZ (extTapleafVersion e))", "formal leaf version")
    p.require(s["ext_primitive"], "| InternalKey => fun _ => Some (from_hash256 (extInternalKey e))", "formal internal key")
    p.require(s["raw_env"], "| BitcoinExt.TapleafVersion => fun _ => Some (fromZ (Byte.unsigned (raw_leaf_version environment)))", "raw leaf version")
    p.require(s["raw_env"], "| BitcoinExt.InternalKey => fun _ => Some (from_hash256 (raw_internal_key environment))", "raw internal key")
    p.require(s["raw_env"], "extTapleafVersion := Byte.unsigned (raw_leaf_version environment)", "projected leaf version")
    p.require(s["raw_env"], "extInternalKey := raw_internal_key environment", "projected internal key")


def bitcoin_input_hashes(s):
    """Canonical loop trees, nested annex absence and complete cached C getters.
    Shared SHA and context append trees are checked by the existing gates.
    """
    def replace(text, old, new):
        return re.sub(r"\s*".join(re.escape(c) for c in p.compact(old)), lambda _: new, text)

    def binding(key, lhs, expected):
        if p.compact(hbody(s[key], lhs)) != p.compact(expected):
            raise ValueError('input hash binding differs: ' + lhs)

    def definition(key, name, expected):
        if p.compact(p.definition(s[key], name)) != p.compact(expected):
            raise ValueError('input hash definition differs: ' + name)

    def explicit_tree(node):
        if node == ('iden',):
            return node
        if node[0] == 'name' and node[1] in {
            'array', 'add', 'iden', 'ctx8Init', 'outpoints', 'sequences', 'annexes', 'add64', 'add32', 'ctx8Finalize'
        }:
            return node
        if node[0] == 'app' and node[1][0] == 'name':
            op = node[1][1]
            if op in {'takeNode', 'dropNode'}:
                return ('take' if op == 'takeNode' else 'drop', explicit_tree(node[2]))
            if op in {'injlNode', 'injrNode'}:
                return ('app', ('name', op[:-4]), explicit_tree(node[2]))
        if node[0] == 'app' and node[1][0] == 'app' and node[1][1][0] == 'name':
            op = node[1][1][1]
            left, right = explicit_tree(node[1][2]), explicit_tree(node[2])
            if op in {'compNode', 'pairNode'}:
                return ('comp' if op == 'compNode' else 'pair', left, right)
            if op == 'caseNode':
                return ('app', ('app', ('name', 'case'), left), right)
        raise ValueError('unsupported explicit input hash tree')

    core_aliases = [
        ('@AC.comp _ _ _ core', 'compNode'), ('@AC.pair _ _ _ core', 'pairNode'),
        ('@AC.take _ _ _ core', 'takeNode'), ('@AC.drop _ _ _ core', 'dropNode'),
        ('@AC.case _ _ _ _ core', 'caseNode'), ('@AC.injl _ _ _ core', 'injlNode'),
        ('@AC.injr _ _ _ core', 'injrNode'), ('@AC.iden _ core', 'iden'),
    ]
    body = p.definition(s['elems_loop'], 'gen_loop_body')
    prefix = 'let core := Alg.Assertion.toCore term in'
    if not body.lstrip().startswith(prefix):
        raise ValueError('element loop algebra differs')
    body = body.lstrip()[len(prefix):]
    for old, new in [('add term', 'add')] + core_aliases:
        body = replace(body, old, new)
    body_tree = explicit_tree(expression(body))
    definition('inputs_port', 'literal_bitcoin_elems_hash', '''
      let term := PF.CanonicalStructures.toAssertion alg in
      let core := Alg.Assertion.toCore term in
      @AC.comp _ _ _ core
        (@AC.pair _ _ _ core (@AC.unit _ core) (@literal_sha_hash_ctx_init core))
        (@AC.comp _ _ _ core
          (@for_while_program w Ty.Unit sha256_ctx8_type sha256_ctx8_type core
            (@gen_loop_body X add term Ty.Unit (Word w)
              (@AC.drop Ty.Unit (Word w) _ core (@PF.Combinators.prim _ _ alg p))))
          (@AC.copair _ _ _ core (@literal_ctx8_finalize term) (@literal_ctx8_finalize term)))''')
    hs = s['sighash'].split('mkLib Sha256.Lib{..} Sha256.LibAssert{..} Transaction.Lib{..} = lib', 1)[1]
    cases = [
        ('InputOutpointsHash', 'inputOutpointsHash', 'input_outpoints', 'InputPrevOutpoint',
         'Ty.Prod (Word 8) (Word 5)', 'outpoint', 'Base Bitcoin', 112),
        ('InputAnnexesHash', 'inputAnnexesHash', 'input_annexes', 'InputAnnexHash',
         'Ty.Sum Ty.Unit (Word 8)', 'annex', 'Ext BitcoinExt', 272),
        ('InputsHash', 'inputsHash', 'inputs', None, None, None, None, 336),
    ]
    for tag, hs_name, stem, primitive, ty, adder, signature, offset in cases:
        p.require(s['bitcoin_catalog'], f'{tag} :: SigHashJet () Word256', 'input hash catalog type')
        binding('bitcoin_catalog', 'specificationSigHash ' + tag, 'SigHash.' + hs_name)
        binding('sighash_lib', hs_name, 'SigHash.' + hs_name + ' SigHash.lib')
        selected = re.search(r'\b' + hs_name + r'\s*=(.*?)\n\s*[,}]', hs, re.S)
        if not selected:
            raise ValueError('missing canonical input hash')
        if primitive:
            parts = re.fullmatch(r'\s*let\s+finalize\s*=\s*ctx8Finalize\s+body\s*=(.*?)\bin\b(.*)', selected[1], re.S)
            if not parts:
                raise ValueError('input hash let bindings differ')
            hs_body = replace(parts[1], f'drop (primitive {primitive})', 'array')
            hs_body = replace(hs_body, adder + 'Hash', 'add')
            if expression(hs_body) != body_tree:
                raise ValueError('input hash loop stop/continue tree differs')
            same(parts[2], 'unit &&& ctx8Init >>> forWhile word32 body >>> copair finalize finalize', 'input hash traversal')
            definition('inputs_port', 'literal_bitcoin_' + stem + '_hash', f'''
              @literal_bitcoin_elems_hash ({ty})
                (fun term => @literal_bitcoin_{adder}_hash term) 5
                (BitcoinFull.{signature}.{primitive}) alg''')
        else:
            port = p.definition(s['inputs_port'], 'literal_bitcoin_inputs_hash')
            prefix = 'let term := PF.CanonicalStructures.toAssertion alg in'
            prefix2 = 'let core := Alg.Assertion.toCore term in'
            if not port.lstrip().startswith(prefix):
                raise ValueError('inputs hash primitive algebra differs')
            port = port.lstrip()[len(prefix):].lstrip()
            if not port.startswith(prefix2):
                raise ValueError('inputs hash Core algebra differs')
            port = port[len(prefix2):]
            aliases = [
                ('@literal_sha_hash_ctx_init core', 'ctx8Init'),
                ('@literal_bitcoin_input_outpoints_hash alg', 'outpoints'),
                ('@literal_bitcoin_input_sequences_hash alg', 'sequences'),
                ('@literal_bitcoin_input_annexes_hash alg', 'annexes'),
                ('@literal_ctx8_addn 6 term', 'add64'), ('@literal_ctx8_addn 5 term', 'add32'),
                ('@literal_ctx8_finalize term', 'ctx8Finalize'),
            ]
            for old, new in aliases + core_aliases:
                port = replace(port, old, new)
            hs_port = selected[1]
            for old, new in [('inputOutpointsHash', 'outpoints'), ('inputSequencesHash', 'sequences'),
                             ('inputAnnexesHash', 'annexes'), ('ctx8Addn vector64', 'add64'), ('ctx8Addn vector32', 'add32')]:
                hs_port = replace(hs_port, old, new)
            if expression(hs_port) != explicit_tree(expression(port)):
                raise ValueError('canonical inputs hash composition differs')
        for suffix, env, rep, alg in [
            ('literal_local', 'ext_environment', f'(hash_getter_rep {stem}_hash_of 0 {offset} 432)', 'fullalg'),
            ('raw_literal_local', 'raw_bitcoin_environment', f'(raw_env_rep (hash_getter_rep {stem}_hash_of 0 {offset} 432))', 'raw_fullalg'),
        ]:
            statement = re.search(r'Theorem bitcoin_' + stem + '_hash_' + suffix + r'_spec\s*:(.*?)\bProof\.', s['inputs_port'], re.S)
            expected = f'''application_jet_local_spec_sep f_simplicity_bitcoin_{stem}_hash bitcoin_ge {env}
              Ty.Unit Word256 {rep}
              (fun a environment => @literal_bitcoin_{stem}_hash {alg} a environment).'''
            if not statement or p.compact(statement[1]) != p.compact(expected):
                raise ValueError('input hash complete C contract differs')
    binding('btc_primitive', 'interpret InputPrevOutpoint', 'return . (atInput $ encodeOutpoint . sigTxiPreviousOutpoint)')
    binding('btc_primitive', 'interpret InputAnnexHash', 'return . (atInput $ cast . fmap (encodeHash . bslHash) . sigTxiAnnex)')
    p.require(s['base_primitive'], '| InputPrevOutpoint => atInput (fun txi => encodeOutpoint (sigTxiPreviousOutpoint txi))', 'formal outpoint projection')
    p.require(s['ext_primitive'], '''| InputAnnexHash => fun i =>
      Some (match nth_error (extInAnnexHash e) (Z.to_nat (toZ i)) with
            | None => inl tt
            | Some None => inr (inl tt)
            | Some (Some h) => inr (inr (from_hash256 h)) end)''', 'formal nested annex absence')
    p.require(s['raw_env'], '''extInAnnexHash := map (fun i => option_map byteStringHash (raw_annex i)) (raw_inputs environment)''', 'raw annex projection')
    p.require(s['raw_env'], '''| BitcoinExt.InputAnnexHash => fun i =>
      Some (match nth_error (raw_inputs environment) (Z.to_nat (toZ i)) with
            | None => inl tt
            | Some data => inr (cast (option_map (fun bytes => from_hash256 (byteStringHash bytes)) (raw_annex data)))
            end)''', 'raw nested annex absence')


def bitcoin_single_input_hash(s):
    """Canonical optional single-input tree and both complete computing C contracts.
    The C memory relation still includes SHA readiness; memcpy stays explicit.
    """
    def replace(text, old, new):
        return re.sub(r'\s*'.join(re.escape(c) for c in p.compact(old)), lambda _: new, text)

    def binding(key, lhs, expected):
        if p.compact(hbody(s[key], lhs)) != p.compact(expected):
            raise ValueError('single-input binding differs: ' + lhs)

    p.require(s['bitcoin_catalog'], 'InputHash :: SigHashJet Word32 (S Word256)', 'single-input catalog type')
    binding('bitcoin_catalog', 'specificationSigHash InputHash', 'SigHash.inputHash')
    binding('sighash_lib', 'inputHash', 'SigHash.inputHash SigHash.lib')
    binding('sighash', 'ctx8Add4', 'ctx8Addn vector4')
    assertion = p.definition(s['single_input_port'], 'literal_bitcoin_assert_iden')
    assertion = replace(assertion,
        '@Alg.Assertion.Combinators.assertr Ty.Unit B Ty.Unit B term assertion_cmr_fail0', 'assertr cmrFail0')
    same(hbody(s['hs_bit'], 'assert t').replace('t &&&', 'iden &&&'), assertion, 'single-input assertions')
    hs = s['sighash'].split('mkLib Sha256.Lib{..} Sha256.LibAssert{..} Transaction.Lib{..} = lib', 1)[1]
    selected = re.search(r'\binputHash\s*=(.*?)\n\s*[,}]', hs, re.S)
    if not selected:
        raise ValueError('missing canonical single-input program')
    hs = selected[1]
    for old, new in [
        ('primitive InputPrevOutpoint', 'outpointPrim'), ('primitive InputSequence', 'seqPrim'),
        ('primitive InputAnnexHash', 'annexPrim'),
        ('(drop . take . assert $ iden)', 'drop (take assertSeq)'),
        ('(drop . drop . assert $ iden)', 'drop (drop assertAnnex)'),
    ]:
        hs = replace(hs, old, new)
    port = p.definition(s['single_input_port'], 'literal_bitcoin_input_hash')
    prefix = 'let term := PF.CanonicalStructures.toAssertion alg in'
    prefix2 = 'let core := Alg.Assertion.toCore term in'
    if not port.lstrip().startswith(prefix):
        raise ValueError('single-input primitive algebra differs')
    port = port.lstrip()[len(prefix):].lstrip()
    if not port.startswith(prefix2):
        raise ValueError('single-input Core algebra differs')
    port = port[len(prefix2):]
    aliases = [
        ('@PF.Combinators.prim _ _ alg (BitcoinFull.Base Bitcoin.InputPrevOutpoint)', 'outpointPrim'),
        ('@PF.Combinators.prim _ _ alg (BitcoinFull.Base Bitcoin.InputSequence)', 'seqPrim'),
        ('@PF.Combinators.prim _ _ alg (BitcoinFull.Ext BitcoinExt.InputAnnexHash)', 'annexPrim'),
        ('@literal_sha_hash_ctx_init core', 'ctx8Init'),
        ('@literal_bitcoin_outpoint_hash term', 'outpointHash'),
        ('@literal_bitcoin_annex_hash term', 'annexHash'),
        ('@literal_bitcoin_assert_iden (Word 5) term', 'assertSeq'),
        ('@literal_bitcoin_assert_iden (Ty.Sum Ty.Unit (Word 8)) term', 'assertAnnex'),
        ('@literal_ctx8_addn 2 term', 'ctx8Add4'), ('@literal_ctx8_finalize term', 'ctx8Finalize'),
        ('@AC.comp _ _ _ core', 'compNode'), ('@AC.pair _ _ _ core', 'pairNode'),
        ('@AC.case _ _ _ _ core', 'caseNode'), ('@AC.injl _ _ _ core', 'injlNode'),
        ('@AC.injr _ _ _ core', 'injrNode'), ('@AC.take _ _ _ core', 'takeNode'),
        ('@AC.drop _ _ _ core', 'dropNode'), ('@AC.unit _ core', 'unit'), ('@AC.iden _ core', 'iden'),
    ]
    atoms = {new for _, new in aliases if not new.endswith('Node')}
    for old, new in aliases:
        port = replace(port, old, new)

    def explicit_tree(node):
        if node == ('iden',) or (node[0] == 'name' and node[1] in atoms):
            return node
        if node[0] == 'app' and node[1][0] == 'name':
            op = node[1][1]
            if op in {'takeNode', 'dropNode'}:
                return ('take' if op == 'takeNode' else 'drop', explicit_tree(node[2]))
            if op in {'injlNode', 'injrNode'}:
                return ('app', ('name', op[:-4]), explicit_tree(node[2]))
        if node[0] == 'app' and node[1][0] == 'app' and node[1][1][0] == 'name':
            op = node[1][1][1]
            left, right = explicit_tree(node[1][2]), explicit_tree(node[2])
            if op in {'compNode', 'pairNode'}:
                return ('comp' if op == 'compNode' else 'pair', left, right)
            if op == 'caseNode':
                return ('app', ('app', ('name', 'case'), left), right)
        raise ValueError('unsupported explicit single-input hash tree')

    if expression(hs) != explicit_tree(expression(port)):
        raise ValueError('canonical single-input hash Core tree differs')
    for suffix, env, rep, alg in [
        ('literal_local', 'ext_environment', 'input_hash_rep', 'fullalg'),
        ('raw_literal_local', 'raw_bitcoin_environment', '(raw_env_rep input_hash_rep)', 'raw_fullalg'),
    ]:
        statement = re.search(r'Theorem bitcoin_input_hash_' + suffix + r'_spec\s*:(.*?)\bProof\.', s['single_input_port'], re.S)
        expected = f'''memcpy_model ->
          application_jet_local_spec_sep f_simplicity_bitcoin_input_hash sha_ge {env}
            (Word 5) (Ty.Sum Ty.Unit (Word 8)) {rep}
            (fun a environment => @literal_bitcoin_input_hash {alg} a environment).'''
        if not statement or p.compact(statement[1]) != p.compact(expected):
            raise ValueError('single-input whole C contract differs')


def elements_array_hashes(s):
    """Seven raw-data primitive streams; shared SHA trees have existing gates.
    Complete getter contracts retain caller cache/frame representations.
    """
    def binding(key, lhs, expected):
        if p.compact(hbody(s[key], lhs)) != p.compact(expected):
            raise ValueError('Elements array binding differs: ' + lhs)

    def definition(name, expected):
        if p.compact(p.definition(s['elements_array_port'], name)) != p.compact(expected):
            raise ValueError('Elements array program differs: ' + name)

    p.require(s['elements_catalog'], 'import qualified Simplicity.Elements.Programs.SigHash.Lib as SigHash', 'Elements SigHash catalog import')
    p.require(s['elements_sighash_lib'], 'import qualified Simplicity.Elements.Programs.SigHash as SigHash', 'Elements SigHash wrapper import')
    p.require(s['elements_sighash'], 'import qualified Simplicity.Programs.Sha256 as Sha256', 'shared SHA library')
    binding('elements_sighash', 'lib', 'mkLib Sha256.lib Sha256.libAssert Transaction.lib')
    for lhs, expected in [
        ('hashWord256s w array', 'iden &&& (unit >>> ctx8Init) >>> hashLoop256 w array >>> ctx8Finalize'),
        ('hashWord256s32', 'hashWord256s word32'), ('hashWord256s8', 'hashWord256s word8'),
        ('hashLoop256', 'Sha256.hashLoop vector32'),
        ('hashWord32s array', 'iden &&& (unit >>> ctx8Init) >>> Sha256.hashLoop vector4 word32 array >>> ctx8Finalize'),
    ]:
        binding('elements_sighash', lhs, expected)
    definition('literal_elements_array_hash', '''
      let term := EFP.CanonicalStructures.toAssertion alg in
      @literal_sha_hash_words k w term Ty.Unit
        (@AC.drop Ty.Unit (Word w) (Ty.Sum Ty.Unit (Vector (Word 3) k))
          (Alg.Assertion.toCore term) (@EFP.Combinators.prim _ _ alg p))''')
    body = s['elements_sighash'].split('mkLib Sha256.Lib{..} Sha256.LibAssert{..} Transaction.Lib{..} = lib', 1)[1]
    cases = [
        ('OutputScriptsHash', 'outputScriptsHash', 'output_scripts', 'OutputScriptHash', 5, 5, 0, 88, 760),
        ('OutputRangeProofsHash', 'outputRangeProofsHash', 'output_range_proofs', 'OutputRangeProof', 5, 5, 0, 120, 760),
        ('OutputSurjectionProofsHash', 'outputSurjectionProofsHash', 'output_surjection_proofs', 'OutputSurjectionProof', 5, 5, 0, 152, 760),
        ('InputScriptsHash', 'inputScriptsHash', 'input_scripts', 'InputScriptHash', 5, 5, 0, 280, 760),
        ('InputSequencesHash', 'inputSequencesHash', 'input_sequences', 'InputSequence', 2, 5, 0, 344, 760),
        ('InputScriptSigsHash', 'inputScriptSigsHash', 'input_script_sigs', 'InputScriptSigHash', 5, 5, 0, 408, 760),
        ('TappathHash', 'tappathHash', 'tappath', 'Tappath', 5, 3, 8, 40, 176),
    ]
    for tag, hs_name, stem, primitive, k, w, ptr, offset, size in cases:
        p.require(s['elements_catalog'], f'{tag} :: SigHashJet () Word256', 'Elements array catalog type')
        binding('elements_catalog', 'specificationSigHash ' + tag, 'SigHash.' + hs_name)
        binding('elements_sighash_lib', hs_name, 'SigHash.' + hs_name + ' SigHash.lib')
        selected = re.search(r'\b' + hs_name + r'\s*=(.*?)\n\s*[,}]', body, re.S)
        helper = 'hashWord32s' if k == 2 else ('hashWord256s8' if w == 3 else 'hashWord256s32')
        if not selected:
            raise ValueError('missing Elements array hash program')
        same(selected[1], f'{helper} (drop (primitive {primitive}))', 'Elements array routing')
        program = 'literal_elements_' + stem + '_hash'
        definition(program, f'@literal_elements_array_hash {k} {w} Elements.{primitive} alg')
        statement = re.search(r'Theorem elements_' + stem + r'_hash_literal_local_spec\s*:(.*?)\bProof\.', s['elements_array_port'], re.S)
        expected = f'''application_jet_local_spec_sep f_simplicity_{stem}_hash elements_ge Elements.env Ty.Unit Word256
          (hash_getter_rep (fun e => elements_words_hash_of {k} {w} (elements_{stem}_words e)) {ptr} {offset} {size})
          (fun a environment => @{program} elements_hash_alg a environment).'''
        if not statement or p.compact(statement[1]) != p.compact(expected):
            raise ValueError('Elements array complete C contract differs')
    for lhs, rhs in {
        'lookupInput': '(sigTxIn tx !?) . fromIntegral',
        'lookupOutput': '(sigTxOut tx !?) . fromIntegral',
        'atInput f': 'cast . fmap f . lookupInput . fromInteger . fromWord32',
        'atOutput f': 'cast . fmap f . lookupOutput . fromInteger . fromWord32',
        'cast (Just x)': 'Right x', 'cast Nothing': 'Left ()',
        'encodeHash': 'toWord256 . integerHash256',
        'interpret OutputScriptHash': 'return . (atOutput $ encodeHash . bslHash . txoScript)',
        'interpret OutputRangeProof': 'return . (atOutput $ encodeHash . bslHash . view (to txoAmount.under amount.prf_))',
        'interpret OutputSurjectionProof': 'return . (atOutput $ encodeHash . bslHash . view (to txoAsset.under asset.prf_))',
        'interpret InputScriptHash': 'return . (atInput $ encodeHash . bslHash . utxoScript . sigTxiTxo)',
        'interpret InputSequence': 'return . (atInput $ toWord32 . toInteger . sigTxiSequence)',
        'interpret InputScriptSigHash': 'return . (atInput $ encodeHash . bslHash . sigTxiScriptSig)',
        'interpret Tappath': 'return . cast . fmap encodeHash . listToMaybe . flip drop (tappath (envTap env)) . fromInteger . fromWord8',
    }.items():
        binding('elements_primitive_hs', lhs, rhs)
    for expected in [
        '| OutputScriptHash => atOutput (fun txo => encodeHash (byteStringHash (txoScript txo)))',
        '| OutputRangeProof => atOutput (fun txo => encodeHash (byteStringHash (viewPrf (txoAmount txo))))',
        '| OutputSurjectionProof => atOutput (fun txo => encodeHash (byteStringHash (viewPrf (txoAsset txo))))',
        '| InputScriptHash => atInput (fun txi => encodeHash (byteStringHash (utxoScript (sigTxiTxo txi))))',
        '| InputSequence => atInput (fun txi => fromZ (Int.unsigned (sigTxiSequence txi)))',
        '| InputScriptSigHash => atInput (fun txi => encodeHash (byteStringHash (sigTxiScriptSig txi)))',
        '| Tappath => fun i : Word8 => Some (cast (option_map encodeHash (nth_error (tappath (envTap e)) (Z.to_nat (toZ i)))))',
    ]:
        p.require(s['elements_primitive_coq'], expected, 'Elements array primitive interpretation')
    if p.compact(p.definition(s['elements_primitive_coq'], 'viewPrf')) != p.compact('''match c with
      | Explicit _ => [] | Confidential _ p => p end'''):
        raise ValueError('Elements explicit/confidential proof view differs')


def explicit_core_tree(node, atoms):
    """Typed Coq Core applications after exact, context-specific aliases."""
    if node == ('iden',) or (node[0] == 'name' and node[1] in atoms):
        return node
    if node[0] == 'app' and node[1][0] == 'name':
        op = node[1][1]
        if op in {'takeNode', 'dropNode'}:
            return ('take' if op == 'takeNode' else 'drop', explicit_core_tree(node[2], atoms))
        if op in {'injlNode', 'injrNode'}:
            return ('app', ('name', op[:-4]), explicit_core_tree(node[2], atoms))
    if node[0] == 'app' and node[1][0] == 'app' and node[1][1][0] == 'name':
        op = node[1][1][1]
        left, right = explicit_core_tree(node[1][2], atoms), explicit_core_tree(node[2], atoms)
        if op in {'compNode', 'pairNode'}:
            return ('comp' if op == 'compNode' else 'pair', left, right)
        if op in {'caseNode', 'copairNode'}:
            return ('app', ('app', ('name', 'case' if op == 'caseNode' else 'copair'), left), right)
    raise ValueError('unsupported explicit Core tree')


def elements_input_hashes(s):
    """Two-lookup outpoint loop, nested annex loop and complete C getters.
    Shared SHA, literal annex and primitive-array trees have existing gates.
    """
    def replace(text, old, new):
        return re.sub(r'\s*'.join(re.escape(c) for c in p.compact(old)), lambda _: new, text)

    def binding(key, lhs, expected):
        if p.compact(hbody(s[key], lhs)) != p.compact(expected):
            raise ValueError('Elements input binding differs: ' + lhs)

    def definition(name, expected):
        if p.compact(p.definition(s['elements_inputs_port'], name)) != p.compact(expected):
            raise ValueError('Elements input program differs: ' + name)

    p.require(s['elements_sighash'], 'import Simplicity.Programs.Elements.Lib', 'Elements context library import')
    p.require(s['elements_prog_lib'], 'import qualified Simplicity.Programs.Elements as Elements', 'Elements context wrapper import')
    binding('elements_prog', 'libAssert', 'mkLibAssert Sha256.lib Sha256.libAssert LibSecp256k1.lib')
    for name in ['outpointHash', 'annexHash']:
        binding('elements_prog_lib', name, f'Elements.{name} Elements.libAssert')
    contexts = s['elements_prog'].split('mkLibAssert Sha256.Lib{..} Sha256.LibAssert{..} LibSecp256k1.Lib{..} = libAssert', 1)[1]
    hs_add = re.search(r'\boutpointHash\s*=(.*?)\n\s*,\s*assetAmountHash', contexts, re.S)
    hs_annex = re.search(r'\bannexHash\s*=(.*?)\n\s*,\s*buildTaptweak', contexts, re.S)
    if not hs_add or not hs_annex:
        raise ValueError('missing Elements context program')
    add = p.definition(s['elements_inputs_port'], 'literal_elements_outpoint_add')
    for old, new in [('@literal_bitcoin_annex_hash term', 'annexHash'),
                     ('@literal_ctx8_addn 5 term', 'ctx8Add32'), ('@literal_ctx8_addn 2 term', 'ctx8Add4')]:
        add = replace(add, old, new)
    same(hs_add[1], add, 'Elements pegin/outpoint absorber')
    annex = p.definition(s['bctx_port'], 'literal_bitcoin_annex_hash')
    for old, new in [('@Word.zero 3 (Alg.Assertion.toCore term)', 'zero8'),
                     ('Alg.scribe (haskell_to_word 3 0x01)', 'byteOne'),
                     ('@literal_ctx8_add1 term', 'ctx8Add1'), ('@literal_ctx8_addn 5 term', 'ctx8Add32')]:
        annex = replace(annex, old, new)
    hs_annex = replace(replace(hs_annex[1], 'zero word8', 'zero8'), 'scribe (toWord8 0x01)', 'byteOne')
    same(hs_annex, annex, 'Elements shared literal annex program')
    p.require(contexts, 'ctx8Add4 = ctx8Addn vector4', 'Elements outpoint index width')
    p.require(contexts, 'ctx8Add32 = ctx8Addn vector32', 'Elements outpoint digest width')

    ops = [('@AC.comp _ _ _ core', 'compNode'), ('@AC.pair _ _ _ core', 'pairNode'),
           ('@AC.case _ _ _ _ core', 'caseNode'), ('@AC.copair _ _ _ core', 'copairNode'),
           ('@AC.injl _ _ _ core', 'injlNode'), ('@AC.injr _ _ _ core', 'injrNode'),
           ('@AC.take _ _ _ core', 'takeNode'), ('@AC.drop _ _ _ core', 'dropNode'),
           ('@AC.unit _ core', 'unit'), ('@AC.iden _ core', 'iden'),
           ('AC.drop', 'dropNode'), ('AC.take', 'takeNode'), ('AC.iden', 'iden')]
    atoms = {'pPegin', 'pOutpoint', 'outpointHash', 'annexHash', 'array', 'unit',
             'ctx8Init', 'ctx8Finalize', 'loop', 'outpoints', 'sequences', 'annexes', 'add64', 'add32'}

    def tree(text, aliases, prefix=True):
        if prefix:
            header = re.fullmatch(r'\s*let term := EFP\.CanonicalStructures\.toAssertion alg in\s*'
                                  r'let core := Alg\.Assertion\.toCore term in\s*(.*)', text, re.S)
            if not header:
                raise ValueError('Elements input algebra binding differs')
            text = header[1]
        for old, new in aliases + ops:
            text = replace(text, old, new)
        return explicit_core_tree(expression(text), atoms)

    definition('literal_elements_elems_hash', '''let core := Alg.Assertion.toCore term in
      @AC.comp _ _ _ core
        (@AC.pair _ _ _ core (@AC.unit _ core) (@literal_sha_hash_ctx_init core))
        (@AC.comp _ _ _ core
          (@for_while_program w Ty.Unit sha256_ctx8_type sha256_ctx8_type core
            (@gen_loop_body X add term Ty.Unit (Word w) array))
          (@AC.copair _ _ _ core (@literal_ctx8_finalize term) (@literal_ctx8_finalize term)))''')
    definition('literal_elements_input_annexes_hash', '''
      let term := EFP.CanonicalStructures.toAssertion alg in let core := Alg.Assertion.toCore term in
      @literal_elements_elems_hash (Ty.Sum Ty.Unit Word256)
        (fun term => @literal_bitcoin_annex_hash term) 5 term
        (@AC.drop Ty.Unit Word32 _ core (@EFP.Combinators.prim _ _ alg Elements.InputAnnexHash))''')
    hs_programs = s['elements_sighash'].split('mkLib Sha256.Lib{..} Sha256.LibAssert{..} Transaction.Lib{..} = lib', 1)[1]
    for tag, hs_name, stem, offset in [
        ('InputOutpointsHash', 'inputOutpointsHash', 'input_outpoints', 216),
        ('InputAnnexesHash', 'inputAnnexesHash', 'input_annexes', 376),
        ('InputsHash', 'inputsHash', 'inputs', 440),
    ]:
        p.require(s['elements_catalog'], f'{tag} :: SigHashJet () Word256', 'Elements input catalog type')
        binding('elements_catalog', 'specificationSigHash ' + tag, 'SigHash.' + hs_name)
        binding('elements_sighash_lib', hs_name, 'SigHash.' + hs_name + ' SigHash.lib')
        selected = re.search(r'\b' + hs_name + r'\s*=(.*?)\n\s*[,}]', hs_programs, re.S)
        if not selected:
            raise ValueError('missing Elements input hash')
        if stem != 'inputs':
            parts = re.fullmatch(r'\s*let\s+finalize\s*=\s*ctx8Finalize\s+body\s*=(.*?)\bin\b(.*)', selected[1], re.S)
            if not parts:
                raise ValueError('Elements input loop bindings differ')
            if stem == 'input_outpoints':
                hs_body = replace(replace(parts[1], 'primitive InputPegin', 'pPegin'), 'primitive InputPrevOutpoint', 'pOutpoint')
                aliases = [('@EFP.Combinators.prim _ _ alg Elements.InputPegin', 'pPegin'),
                           ('@EFP.Combinators.prim _ _ alg Elements.InputPrevOutpoint', 'pOutpoint'),
                           ('@AC.drop Ty.Unit Word32 _ core', 'dropNode'),
                           ('@literal_elements_outpoint_add term', 'outpointHash')]
                actual = tree(p.definition(s['elements_inputs_port'], 'literal_elements_outpoints_body'), aliases)
                if expression(hs_body) != actual:
                    raise ValueError('Elements outpoint loop two-lookup/early-exit tree differs')
                program = p.definition(s['elements_inputs_port'], 'literal_elements_input_outpoints_hash')
                aliases = [('@literal_sha_hash_ctx_init core', 'ctx8Init'),
                           ('@for_while_program 5 _ _ _ core (@literal_elements_outpoints_body alg)', 'loop'),
                           ('@literal_ctx8_finalize term', 'ctx8Finalize')]
                expected = replace(replace(parts[2], 'forWhile word32 body', 'loop'), 'finalize', 'ctx8Finalize')
                if expression(expected) != tree(program, aliases):
                    raise ValueError('Elements outpoint whole traversal differs')
            else:
                hs_body = replace(parts[1], 'drop (primitive InputAnnexHash)', 'array')
                body = p.definition(s['elems_loop'], 'gen_loop_body')
                prefix = 'let core := Alg.Assertion.toCore term in'
                if not body.lstrip().startswith(prefix):
                    raise ValueError('element loop algebra differs')
                if expression(hs_body) != tree(body.lstrip()[len(prefix):], [('add term', 'annexHash')], prefix=False):
                    raise ValueError('Elements annex stop/continue body differs')
                same(parts[2], 'unit &&& ctx8Init >>> forWhile word32 body >>> copair finalize finalize', 'Elements annex traversal')
        else:
            aliases = [('@literal_sha_hash_ctx_init core', 'ctx8Init'),
                       ('@literal_elements_input_outpoints_hash alg', 'outpoints'),
                       ('@literal_elements_input_sequences_hash alg', 'sequences'),
                       ('@literal_elements_input_annexes_hash alg', 'annexes'),
                       ('@literal_ctx8_addn 6 term', 'add64'), ('@literal_ctx8_addn 5 term', 'add32'),
                       ('@literal_ctx8_finalize term', 'ctx8Finalize')]
            hs_body = selected[1]
            for old, new in [('inputOutpointsHash', 'outpoints'), ('inputSequencesHash', 'sequences'),
                             ('inputAnnexesHash', 'annexes'), ('ctx8Addn vector64', 'add64'), ('ctx8Addn vector32', 'add32')]:
                hs_body = replace(hs_body, old, new)
            if expression(hs_body) != tree(p.definition(s['elements_inputs_port'], 'literal_elements_inputs_hash'), aliases):
                raise ValueError('Elements inputs hash composition differs')
        statement = re.search(r'Theorem elements_' + stem + r'_hash_literal_local_spec\s*:(.*?)\bProof\.', s['elements_inputs_port'], re.S)
        expected = f'''application_jet_local_spec_sep f_simplicity_{stem}_hash elements_ge Elements.env Ty.Unit Word256
          (hash_getter_rep elements_{stem}_hash_of 0 {offset} 760)
          (fun a environment => @literal_elements_{stem}_hash elements_hash_alg a environment).'''
        if not statement or p.compact(statement[1]) != p.compact(expected):
            raise ValueError('Elements input whole C contract differs')
    binding('elements_primitive_hs', 'interpret InputPegin', 'return . (atInput $ cast . fmap encodeHash . sigTxiPegin)')
    binding('elements_primitive_hs', 'interpret InputPrevOutpoint', 'return . (atInput $ encodeOutpoint . sigTxiPreviousOutpoint)')
    binding('elements_primitive_hs', 'encodeOutpoint op', '(encodeHash $ opHash op, toWord32 . fromIntegral $ opIndex op)')
    binding('elements_primitive_hs', 'interpret InputAnnexHash', 'return . (atInput $ cast . fmap (encodeHash . bslHash) . sigTxiAnnex)')
    for expected in [
        '| InputPegin => atInput (fun txi => cast (option_map encodeHash (sigTxiPegin txi)))',
        '| InputPrevOutpoint => atInput (fun txi => encodeOutpoint (sigTxiPreviousOutpoint txi))',
        '| InputAnnexHash => atInput (fun txi => cast (option_map (fun x => encodeHash (byteStringHash x)) (sigTxiAnnex txi)))',
    ]:
        p.require(s['elements_primitive_coq'], expected, 'Elements optional primitive interpretation')


def elements_tap_hashes(s):
    """Fixed Elements tag, full tapleaf/tapEnv trees and native key boundary.
    This does not establish caller cache construction or host-runtime fidelity.
    """
    def replace(text, old, new):
        return re.sub(r'\s*'.join(re.escape(c) for c in p.compact(old)), lambda _: new, text)

    def binding(key, lhs, expected):
        if p.compact(hbody(s[key], lhs)) != p.compact(expected):
            raise ValueError('Elements tap binding differs: ' + lhs)

    aliases = [
        ('@literal_sha_tag_ctx (literal_short_tag_prefix "TapLeaf/elements"%string) core', 'tagInit'),
        ('@literal_sha_hash_ctx_init core', 'ctx8Init'),
        ('@literal_elements_tapleaf_hash alg', 'tapleafHash'),
        ('@literal_elements_tappath_hash alg', 'tappathHash'),
        ('@EFP.Combinators.prim _ _ alg Elements.TapleafVersion', 'primVersion'),
        ('@EFP.Combinators.prim _ _ alg Elements.ScriptCMR', 'primCMR'),
        ('@EFP.Combinators.prim _ _ alg Elements.InternalKey', 'primKey'),
        ('@Alg.scribe Ty.Unit Word8 (haskell_to_word 3 32) core', 'leafSize'),
        ('@literal_ctx8_addn 1 term', 'add2'), ('@literal_ctx8_addn 5 term', 'add32'),
        ('@literal_ctx8_addn 6 term', 'add64'), ('@literal_ctx8_finalize term', 'ctx8Finalize'),
    ]
    atoms = {new for _, new in aliases}
    hs_programs = s['elements_sighash'].split('mkLib Sha256.Lib{..} Sha256.LibAssert{..} Transaction.Lib{..} = lib', 1)[1]
    for tag, hs_name, stem, offset in [
        ('TapleafHash', 'tapleafHash', 'tapleaf', 8), ('TapEnvHash', 'tapEnvHash', 'tap_env', 72),
    ]:
        p.require(s['elements_catalog'], f'{tag} :: SigHashJet () Word256', 'Elements tap catalog type')
        binding('elements_catalog', 'specificationSigHash ' + tag, 'SigHash.' + hs_name)
        binding('elements_sighash_lib', hs_name, 'SigHash.' + hs_name + ' SigHash.lib')
        hs = re.search(r'\b' + hs_name + r'\s*=(.*?)\n\s*[,}]', hs_programs, re.S)
        if not hs:
            raise ValueError('missing canonical Elements tap program')
        hs = hs[1]
        program = 'literal_elements_' + stem + '_hash'
        port = p.definition(s['elements_tap_port'], program)
        # Whitespace is significant INSIDE a tag. Do this before aliases that
        # intentionally ignore formatting between Core expression tokens.
        expected_strings = ['"TapLeaf/elements"'] if stem == 'tapleaf' else []
        for text in [hs, port]:
            if re.findall(r'"(?:\\.|[^"\\])*"', text) != expected_strings:
                raise ValueError('Elements tap tag literal differs')
        header = re.fullmatch(r'\s*let term := EFP\.CanonicalStructures\.toAssertion alg in\s*'
                              r'let core := Alg\.Assertion\.toCore term in\s*(.*)', port, re.S)
        if not header:
            raise ValueError('Elements tap algebra binding differs')
        port = header[1]
        for old, new in aliases + [('@AC.comp _ _ _ core', 'compNode'), ('@AC.pair _ _ _ core', 'pairNode')]:
            port = replace(port, old, new)
        for old, new in [
            ('Sha256.ctx8InitTag "TapLeaf/elements"', 'tagInit'),
            ('primitive TapleafVersion', 'primVersion'), ('primitive ScriptCMR', 'primCMR'),
            ('primitive InternalKey', 'primKey'), ('scribe (toWord8 32)', 'leafSize'),
            ('ctx8Addn vector2', 'add2'), ('ctx8Addn vector32', 'add32'), ('ctx8Addn vector64', 'add64'),
        ]:
            hs = replace(hs, old, new)
        if expression(hs) != explicit_core_tree(expression(port), atoms):
            raise ValueError('canonical Elements tap Core tree differs')
        statement = re.search(r'Theorem elements_' + stem + r'_hash_literal_local_spec\s*:(.*?)\bProof\.', s['elements_tap_port'], re.S)
        expected = f'''application_jet_local_spec_sep f_simplicity_{stem}_hash elements_ge Elements.env Ty.Unit Word256
          (hash_getter_rep elements_{stem}_hash_of 8 {offset} 176)
          (fun a environment => @{program} elements_hash_alg a environment).'''
        if not statement or p.compact(statement[1]) != p.compact(expected):
            raise ValueError('Elements tap whole C contract differs')
    for lhs, rhs in {
        'interpret TapleafVersion': 'element . return . toWord8 . toInteger . tapleafVersion $ envTap env',
        'interpret ScriptCMR': 'element . return . encodeHash . tapScriptCMR $ envTap env',
        'interpret InternalKey': 'element . return . encodeKey . tapInternalKey $ envTap env',
        'encodeKey (Schnorr.PubKey x)': 'toWord256 . toInteger $ x',
    }.items():
        binding('elements_primitive_hs', lhs, rhs)
    p.require(s['native_schnorr'], 'import Simplicity.Word', 'native key word import')
    p.require(s['native_schnorr'], 'data PubKey = PubKey Word256', 'native key carrier')
    p.require(s['native_spec'], 'import Simplicity.LibSecp256k1.Schnorr', 'native key re-export import')
    p.require(s['native_spec'], 'PubKey(..), pubkey_unpack', 'native key re-export')
    if re.search(r'\b(?:data|newtype|type)\s+PubKey\b', s['native_spec']):
        raise ValueError('native key re-export is shadowed')
    p.require(s['secp_types'], 'type PubKey = Word256', 'Simplicity key program type')
    for expected in [
        '| TapleafVersion => fun _ => Some (fromZ (Byte.unsigned (tapleafVersion (envTap e))))',
        '| ScriptCMR => fun _ => Some (encodeHash (tapScriptCMR (envTap e)))',
        '| InternalKey => fun _ => Some (from_hash256 (tapInternalKey (envTap e)))',
    ]:
        p.require(s['elements_primitive_coq'], expected, 'Elements tap primitive interpretation')


def elements_issuance_proofs_hash(s):
    """Canonical two-primitive loop and whole original C boundary.
    Primitive proof-view/lens boundaries use the mandatory existing
    elements-issuance-proof guard and the reused closed view lemmas.
    """
    def binding(key, lhs, expected):
        if p.compact(hbody(s[key], lhs)) != p.compact(expected):
            raise ValueError('Elements issuance binding differs: ' + lhs)

    def replace(text, old, new):
        return re.sub(r'\s*'.join(re.escape(c) for c in p.compact(old)), lambda _: new, text)

    tag, name = 'IssuanceRangeProofsHash', 'issuanceRangeProofsHash'
    p.require(s['elements_catalog'], tag + ' :: SigHashJet () Word256', 'issuance hash type')
    binding('elements_catalog', 'specificationSigHash ' + tag, 'SigHash.' + name)
    binding('elements_sighash_lib', name, 'SigHash.' + name + ' SigHash.lib')
    hs_programs = s['elements_sighash'].split('mkLib Sha256.Lib{..} Sha256.LibAssert{..} Transaction.Lib{..} = lib', 1)[1]
    selected = re.search(r'\b' + name + r'\s*=(.*?)\n\s*[,}]', hs_programs, re.S)
    if not selected:
        raise ValueError('missing issuance range proofs program')
    parts = re.fullmatch(r'\s*let\s+finalize\s*=\s*ctx8Finalize\s+body\s*=(.*?)\bin\b(.*)', selected[1], re.S)
    if not parts:
        raise ValueError('issuance loop bindings differ')
    ops = [('@AC.comp _ _ _ core', 'compNode'), ('@AC.pair _ _ _ core', 'pairNode'),
           ('@AC.case _ _ _ _ core', 'caseNode'), ('@AC.copair _ _ _ core', 'copairNode'),
           ('@AC.injl _ _ _ core', 'injlNode'), ('@AC.injr _ _ _ core', 'injrNode'),
           ('@AC.take _ _ _ core', 'takeNode'), ('@AC.drop _ _ _ core', 'dropNode'),
           ('@AC.drop Ty.Unit Word32 _ core', 'dropNode'), ('@AC.unit _ core', 'unit'),
           ('@AC.iden _ core', 'iden'), ('AC.drop', 'dropNode'), ('AC.take', 'takeNode'), ('AC.iden', 'iden')]
    aliases = [('@EFP.Combinators.prim _ _ alg Elements.IssuanceAssetProof', 'assetProof'),
               ('@EFP.Combinators.prim _ _ alg Elements.IssuanceTokenProof', 'tokenProof'),
               ('@literal_ctx8_addn 6 term', 'add64'),
               ('@literal_sha_hash_ctx_init core', 'ctx8Init'),
               ('@literal_ctx8_finalize term', 'ctx8Finalize'),
               ('@for_while_program 5 _ _ _ core (@literal_elements_issuance_proofs_body alg)', 'loop')]
    atoms = {'assetProof', 'tokenProof', 'add64', 'ctx8Init', 'ctx8Finalize', 'unit', 'loop'}
    def tree(name):
        port = p.definition(s['elements_issuance_port'], name)
        header = re.fullmatch(r'\s*let term := EFP\.CanonicalStructures\.toAssertion alg in\s*'
                              r'let core := Alg\.Assertion\.toCore term in\s*(.*)', port, re.S)
        if not header:
            raise ValueError('issuance algebra binding differs')
        port = header[1]
        for old, new in aliases + ops:
            port = replace(port, old, new)
        return explicit_core_tree(expression(port), atoms)
    body = parts[1]
    for old, new in [('primitive IssuanceAssetProof', 'assetProof'),
                     ('primitive IssuanceTokenProof', 'tokenProof'), ('ctx8Addn vector64', 'add64')]:
        body = replace(body, old, new)
    if expression(body) != tree('literal_elements_issuance_proofs_body'):
        raise ValueError('issuance two-lookup/body tree differs')
    program = replace(replace(parts[2], 'forWhile word32 body', 'loop'), 'finalize', 'ctx8Finalize')
    if expression(program) != tree('literal_elements_issuance_range_proofs_hash'):
        raise ValueError('issuance whole traversal differs')
    expected = '''application_jet_local_spec_sep f_simplicity_issuance_range_proofs_hash elements_ge Elements.env Ty.Unit Word256
        (hash_getter_rep elements_issuance_range_proofs_hash_of 0 536 760)
        (fun a environment => @literal_elements_issuance_range_proofs_hash elements_hash_alg a environment).'''
    statement = re.search(r'Theorem elements_issuance_range_proofs_hash_literal_local_spec\s*:(.*?)\bProof\.', s['elements_issuance_port'], re.S)
    if not statement or p.compact(statement[1]) != p.compact(expected):
        raise ValueError('issuance whole C contract differs')
    for part, token in [('asset', 'false'), ('token', 'true')]:
        found = re.search(r'Lemma literal_elements_issuance_' + part + r'_proof_view_matches txi\s*:(.*?)\bProof\.', s['elements_issuance_port'], re.S)
        expected = 'elements_issuance_' + part + '_proof_bytes txi = haskell_issuance_proof_view ' + token + ' txi.'
        if not found or p.compact(found[1]) != p.compact(expected):
            raise ValueError('reused closed issuance proof-view bridge differs')


def elements_nonce_hashes(s):
    """Whole nonce serializer/loop and original C getter.
    The native-word primitive boundary reuses the mandatory output-nonce
    guard and the closed encoder bridge, rather than a field restriction.
    """
    def replace(text, old, new):
        return re.sub(r'\s*'.join(re.escape(c) for c in p.compact(old)), lambda _: new, text)

    def binding(key, lhs, expected):
        if p.compact(hbody(s[key], lhs)) != p.compact(expected):
            raise ValueError('Elements nonce binding differs: ' + lhs)

    binding('elements_prog_lib', 'nonceHash', 'Elements.nonceHash Elements.libAssert')
    contexts = s['elements_prog'].split('mkLibAssert Sha256.Lib{..} Sha256.LibAssert{..} LibSecp256k1.Lib{..} = libAssert', 1)[1]
    hs = re.search(r'\bnonceHash\s*=(.*?)\n\s*,\s*annexHash', contexts, re.S)
    if not hs:
        raise ValueError('missing canonical nonce serializer')
    port = p.definition(s['elements_nonce_port'], 'literal_elements_nonce_hash')
    for byte in ['0x01', '0x02', '0x03']:
        port = replace(port, 'Alg.scribe (haskell_to_word 3 ' + byte + ')', 'scribe (toWord8 ' + byte + ')')
    for old, new in [('@Word.zero 3 (Alg.Assertion.toCore term)', 'zero word8'),
                     ('@literal_ctx8_add1 term', 'ctx8Add1'), ('@literal_ctx8_addn 5 term', 'ctx8Add32')]:
        port = replace(port, old, new)
    same(hs[1], port, 'canonical Elements nonce serializer')
    p.require(contexts, 'ctx8Add32 = ctx8Addn vector32', 'nonce payload width')
    tag, name = 'OutputNoncesHash', 'outputNoncesHash'
    p.require(s['elements_catalog'], tag + ' :: SigHashJet () Word256', 'nonce hash jet type')
    binding('elements_catalog', 'specificationSigHash ' + tag, 'SigHash.' + name)
    binding('elements_sighash_lib', name, 'SigHash.' + name + ' SigHash.lib')
    programs = s['elements_sighash'].split('mkLib Sha256.Lib{..} Sha256.LibAssert{..} Transaction.Lib{..} = lib', 1)[1]
    hs = re.search(r'\b' + name + r'\s*=(.*?)\n\s*[,}]', programs, re.S)
    if not hs:
        raise ValueError('missing nonce hash loop')
    parts = re.fullmatch(r'\s*let\s+finalize\s*=\s*ctx8Finalize\s+body\s*=(.*?)\bin\b(.*)', hs[1], re.S)
    if not parts:
        raise ValueError('nonce loop bindings differ')
    hs_body = replace(parts[1], 'drop (primitive OutputNonce)', 'array')
    body = p.definition(s['elems_loop'], 'gen_loop_body')
    prefix = 'let core := Alg.Assertion.toCore term in'
    if not body.lstrip().startswith(prefix):
        raise ValueError('nonce generic loop algebra differs')
    body = body.lstrip()[len(prefix):]
    for old, new in [('add term', 'nonceHash'), ('@AC.comp _ _ _ core', 'compNode'),
                     ('@AC.pair _ _ _ core', 'pairNode'), ('@AC.case _ _ _ _ core', 'caseNode'),
                     ('@AC.injl _ _ _ core', 'injlNode'), ('@AC.injr _ _ _ core', 'injrNode'),
                     ('@AC.take _ _ _ core', 'takeNode'), ('@AC.drop _ _ _ core', 'dropNode'),
                     ('@AC.iden _ core', 'iden')]:
        body = replace(body, old, new)
    if expression(hs_body) != explicit_core_tree(expression(body), {'array', 'nonceHash'}):
        raise ValueError('nonce stop/continue loop tree differs')
    same(parts[2], 'unit &&& ctx8Init >>> forWhile word32 body >>> copair finalize finalize', 'nonce traversal')
    expected = '''let term := EFP.CanonicalStructures.toAssertion alg in
      let core := Alg.Assertion.toCore term in
      @literal_elements_elems_hash elements_nonce_type
        (fun term => @literal_elements_nonce_hash term) 5 term
        (@Alg.Core.Combinators.drop Ty.Unit Word32 _ core
          (@EFP.Combinators.prim _ _ alg Elements.OutputNonce))'''
    if p.compact(p.definition(s['elements_nonce_port'], 'literal_elements_output_nonces_hash')) != p.compact(expected):
        raise ValueError('nonce primitive/loop adapter differs')
    found = re.search(r'Lemma literal_elements_nonce_encode_matches n\s*:(.*?)\bProof\.', s['elements_nonce_port'], re.S)
    if not found or p.compact(found[1]) != p.compact('elements_nonce_encode n = encode_nonce_literal n.'):
        raise ValueError('native nonce encoder bridge differs')
    statement = re.search(r'Theorem elements_output_nonces_hash_literal_local_spec\s*:(.*?)\bProof\.', s['elements_nonce_port'], re.S)
    expected = '''application_jet_local_spec_sep f_simplicity_output_nonces_hash elements_ge Elements.env Ty.Unit Word256
        (hash_getter_rep elements_output_nonces_hash_of 0 56 760)
        (fun a environment => @literal_elements_output_nonces_hash elements_hash_alg a environment).'''
    if not statement or p.compact(statement[1]) != p.compact(expected):
        raise ValueError('nonce whole C contract differs')


def elements_amount_hashes(s):
    """Three canonical serializers, shared primitive-pair loop and C getters.
    Native primitive encoders/pair routing and the generic element loop
    reuse their existing mandatory source/definition guards.
    """
    def replace(text, old, new):
        return re.sub(r'\s*'.join(re.escape(c) for c in p.compact(old)), lambda _: new, text)

    def binding(key, lhs, expected):
        if p.compact(hbody(s[key], lhs)) != p.compact(expected):
            raise ValueError('Elements amount-hash binding differs: ' + lhs)

    def definition(name, expected):
        if p.compact(p.definition(s['elements_amounts_port'], name)) != p.compact(expected):
            raise ValueError('Elements amount-hash adapter differs: ' + name)

    binding('elements_prog_lib', 'assetAmountHash', 'Elements.assetAmountHash Elements.libAssert')
    contexts = s['elements_prog'].split('mkLibAssert Sha256.Lib{..} Sha256.LibAssert{..} LibSecp256k1.Lib{..} = libAssert', 1)[1]
    for stem, pattern in [
        ('asset', r'\bassetHash\s*=(.*?)\n\s*amountHash\s*='),
        ('amount', r'\bamountHash\s*=(.*?)\n\s*taptweakPrefix\s*='),
        ('asset_amount', r'\bassetAmountHash\s*=(.*?)\n\s*,\s*nonceHash'),
    ]:
        hs = re.search(pattern, contexts, re.S)
        if not hs:
            raise ValueError('missing canonical Elements serializer')
        port = p.definition(s['elements_amounts_port'], 'literal_elements_' + stem + '_hash')
        for byte in ['0x01', '0x08', '0x09', '0x0a', '0x0b']:
            port = replace(port, 'Alg.scribe (haskell_to_word 3 ' + byte + ')', 'scribe (toWord8 ' + byte + ')')
        for old, new in [
            ('@literal_ctx8_add1 term', 'ctx8Add1'), ('@literal_ctx8_addn 5 term', 'ctx8Add32'),
            ('@literal_ctx8_addn 3 term', 'ctx8Add8'),
            ('@literal_elements_asset_hash term', 'assetHash'),
            ('@literal_elements_amount_hash term', 'amountHash'),
        ]:
            port = replace(port, old, new)
        same(hs[1], port, 'Elements ' + stem + ' canonical serializer')
    p.require(contexts, 'ctx8Add8 = ctx8Addn vector8', 'explicit amount width')
    p.require(contexts, 'ctx8Add32 = ctx8Addn vector32', 'confidential payload width')
    definition('literal_elements_amounts_hash', '''
      let term := EFP.CanonicalStructures.toAssertion alg in
      let core := Alg.Assertion.toCore term in
      @literal_elements_elems_hash elements_asset_amount_type
        (fun term => @literal_elements_asset_amount_hash term) 5 term
        (@Alg.Core.Combinators.drop Ty.Unit Word32 _ core
          (@elements_amount_pair_spec alg Word32 elements_amount_hash_type elements_asset_hash_type
            (@EFP.Combinators.prim _ _ alg pm) (@EFP.Combinators.prim _ _ alg pa)))''')
    programs = s['elements_sighash'].split('mkLib Sha256.Lib{..} Sha256.LibAssert{..} Transaction.Lib{..} = lib', 1)[1]
    for tag, name, stem, primitive, offset in [
        ('OutputAmountsHash', 'outputAmountsHash', 'output_amounts', 'Output', 24),
        ('InputAmountsHash', 'inputAmountsHash', 'input_amounts', 'Input', 248),
    ]:
        p.require(s['elements_catalog'], tag + ' :: SigHashJet () Word256', 'amount hash jet type')
        binding('elements_catalog', 'specificationSigHash ' + tag, 'SigHash.' + name)
        binding('elements_sighash_lib', name, 'SigHash.' + name + ' SigHash.lib')
        hs = re.search(r'\b' + name + r'\s*=(.*?)\n\s*[,}]', programs, re.S)
        if not hs:
            raise ValueError('missing canonical amount hash loop')
        parts = re.fullmatch(r'\s*let\s+finalize\s*=\s*ctx8Finalize\s+body\s*=(.*?)\bin\b(.*)', hs[1], re.S)
        if not parts:
            raise ValueError('amount loop bindings differ')
        same(parts[1], 'take (drop ' + ('outputAmount' if primitive == 'Output' else 'inputAmount') +
             ') &&& ih >>> match (injl ih) (injr (ih &&& oh >>> assetAmountHash))', 'amount element loop')
        same(parts[2], 'unit &&& ctx8Init >>> forWhile word32 body >>> copair finalize finalize', 'amount traversal')
        definition('literal_elements_' + stem + '_hash',
                   '@literal_elements_amounts_hash Elements.' + primitive + 'Amount Elements.' + primitive + 'Asset alg')
        statement = re.search(r'Theorem elements_' + stem + r'_hash_literal_local_spec\s*:(.*?)\bProof\.', s['elements_amounts_port'], re.S)
        expected = f'''application_jet_local_spec_sep f_simplicity_{stem}_hash elements_ge Elements.env Ty.Unit Word256
            (hash_getter_rep elements_{stem}_hash_of 0 {offset} 760)
            (fun a environment => @literal_elements_{stem}_hash elements_hash_alg a environment).'''
        if not statement or p.compact(statement[1]) != p.compact(expected):
            raise ValueError('amount whole C contract differs')


def elements_composite_hashes(s):
    """Full composition trees, fixed-vector widths and original C boundaries.
    Each component's canonical/primitive/native boundary has an existing gate.
    """
    def replace(text, old, new):
        return re.sub(r'\s*'.join(re.escape(c) for c in p.compact(old)), lambda _: new, text)

    def binding(key, lhs, expected):
        if p.compact(hbody(s[key], lhs)) != p.compact(expected):
            raise ValueError('Elements composite binding differs: ' + lhs)

    fixed = p.definition(s['elements_composite_port'], 'literal_elements_fixed_vector_hash')
    expected = '''let term := EFP.CanonicalStructures.toAssertion alg in
      let core := Alg.Assertion.toCore term in
      @AC.comp _ _ _ core
        (@AC.pair _ _ _ core (@literal_sha_hash_ctx_init core) payload)
        (@AC.comp _ _ _ core (@literal_ctx8_addn k term) (@literal_ctx8_finalize term))'''
    if p.compact(fixed) != p.compact(expected):
        raise ValueError('Elements fixed-vector hash skeleton differs')
    aliases = [
        ('@literal_elements_output_amounts_hash alg', 'outputAmountsHash'),
        ('@literal_elements_output_nonces_hash alg', 'outputNoncesHash'),
        ('@literal_elements_output_scripts_hash alg', 'outputScriptsHash'),
        ('@literal_elements_output_range_proofs_hash alg', 'outputRangeProofsHash'),
        ('@literal_elements_input_amounts_hash alg', 'inputAmountsHash'),
        ('@literal_elements_input_scripts_hash alg', 'inputScriptsHash'),
    ]
    atoms = {new for _, new in aliases}
    programs = s['elements_sighash'].split('mkLib Sha256.Lib{..} Sha256.LibAssert{..} Transaction.Lib{..} = lib', 1)[1]
    for tag, hs_name, stem, k, offset in [
        ('OutputsHash', 'outputsHash', 'outputs', 7, 184),
        ('InputUtxosHash', 'inputUtxosHash', 'input_utxos', 6, 312),
    ]:
        p.require(s['elements_catalog'], tag + ' :: SigHashJet () Word256', 'Elements composite type')
        binding('elements_catalog', 'specificationSigHash ' + tag, 'SigHash.' + hs_name)
        binding('elements_sighash_lib', hs_name, 'SigHash.' + hs_name + ' SigHash.lib')
        hs = re.search(r'\b' + hs_name + r'\s*=(.*?)\n\s*[,}]', programs, re.S)
        if not hs:
            raise ValueError('missing Elements composite program')
        port = p.definition(s['elements_composite_port'], 'literal_elements_' + stem + '_hash')
        header = re.fullmatch(r'\s*let core := Alg\.Assertion\.toCore \(EFP\.CanonicalStructures\.toAssertion alg\) in\s*'
                              r'@literal_elements_fixed_vector_hash ' + str(k) + r' alg\s*(.*)', port, re.S)
        if not header:
            raise ValueError('Elements composite hash algebra/width differs')
        payload = header[1]
        for old, new in aliases + [('@AC.pair _ _ _ core', 'pairNode')]:
            payload = replace(payload, old, new)
        payload = explicit_core_tree(expression(payload), atoms)
        expected = ('comp', ('pair', ('name', 'ctx8Init'), payload),
                    ('comp', ('name', 'absorb'), ('name', 'ctx8Finalize')))
        hs = replace(hs[1], 'ctx8Addn vector' + str(2 ** k), 'absorb')
        if expression(hs) != expected:
            raise ValueError('canonical Elements composite component tree differs')
        statement = re.search(r'Theorem elements_' + stem + r'_hash_literal_local_spec\s*:(.*?)\bProof\.', s['elements_composite_port'], re.S)
        expected = f'''application_jet_local_spec_sep f_simplicity_{stem}_hash elements_ge Elements.env Ty.Unit Word256
            (hash_getter_rep elements_{stem}_hash_of 0 {offset} 760)
            (fun a environment => @literal_elements_{stem}_hash elements_hash_alg a environment).'''
        if not statement or p.compact(statement[1]) != p.compact(expected):
            raise ValueError('Elements composite whole C contract differs')


def elements_blinding_entropy_hash(s):
    """Three primitive branches, actual one-word program, SHA loop and C.
    Host/runtime/caller construction remain outside this source guard.
    """
    def replace(text, old, new):
        return re.sub(r'\s*'.join(re.escape(c) for c in p.compact(old)), lambda _: new, text)

    def binding(key, name, expected):
        if p.compact(hbody(s[key], name)) != p.compact(expected):
            raise ValueError('blinding entropy binding differs: ' + name)

    def definition(key, name, expected):
        if p.compact(p.definition(s[key], name)) != p.compact(expected):
            raise ValueError('blinding entropy definition differs: ' + name)

    binding('hs_arith', 'one w', 'true >>> left_pad_low word1 w')
    for text in [
        'fill t SingleV = t', 'fill t (DoubleV w) = rec &&& rec', 'rec = fill t w',
        'low = fill false', 'left_pad_pad _ SingleV = iden',
        'left_pad_pad t (DoubleV v) = fill t v &&& left_pad_pad t v',
        'left_pad_low w v = left_pad_pad (unit >>> low w) v',
    ]:
        p.require(s['hs_word'], text, 'actual one-word padding dependency')
    definition('word', 'fill', 'match n with | 0 => t | (S n) => build_fill (fill t) end')
    definition('word', 'build_fill', 'rec &&& rec')
    definition('one_spec', 'one8_spec', '''@Alg.Core.Combinators.comp Ty.Unit Bit Word8 term
      (@Bit.true Ty.Unit term) (@left_pad_low_1_8 term)''')
    definition('one_spec', 'left_pad_low_1_8', 'left_pad_low_1_n 3')
    definition('one_spec', 'left_pad_low_1_n', '''match n with
      | Datatypes.O => @Alg.Core.Combinators.iden Bit term
      | S n => @Alg.Core.Combinators.pair Bit (Word n) (Word n) term
          (fill (n := n) (@Alg.Core.Combinators.comp Bit Ty.Unit Bit term
            (@Alg.Core.Combinators.unit Bit term) (@Bit.false Ty.Unit term)))
          (left_pad_low_1_n n) end''')

    hs = hbody(s['elements_sighash'], 'issuanceBlindingEntropy')
    parts = re.fullmatch(r'\s*let\s+issuanceEntropyBody\s*=(.*?)\bin\b(.*)', hs, re.S)
    if not parts:
        raise ValueError('missing blinding entropy local routing')
    ops = [
        ('@blinding_entropy_body_spec core', 'body'), ('@Word.zero 8 core', 'zero256'),
        ('AC.case', 'caseNode'), ('AC.comp', 'compNode'), ('AC.pair', 'pairNode'),
        ('AC.injl', 'injlNode'), ('AC.injr', 'injrNode'),
        ('AC.take', 'takeNode'), ('AC.drop', 'dropNode'), ('AC.iden', 'iden'), ('AC.unit', 'unit'),
    ]
    def tree(name):
        text = p.definition(s['elements_blinding_model'], name)
        for old, new in ops:
            text = replace(text, old, new)
        return explicit_core_tree(expression(text), {'unit', 'body', 'zero256'})
    if expression(parts[1]) != tree('blinding_entropy_body_spec'):
        raise ValueError('blinding entropy optional-pair body differs')
    whole = parts[2]
    for old, new in [
        ('primitive NewIssuanceContract', 'pNew'), ('primitive ReissuanceBlinding', 'pBlinding'),
        ('primitive ReissuanceEntropy', 'pEntropy'), ('issuanceEntropyBody', 'body'),
        ('zero word256', 'zero256'),
    ]:
        whole = replace(whole, old, new)
    expected = ('comp', ('pair', ('name', 'pNew'), ('pair', ('name', 'pBlinding'), ('name', 'pEntropy'))),
                tree('blinding_entropy_route_spec'))
    if expression(whole) != expected:
        raise ValueError('three-primitive blinding entropy route differs')
    definition('elements_blinding_model', 'elements_issuance_blinding_entropy_spec', '''
      let core := Alg.Assertion.toCore (EFP.CanonicalStructures.toAssertion alg) in
      @AC.comp _ _ _ core
        (@AC.pair _ _ _ core (@EFP.Combinators.prim _ _ alg Elements.NewIssuanceContract)
          (@AC.pair _ _ _ core (@EFP.Combinators.prim _ _ alg Elements.ReissuanceBlinding)
            (@EFP.Combinators.prim _ _ alg Elements.ReissuanceEntropy)))
        (@blinding_entropy_route_spec core)''')
    absorber = p.definition(s['elements_blinding_port'], 'literal_elements_blinding_entropy_absorb')
    for old, new in [
        ('@Word.zero 3 (Alg.Assertion.toCore term)', 'zero word8'),
        ('@one8_spec (Alg.Assertion.toCore term)', 'one word8'),
        ('@literal_ctx8_add1 term', 'ctx8Add1'), ('@literal_ctx8_addn 6 term', 'ctx8Add64'),
    ]:
        absorber = replace(absorber, old, new)
    same(hbody(s['elements_sighash'], 'blindingEntropyHash'), absorber, 'literal blinding entropy absorber')
    p.require(s['elements_sighash'], 'ctx8Add64 = ctx8Addn vector64', 'blinding pair byte width')
    definition('elements_blinding_port', 'literal_elements_issuance_blinding_entropy_hash', '''
      let term := EFP.CanonicalStructures.toAssertion alg in
      let core := Alg.Assertion.toCore term in
      @literal_elements_elems_hash blinding_entropy_value_type
        (fun term => @literal_elements_blinding_entropy_absorb term) 5 term
        (@Alg.Core.Combinators.drop Ty.Unit Word32 _ core (@elements_issuance_blinding_entropy_spec alg))''')
    tag, name = 'IssuanceBlindingEntropyHash', 'issuanceBlindingEntropyHash'
    p.require(s['elements_catalog'], tag + ' :: SigHashJet () Word256', 'blinding entropy jet type')
    binding('elements_catalog', 'specificationSigHash ' + tag, 'SigHash.' + name)
    binding('elements_sighash_lib', name, 'SigHash.' + name + ' SigHash.lib')
    programs = s['elements_sighash'].split('mkLib Sha256.Lib{..} Sha256.LibAssert{..} Transaction.Lib{..} = lib', 1)[1]
    hs = re.search(r'\b' + name + r'\s*=(.*?)\n\s*[,}]', programs, re.S)
    parts = re.fullmatch(r'\s*let\s+finalize\s*=\s*ctx8Finalize\s+body\s*=(.*?)\bin\b(.*)', hs[1], re.S) if hs else None
    if not parts:
        raise ValueError('blinding entropy traversal bindings differ')
    same(parts[1], 'take (drop issuanceBlindingEntropy) &&& ih >>> match (injl ih) (injr (ih &&& oh >>> blindingEntropyHash))', 'blinding entropy element loop')
    same(parts[2], 'unit &&& ctx8Init >>> forWhile word32 body >>> copair finalize finalize', 'blinding entropy traversal')
    for tag, route in [
        ('NewIssuanceContract', 'either (Just . newIssuanceContractHash) (const Nothing)'),
        ('ReissuanceBlinding', 'either (const Nothing) (Just . reissuanceBlindingNonce)'),
        ('ReissuanceEntropy', 'either (const Nothing) (Just . reissuanceEntropy)'),
    ]:
        binding('elements_primitive_hs', 'interpret ' + tag,
                'return . (atInput $ cast . fmap encodeHash . (' + route + ' <=< sigTxiIssuance))')
    for clause in [
        '| Some (inl new) => Some (newIssuanceContractHash new)',
        '| Some (inr re) => Some (reissuanceBlindingNonce re)',
        '| Some (inr re) => Some (reissuanceEntropy re)',
    ]:
        p.require(s['elements_primitive_coq'], clause, 'blinding entropy primitive payload')
    statement = re.search(r'Theorem elements_issuance_blinding_entropy_hash_literal_local_spec\s*:(.*?)\bProof\.', s['elements_blinding_port'], re.S)
    expected = '''application_jet_local_spec_sep f_simplicity_issuance_blinding_entropy_hash elements_ge Elements.env Ty.Unit Word256
      (hash_getter_rep elements_issuance_blinding_entropy_hash_of 0 568 760)
      (fun a environment => @literal_elements_issuance_blinding_entropy_hash elements_hash_alg a environment).'''
    if not statement or p.compact(statement[1]) != p.compact(expected):
        raise ValueError('blinding entropy whole C contract differs')


def elements_issuance_status(s):
    """Resolve canonical flip-match explicitly; retain all four outcomes.
    The contract has no hash-cache, execution or success premise.
    """
    def replace(text, old, new):
        return re.sub(r'\s*'.join(re.escape(c) for c in p.compact(old)), lambda _: new, text)

    def binding(key, lhs, expected):
        if p.compact(hbody(s[key], lhs)) != p.compact(expected):
            raise ValueError('issuance status binding differs: ' + lhs)

    def definition(key, name, expected):
        if p.compact(p.definition(s[key], name)) != p.compact(expected):
            raise ValueError('issuance status definition differs: ' + name)

    def unflip(node):
        node = tuple(unflip(x) if isinstance(x, tuple) else x for x in node)
        if (node[0] == 'app' and node[1][0] == 'app' and node[1][1][0] == 'app'
                and node[1][1][1] == ('name', 'flip') and node[1][1][2] == ('name', 'case')):
            return ('app', ('app', ('name', 'case'), node[2]), node[1][2])
        return node

    p.require(s['elements_catalog'], 'Issuance :: IssuanceJet Word32 (S (S Bit))', 'issuance status jet type')
    binding('elements_catalog', 'specificationIssuance Issuance', 'Issuance.issuance')
    binding('elements_issuance_lib', 'issuance', 'Issuance.issuance Issuance.lib')
    binding('elements_issuance_program', 'lib', 'mkLib Elements.lib')
    programs = s['elements_issuance_program'].split('mkLib Elements.Lib{..} = lib', 1)[1]
    hs = re.search(r'\bissuance\s*=(.*?)\n\s*,\s*issuanceEntropy', programs, re.S)
    if not hs:
        raise ValueError('missing canonical issuance status program')
    hs = hs[1]
    for old, new in [('primitive ReissuanceEntropy', 'pReissuance'), ('primitive NewIssuanceContract', 'pNew')]:
        hs = replace(hs, old, new)
    route = p.definition(s['elements_status_model'], 'issuance_status_route')
    for old, new in [('ISC.case', 'caseNode'), ('ISC.copair', 'copairNode'),
                     ('ISC.injl', 'injlNode'), ('ISC.injr', 'injrNode'),
                     ('ISC.drop', 'dropNode'), ('ISC.take', 'takeNode'),
                     ('ISC.unit', 'unit'), ('ISC.iden', 'iden'),
                     ('Bit.false', 'false'), ('Bit.true', 'true')]:
        route = replace(route, old, new)
    route = explicit_core_tree(expression(route), {'unit', 'false', 'true'})
    expected = ('comp', ('pair', ('name', 'pReissuance'), ('name', 'pNew')), route)
    if unflip(expression(hs)) != expected:
        raise ValueError('canonical issuance flip-match/copair tree differs')
    definition('elements_status_model', 'elements_issuance_status_spec', '''
      elements_comp
        (elements_pair (Primitive.Combinators.prim Elements.ReissuanceEntropy)
                       (Primitive.Combinators.prim Elements.NewIssuanceContract))
        (elements_core (@issuance_status_route))''')
    definition('elements_status_model', 'issuance_status_digest_option', 'Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256)')
    definition('elements_status_model', 'issuance_status_payload', 'Ty.Sum Ty.Unit Bit')
    definition('elements_status_model', 'issuance_status_type', 'Ty.Sum Ty.Unit issuance_status_payload')
    definition('elements_status_model', 'issuance_status_of_input', '''match sigTxiIssuance txi with
      | None => inl tt | Some (inl _) => inr (inl tt) | Some (inr _) => inr (inr tt) end''')
    definition('elements_status_model', 'issuance_status_result', '''match nth_error elems (Z.to_nat (toZ a)) with
      | None => inl tt | Some txi => inr (issuance_status_of_input txi) end''')
    definition('elements_status_exec', 'issuance_status_enum_rep',
               'Mem.load Mint32 m b (ofs + 528) = Some (Vint (issuance_tag (sigTxiIssuance txi)))')
    definition('elements_status_exec', 'issuance_status_pcells',
               '@encode issuance_status_payload (issuance_status_of_input txi)')
    statement = re.search(r'Theorem elements_issuance_status_local_spec\s*:(.*?)\bProof\.', s['elements_status_local'], re.S)
    expected = '''application_jet_local_spec_sep f_simplicity_issuance elements_ge Elements.env Word32 issuance_status_type
      (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e)) issuance_status_enum_rep 544 0 0 696)
      (fun a environment => @elements_issuance_status_spec (PrimitivePrimSem option_Monad_Zero) a environment).'''
    if not statement or p.compact(statement[1]) != p.compact(expected):
        raise ValueError('issuance status complete C contract differs')
    definition('elements_status_tags', 'issuance_tag', '''match o with
      None => Int.repr 0 | Some (inl _) => Int.repr 1 | Some (inr _) => Int.repr 2 end''')


def elements_issuance_computed(s):
    """Literal calculations, primitive routing and complete original C getters.
    Cached-value establishment by the real environment builder stays separate.
    """
    def replace(text, old, new):
        return re.sub(r'\s*'.join(re.escape(c) for c in p.compact(old)), lambda _: new, text)

    def binding(key, lhs, expected):
        if p.compact(hbody(s[key], lhs)) != p.compact(expected):
            raise ValueError('computed issuance binding differs: ' + lhs)

    def definition(key, name, expected):
        if p.compact(p.definition(s[key], name)) != p.compact(expected):
            raise ValueError('computed issuance definition differs: ' + name)

    def unflip(node):
        node = tuple(unflip(x) if isinstance(x, tuple) else x for x in node)
        if (node[0] == 'app' and node[1][0] == 'app' and node[1][1][0] == 'app'
                and node[1][1][1] == ('name', 'flip') and node[1][1][2] == ('name', 'case')):
            return ('app', ('app', ('name', 'case'), node[2]), node[1][2])
        return node

    def coq_tree(body, aliases, atoms):
        for old, new in aliases + [('LC.' + op, op + 'Node') for op in
                                  ['comp', 'pair', 'case', 'copair', 'take', 'drop', 'injl', 'injr']]:
            body = replace(body, old, new)
        body = replace(replace(body, 'LC.unit', 'unit'), 'LC.iden', 'iden')
        return explicit_core_tree(expression(body), atoms)

    # The mandatory shared SHA checker fixes all rounds and the actual IV.
    definition('elements_calc_port', 'literal_issuance_iv', '''
      Alg.scribe (haskell_to_word 8
        0x6a09e667bb67ae853c6ef372a54ff53a510e527f9b05688c1f83d9ab5be0cd19)''')
    binding('elements_prog', 'lib', 'mkLib Sha256.lib')
    binding('elements_issuance_program', 'lib', 'mkLib Elements.lib')
    calculation_body = s['elements_prog'].split('mkLib Sha256.Lib{..} = lib', 1)[1]
    constants = [(5, '(2 ^ 31)', '32', '(2^31)', 'pad32'),
                 (7, '(256 + 32)', '128', '(256+32)', 'len128'),
                 (8, '(2 ^ 255 + 256)', '256', '(2^255 + 256)', 'pad256'),
                 (8, '(2 * 2 ^ 248)', '256', '(2*2^248)', 'tokenConf'),
                 (8, '(2 ^ 248)', '256', '(2^248)', 'tokenExplicit')]
    aliases = [('literal_issuance_iv', 'iv'), ('literal_issuance_op_hash', 'opHash'),
               ('literal_sha_256_block', 'hashBlock'),
               ('@Word.zero 6 core', 'zero64'), ('@Word.zero 8 core', 'zero256')]
    for depth, number, width, hs_number, atom in constants:
        aliases.insert(0, ('Alg.scribe (haskell_to_word ' + str(depth) + ' ' + number + ')', atom))
    atoms = {'iv', 'opHash', 'hashBlock', 'zero64', 'zero256', 'unit'} | {c[4] for c in constants}
    for hs_name, coq_name in [
        ('opHash', 'literal_issuance_op_hash'),
        ('calculateIssuanceEntropy', 'literal_calculate_issuance_entropy'),
        ('calculateAsset', 'literal_calculate_asset'),
        ('calculateExplicitToken', 'literal_calculate_explicit_token'),
        ('calculateConfidentialToken', 'literal_calculate_confidential_token'),
    ]:
        if hs_name == 'opHash':
            hs = hbody(calculation_body, hs_name)
        else:
            found = re.search(r'\b' + hs_name + r'\s*=(.*?)\n\s*[,}]', calculation_body, re.S)
            if not found:
                raise ValueError('missing issuance calculation: ' + hs_name)
            hs = found[1]
        for depth, number, width, hs_number, atom in constants:
            hs = replace(hs, 'scribe (toWord' + width + ' ' + hs_number + ')', atom)
        hs = replace(replace(hs, 'zero word64', 'zero64'), 'zero word256', 'zero256')
        if expression(hs) != coq_tree(p.definition(s['elements_calc_port'], coq_name), aliases, atoms):
            raise ValueError('issuance calculation Core tree differs: ' + hs_name)

    primitives = [('ReissuanceEntropy', 'pReissuance'), ('NewIssuanceContract', 'pNew'),
                  ('InputPrevOutpoint', 'pOutpoint'), ('IssuanceAssetAmount', 'pAmount')]
    calcs = [('literal_calculate_issuance_entropy', 'calculateIssuanceEntropy'),
             ('literal_calculate_asset', 'calculateAsset'),
             ('literal_calculate_confidential_token', 'calculateConfidentialToken'),
             ('literal_calculate_explicit_token', 'calculateExplicitToken')]
    route_atoms = {'unit'} | {c[1] for c in calcs}
    def route(name):
        text = p.definition(s['elements_computed_port'], name)
        if name == 'literal_issuance_entropy_route':
            text = replace(text, 'literal_new_issuance_entropy_route',
                           '(' + p.definition(s['elements_computed_port'], 'literal_new_issuance_entropy_route') + ')')
        return coq_tree(text, calcs, route_atoms)

    routes = {'entropy': route('literal_issuance_entropy_route'),
              'asset': route('literal_issuance_asset_route'),
              'token': route('literal_issuance_token_route')}
    programs = s['elements_issuance_program'].split('mkLib Elements.Lib{..} = lib', 1)[1]
    for stem, hs_name, tag, offset in [
        ('entropy', 'issuanceEntropy', 'IssuanceEntropy', 72),
        ('asset', 'issuanceAsset', 'IssuanceAsset', 168),
        ('token', 'issuanceToken', 'IssuanceToken', 200),
    ]:
        p.require(s['elements_catalog'], tag + ' :: IssuanceJet Word32 (S (S Word256))', 'computed issuance type')
        binding('elements_catalog', 'specificationIssuance ' + tag, 'Issuance.' + hs_name)
        binding('elements_issuance_lib', hs_name, 'Issuance.' + hs_name + ' Issuance.lib')
        found = re.search(r'\b' + hs_name + r'\s*=(.*?)\n\s*[,}]', programs, re.S)
        if not found:
            raise ValueError('missing primitive issuance program: ' + hs_name)
        hs = found[1]
        for prim, atom in primitives:
            hs = replace(hs, 'primitive ' + prim, atom)
        hs = replace(hs, 'issuanceEntropy', 'entropy')
        if stem == 'entropy':
            expected = ('comp', ('pair', ('name', 'pReissuance'),
                         ('pair', ('name', 'pNew'), ('name', 'pOutpoint'))), routes[stem])
            adapter = '''elements_comp
              (elements_pair (Primitive.Combinators.prim Elements.ReissuanceEntropy)
                (elements_pair (Primitive.Combinators.prim Elements.NewIssuanceContract)
                  (Primitive.Combinators.prim Elements.InputPrevOutpoint)))
              (elements_core (@literal_issuance_entropy_route))'''
        elif stem == 'asset':
            expected = ('comp', ('name', 'entropy'), routes[stem])
            adapter = '''elements_comp literal_elements_issuance_entropy
              (elements_core (@literal_issuance_asset_route))'''
        else:
            expected = ('comp', ('pair', ('name', 'entropy'), ('name', 'pAmount')), routes[stem])
            adapter = '''elements_comp
              (elements_pair literal_elements_issuance_entropy (Primitive.Combinators.prim Elements.IssuanceAssetAmount))
              (elements_core (@literal_issuance_token_route))'''
        if unflip(expression(hs)) != expected:
            raise ValueError('primitive issuance routing Core tree differs: ' + hs_name)
        definition('elements_computed_port', 'literal_elements_issuance_' + stem, adapter)
        statement = re.search(r'Theorem elements_issuance_' + stem + r'_literal_local_spec\s*:(.*?)\bProof\.',
                              s['elements_computed_port'], re.S)
        expected_contract = (
            'application_jet_local_spec_sep f_simplicity_issuance_' + stem + ' elements_ge Elements.env Word32 issuance_digest_option '
            '(indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e)) '
            '(computed_issuance_hash_rep ' + str(offset) + ' issuance_' + stem + '_of_input) 544 0 0 696) '
            '(fun a environment => @literal_elements_issuance_' + stem + ' (PrimitivePrimSem option_Monad_Zero) a environment).')
        if not statement or p.compact(statement[1]) != p.compact(expected_contract):
            raise ValueError('complete issuance C getter contract differs: ' + stem)
    definition('elements_computed_exec', 'computed_issuance_hash_rep', r'''
      issuance_status_enum_rep m b ofs txi /\
      forall h, value txi = inr h ->
        uint32_array_at m b (ofs + 256 + delta) (hash256_reg (to_hash256 h))''')


def elements_annex_context(s):
    """The shared literal annex program also describes the original Elements jet.
    Shared context trees/encoders have mandatory checks above; retain both
    assertion outcomes, the initialized SHA globals and external memcpy premise.
    """
    for key, lhs, expected in [
        ('elements_catalog', 'specificationSigHash AnnexHash', 'Prog.annexHash'),
        ('elements_prog_lib', 'annexHash', 'Elements.annexHash Elements.libAssert'),
        ('elements_prog', 'libAssert', 'mkLibAssert Sha256.lib Sha256.libAssert LibSecp256k1.lib'),
    ]:
        if p.compact(hbody(s[key], lhs)) != p.compact(expected):
            raise ValueError('Elements annex library binding differs: ' + lhs)
    p.require(s['elements_catalog'], 'AnnexHash :: SigHashJet (Ctx8, S Word256) Ctx8', 'annex context jet type')
    for key, theorem, predicate, program in [
        ('elements_annex_exec', 'elements_annex_hash_local_spec', 'nonce_sha_partial_local_spec',
         '(fun a => @annex_hash_spec optalg a)'),
        ('elements_annex_context_port', 'elements_annex_hash_literal_local_spec', 'nonce_elements_partial_local_spec',
         '(@literal_bitcoin_annex_hash optalg)'),
    ]:
        statement = re.search(r'Theorem ' + theorem + r'\s*:(.*?)\bProof\.', s[key], re.S)
        expected = ('memcpy_model -> ' + predicate + ' f_simplicity_annex_hash '
                    '(Ty.Prod sha256_ctx8_type (Ty.Sum Ty.Unit (Word 8))) sha256_ctx8_type ' + program + '.')
        if not statement or p.compact(statement[1]) != p.compact(expected):
            raise ValueError('Elements annex whole original C contract differs: ' + theorem)


def elements_tap_builders(s):
    """Reuse the checked Bitcoin payload tree, with actual Elements tags/ge.
    This is correspondence and boundary checking, not a new execution oracle.
    """
    def binding(key, lhs, expected):
        actual = hbody(s[key], lhs)
        if re.findall(r'"([^"]*)"', actual) != re.findall(r'"([^"]*)"', expected):
            raise ValueError('Elements builder literal string differs: ' + lhs)
        if p.compact(actual) != p.compact(expected):
            raise ValueError('Elements builder binding differs: ' + lhs)

    def definition(key, name, expected):
        if p.compact(p.definition(s[key], name)) != p.compact(expected):
            raise ValueError('Elements builder definition differs: ' + name)

    def hs_program(key, name):
        library = s[key].split('mkLib Sha256.Lib{..} = lib', 1)[1]
        found = re.search(r'\b' + name + r'\s*=(.*?)\n\s*[,}]', library, re.S)
        if not found:
            raise ValueError('missing Elements builder tree: ' + name)
        return found[1]

    binding('elements_prog', 'lib', 'mkLib Sha256.lib')
    binding('elements_prog', 'simplicityVersion', 'scribe . toWord8 $ 0xbe')
    definition('eltap_linkage', 'sha_ge', 'Clight.globalenv jets_elements.prog')
    if p.compact(p.definition(s['eltap_contract'], 'elements_sha_local_spec_pre')) != p.compact(
            p.definition(s['sha_original_tap_contract'], 'sha_jet_local_spec_pre')):
        raise ValueError('Elements initialized-frame contract differs from the existing complete SHA contract')
    p.require(s['eltap_contract'], 'Require Import C.jet_elements_support_sha_linkage.',
              'actual Elements program contract linkage')

    for tag, name, stem, size, field in [
        ('BuildTapleafSimplicity', 'buildTapleafSimplicity', 'leaf', 'Word256', '_tagName__1'),
        ('BuildTapbranch', 'buildTapbranch', 'branch', '(Word256, Word256)', '_tagName__2'),
    ]:
        label = 'TapLeaf/elements' if stem == 'leaf' else 'TapBranch/elements'
        short = 'TapLeaf' if stem == 'leaf' else 'TapBranch'
        prefix = 'tapleafPrefix' if stem == 'leaf' else 'tapbranchPrefix'
        binding('elements_catalog', 'specificationSigHash ' + tag, 'Prog.' + name)
        p.require(s['elements_catalog'], tag + ' :: SigHashJet ' + size + ' Word256', 'Elements builder catalog type')
        binding('elements_prog_lib', name, 'Elements.' + name + ' Elements.lib')
        binding('elements_prog', prefix,
                'scribe . toWord256 . integerHash256 . ivHash . tagIv $ fromString "' + label + '"')
        if p.compact(hs_program('elements_prog', name)) != p.compact(hs_program('bitcoin_prog', name)):
            raise ValueError('Elements/Bitcoin shared builder payload tree differs: ' + name)
        port_name = 'literal_elements_build_tap' + stem
        port = p.definition(s['eltap_builders_port'], port_name)
        if re.findall(r'"([^"]*)"', port) != [label]:
            raise ValueError('Elements builder port tag differs: ' + name)
        shared = p.definition(s['bt_port'], 'literal_build_tap' + stem)
        if p.compact(port.replace('"' + label + '"', '"' + short + '"')) != p.compact(shared):
            raise ValueError('Elements builder shared literal Core tree differs: ' + name)

        helper = 'eltap_' + stem + '_exec'
        globals_key = 'eltap_' + stem + '_public'
        ints = 'el_tap' + stem + '_tag_ints'
        ready = 'el_sha_tap' + stem + '_tag_ok'
        n = len(label)
        definition(helper, ints, 'map Int.repr [' + '; '.join(str(ord(c)) for c in label) + ']')
        definition(helper, ready, '''
          forall i, (i < ''' + str(n) + ''')%nat ->
            Mem.load Mint8unsigned m (sha_symbol_block ''' + field + ''') (Z.of_nat i) =
              Some (Vint (nth i ''' + ints + ''' Int.zero))''')
        pre = 'el_sha_tap' + stem + '_pre'
        definition(globals_key, pre, 'sha_globals_ok m /\\ ' + ready + ' m')
        theorem = ('elements_build_tapleaf_simplicity_literal_local_spec' if stem == 'leaf'
                   else 'elements_build_tapbranch_literal_local_spec')
        function = 'f_simplicity_build_tap' + stem + ('_simplicity' if stem == 'leaf' else '')
        depth = 8 if stem == 'leaf' else 9
        statement = re.search(r'Theorem ' + theorem + r'\s*:(.*?)\bProof\.', s['eltap_builders_port'], re.S)
        expected = ('memcpy_model -> elements_sha_local_spec_pre ' + pre + ' ' + function +
                    ' (Word ' + str(depth) + ') (Word 8) (@' + port_name + ' Alg.CoreFunSem).')
        if not statement or p.compact(statement[1]) != p.compact(expected):
            raise ValueError('Elements builder whole C boundary differs: ' + theorem)


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
        "bitcoin_prog": REPO / "Haskell/Core/Simplicity/Programs/Bitcoin.hs",
        "bitcoin_catalog": REPO / "Haskell/Simplicity/Bitcoin/Jets.hs",
        "bitcoin_lib": REPO / "Haskell/Core/Simplicity/Programs/Bitcoin/Lib.hs",
        "bt_port": COQ / "C/jet_bitcoin_taproot_literal.v",
        "bt_jet": COQ / "C/jet_bitcoin_taproot_literal_local.v",
        "tapleaf_c": COQ / "C/jet_bitcoin_build_tapleaf_jet.v",
        "tapbranch_c": COQ / "C/jet_bitcoin_build_tapbranch_jet.v",
        "hs_ty": REPO / "Haskell/Core/Simplicity/Ty.hs",
        "bctx_port": COQ / "C/jet_bitcoin_ctx_hash_literal.v",
        "bctx_jet": COQ / "C/jet_bitcoin_ctx_hash_literal_local.v",
        "sighash": REPO / "Haskell/Simplicity/Bitcoin/Programs/SigHash.hs",
        "sighash_lib": REPO / "Haskell/Simplicity/Bitcoin/Programs/SigHash/Lib.hs",
        "hash_words_port": COQ / "C/jet_sha_hash_words_literal.v",
        "tappath_port": COQ / "C/jet_bitcoin_tappath_hash_literal.v",
        "array_port": COQ / "C/jet_bitcoin_array_hash_literal.v",
        "base_primitive": COQ / "Simplicity/Primitive/Bitcoin.v",
        "full_primitive": COQ / "C/jet_bitcoin_full_prim.v",
        "raw_program": COQ / "C/jet_bitcoin_raw_program.v",
        "raw_hash": COQ / "C/jet_bitcoin_hash_raw_literal.v",
        "raw_env": COQ / "C/jet_bitcoin_raw_env.v",
        "raw_jets": COQ / "C/jet_bitcoin_raw_jets.v",
        "tap_hash_port": COQ / "C/jet_bitcoin_tap_hash_literal.v",
        "inputs_port": COQ / "C/jet_bitcoin_inputs_hash_literal.v",
        "elems_loop": COQ / "C/jet_sha_hash_loop_gen.v",
        "single_input_port": COQ / "C/jet_bitcoin_input_hash_literal.v",
        "elements_array_port": COQ / "C/jet_elements_array_hash_literal.v",
        "elements_inputs_port": COQ / "C/jet_elements_inputs_hash_literal.v",
        "elements_tap_port": COQ / "C/jet_elements_tap_hash_literal.v",
        "elements_issuance_port": COQ / "C/jet_elements_issuance_proofs_hash_literal.v",
        "elements_nonce_port": COQ / "C/jet_elements_nonces_hash_literal.v",
        "elements_amounts_port": COQ / "C/jet_elements_amounts_hash_literal.v",
        "elements_composite_port": COQ / "C/jet_elements_composite_hash_literal.v",
        "elements_blinding_model": COQ / "C/jet_elements_blinding_entropy_spec.v",
        "elements_blinding_port": COQ / "C/jet_elements_blinding_entropy_literal.v",
        "one_spec": COQ / "C/jet_spec.v",
        "elements_status_model": COQ / "C/jet_elements_issuance_status_spec.v",
        "elements_status_exec": COQ / "C/jet_elements_issuance_status_exec.v",
        "elements_status_local": COQ / "C/jet_elements_issuance_status_local.v",
        "elements_status_tags": COQ / "C/jet_elements_issuance_jets.v",
        "elements_calc_port": COQ / "C/jet_elements_issuance_calc_literal.v",
        "elements_computed_port": COQ / "C/jet_elements_issuance_computed_literal.v",
        "elements_computed_exec": COQ / "C/jet_elements_issuance_computed_exec.v",
        "sha_original_tap_contract": COQ / "C/jet_sha_tapdata_jet.v",
        "eltap_linkage": COQ / "C/jet_elements_support_sha_linkage.v",
        "eltap_builders_port": COQ / "C/jet_elements_tap_builders_literal.v",
        "eltap_contract": COQ / "C/jet_elements_tap_contract.v",
        "eltap_leaf_exec": COQ / "C/jet_elements_make_tapleaf_exec.v",
        "eltap_branch_exec": COQ / "C/jet_elements_make_tapbranch_exec.v",
        "eltap_leaf_public": COQ / "C/jet_elements_build_tapleaf_jet.v",
        "eltap_branch_public": COQ / "C/jet_elements_build_tapbranch_jet.v",
        "elements_annex_exec": COQ / "C/jet_elements_annex_context_exec.v",
        "elements_annex_context_port": COQ / "C/jet_elements_annex_context_literal.v",
        "elements_issuance_program": REPO / "Haskell/Simplicity/Elements/Programs/Issuance.hs",
        "elements_issuance_lib": REPO / "Haskell/Simplicity/Elements/Programs/Issuance/Lib.hs",
        "elements_prog": REPO / "Haskell/Core/Simplicity/Programs/Elements.hs",
        "elements_prog_lib": REPO / "Haskell/Core/Simplicity/Programs/Elements/Lib.hs",
        "native_schnorr": REPO / "Haskell/Core/Simplicity/LibSecp256k1/Schnorr.hs",
        "native_spec": REPO / "Haskell/Core/Simplicity/LibSecp256k1/Spec.hs",
        "secp_types": REPO / "Haskell/Core/Simplicity/Ty/LibSecp256k1.hs",
        "elements_sighash": REPO / "Haskell/Simplicity/Elements/Programs/SigHash.hs",
        "elements_sighash_lib": REPO / "Haskell/Simplicity/Elements/Programs/SigHash/Lib.hs",
        "elements_catalog": REPO / "Haskell/Simplicity/Elements/Jets.hs",
        "elements_primitive_hs": REPO / "Haskell/Elements/Simplicity/Elements/Primitive.hs",
        "elements_primitive_coq": COQ / "C/jet_elements_prim.v",
        "forwhile": COQ / "C/jet_forWhile_spec.v",
        "btc_primitive": REPO / "Haskell/Bitcoin/Simplicity/Bitcoin/Primitive.hs",
        "ext_primitive": COQ / "C/jet_bitcoin_ext_prim.v",
        "btc_env_c": REPO / "C/bitcoin/env.c",
    }.items()}


def test():
    s = sources()
    check(s)
    context_add(s)
    buffer_finalize(s)
    tapdata(s)
    bitcoin_taproot(s)
    bitcoin_context_hash(s)
    primitive_hash_words(s)
    bitcoin_array_hashes(s)
    bitcoin_raw_hashes(s)
    bitcoin_tap_environment(s)
    bitcoin_input_hashes(s)
    bitcoin_single_input_hash(s)
    elements_array_hashes(s)
    elements_input_hashes(s)
    elements_tap_hashes(s)
    elements_issuance_proofs_hash(s)
    elements_nonce_hashes(s)
    elements_amount_hashes(s)
    elements_composite_hashes(s)
    elements_blinding_entropy_hash(s)
    elements_issuance_status(s)
    elements_issuance_computed(s)
    elements_annex_context(s)
    elements_tap_builders(s)
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
    builder_mutations = [
        ("bitcoin_catalog", "BuildTapbranch = Prog.buildTapbranch", "BuildTapbranch = Prog.buildTapleafSimplicity"),
        ("bitcoin_lib", "buildTapleafSimplicity = Bitcoin.buildTapleafSimplicity Bitcoin.lib", "buildTapleafSimplicity = Bitcoin.buildTapbranch Bitcoin.lib"),
        ("bitcoin_lib", "annexHash = Bitcoin.annexHash Bitcoin.libAssert", "annexHash = Bitcoin.outpointHash Bitcoin.libAssert"),
        ("bitcoin_prog", "lib = mkLib Sha256.lib", "lib = mkLib Sha256.libChanged"),
        ("bitcoin_prog", 'tagIv $ fromString "TapLeaf"', 'tagIv $ fromString "Tapleaf"'),
        ("bitcoin_prog", 'tagIv $ fromString "TapBranch"', 'tagIv $ fromString "TapLeaf"'),
        ("bitcoin_prog", "simplicityVersion = scribe . toWord8 $ 0xbe", "simplicityVersion = scribe . toWord8 $ 0xc0"),
        ("bitcoin_prog", "full_shift word16 word256", "full_shift word8 word256"),
        ("bitcoin_prog", "512+16+256", "512+8+256"),
        ("bitcoin_prog", "2^511 + 1024", "2^511 + 512"),
        ("bitcoin_prog", "cond iden (ih &&& oh)", "cond iden (oh &&& ih)"),
        ("bitcoin_prog", "lt word256 &&& iden", "lt word256 &&& (ih &&& oh)"),
        ("hs_types", "Left v -> Left (vectorPromote v)", "Left v -> Left v"),
        ("hs_word", "go (Left v) = full_right_shift1", "go (Left v) = full_left_shift1"),
        ("bt_port", "String.length tag", "String.length tag + 1"),
        ("bt_port", "literal_short_tag_digest tag ++ literal_short_tag_digest tag", "literal_short_tag_bytes tag ++ literal_short_tag_digest tag"),
        ("bt_port", "haskell_integer_hash256 (hash256_to_bytelist", "haskell_integer_hash256 (rev (hash256_to_bytelist"),
        ("bt_port", "@Word.full_right_shift1 (Word 4) 4 term", "@Word.full_right_shift1 (Word 4) 3 term"),
        ("bt_port", "haskell_to_word 3 32", "haskell_to_word 3 33"),
        ("bt_port", "haskell_to_word 4 0x8000", "haskell_to_word 4 0x0080"),
        ("bt_port", "@lt_word_spec term 8", "@lt_word_spec term 7"),
        ("bt_port", "Bit.cond iden (I H &&& O H)", "Bit.cond iden (O H &&& I H)"),
        ("bt_port", "@literal_sha_256_block term", "iden"),
        ("tapleaf_c", "sha_globals_ok m /\\ sha_tapleaf_tag_ok m", "sha_globals_ok m"),
        ("tapbranch_c", "sha_globals_ok m /\\ sha_tapbranch_tag_ok m", "sha_globals_ok m"),
        ("bt_jet", "memcpy_model ->", "False -> memcpy_model ->"),
        ("bt_jet", "sha_jet_local_spec_pre sha_tapbranch_pre", "sha_jet_local_spec_pre sha_tapleaf_pre"),
    ]
    for key, old, new in builder_mutations:
        if old not in s[key]:
            raise ValueError("inactive Bitcoin builder mutation: " + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            bitcoin_taproot(changed)
        except ValueError:
            continue
        raise ValueError("Bitcoin builder source mutation escaped: " + old)
    print("Bitcoin TapLeaf/TapBranch complete canonical trees, tags and C boundaries match;", len(builder_mutations), "mutations rejected")
    context_hash_mutations = [
        ("bitcoin_catalog", "OutpointHash = Prog.outpointHash", "OutpointHash = Prog.annexHash"),
        ("bitcoin_prog", "outpointHash = (oh &&& ioh", "outpointHash = (oh &&& iih"),
        ("bitcoin_prog", "ctx8Add32) &&& iih >>> ctx8Add4", "ctx8Add32) &&& iih >>> ctx8Add32"),
        ("bitcoin_prog", "annexHash = ih &&& oh", "annexHash = oh &&& ih"),
        ("bitcoin_prog", "take (zero word8)", "take (zero word16)"),
        ("bitcoin_prog", "scribe (toWord8 0x01)", "scribe (toWord8 0x00)"),
        ("bitcoin_prog", "ctx8Add4 = ctx8Addn vector4", "ctx8Add4 = ctx8Addn vector8"),
        ("hs_ty", "type S a = Either () a", "type S a = Either a ()"),
        ("bctx_port", "@literal_ctx8_addn 5 term", "@literal_ctx8_addn 4 term"),
        ("bctx_port", "I H &&& O H >>> case", "O H &&& I H >>> case"),
        ("bctx_port", "haskell_to_word 3 0x01", "haskell_to_word 3 0x00"),
        ("bctx_jet", "memcpy_model ->", "False -> memcpy_model ->"),
        ("bctx_jet", "sha_jet_partial_local_spec", "sha_jet_local_spec"),
        ("bctx_jet", "f_simplicity_bitcoin_outpoint_hash", "f_simplicity_bitcoin_annex_hash"),
    ]
    for key, old, new in context_hash_mutations:
        if old not in s[key]:
            raise ValueError("inactive Bitcoin context hash mutation: " + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            bitcoin_context_hash(changed)
        except ValueError:
            continue
        raise ValueError("Bitcoin context hash source mutation escaped: " + old)
    print("Bitcoin outpoint/annex canonical assertion trees and whole C boundaries match;", len(context_hash_mutations), "mutations rejected")
    primitive_hash_mutations = [
        ("bitcoin_catalog", "TappathHash = SigHash.tappathHash", "TappathHash = SigHash.tapleafHash"),
        ("sighash_lib", "tappathHash = SigHash.tappathHash SigHash.lib", "tappathHash = SigHash.tapleafHash SigHash.lib"),
        ("sighash", "lib = mkLib Sha256.lib Sha256.libAssert Transaction.lib", "lib = mkLib Sha256.lib Sha256.libAssert Transaction.libChanged"),
        ("sighash", "hashWord256s8 (drop (primitive Tappath))", "hashWord256s32 (drop (primitive Tappath))"),
        ("sighash", "hashWord256s8 = hashWord256s word8", "hashWord256s8 = hashWord256s word32"),
        ("sighash", "hashLoop256 = Sha256.hashLoop vector32", "hashLoop256 = Sha256.hashLoop vector16"),
        ("hs", "ctx8Addv = ctx8Addn libAssert v", "ctx8Addv = ctx8Addn libAssert vChanged"),
        ("hs", "take array &&& ih", "take array &&& oh"),
        ("hs", "injl ih", "injl oh"),
        ("hs", "forWhile w body >>> copair iden iden", "forWhile w body >>> copair iden unit"),
        ("hs_word", "monobody = body", "monobody = bodyChanged"),
        ("hs_word", "forWhile n (forWhile n ((oooh", "forWhile n (forWhile n ((ooih"),
        ("hash_words_port", "@literal_ctx8_addn k term", "@literal_ctx8_addn (S k) term"),
        ("hash_words_port", "case (injl (I H))", "case (injl (O H))"),
        ("hash_words_port", "copair iden iden", "copair unit iden"),
        ("hash_words_port", ">>> @literal_ctx8_finalize term", ">>> iden"),
        ("hash_words_port", "0x6a09e667bb67ae85", "0x6a09e667bb67ae84"),
        ("tappath_port", "@literal_sha_hash_words 5 3 term", "@literal_sha_hash_words 5 5 term"),
        ("tappath_port", "BitcoinFull.Ext BitcoinExt.Tappath", "BitcoinFull.Ext BitcoinExt.InternalKey"),
        ("tappath_port", "application_jet_local_spec_sep", "False -> application_jet_local_spec_sep"),
        ("tappath_port", "(tappath_of e)) 8 40 176", "(tappath_of e)) 8 72 176"),
        ("btc_primitive", "fromInteger . fromWord8", "fromInteger . fromWord32"),
        ("btc_primitive", "cast Nothing = Left ()", "cast Nothing = Right ()"),
        ("ext_primitive", "(length extTappath <= 128)%nat", "(length extTappath <= 64)%nat"),
        ("btc_env_c", "if (128 < rawEnv->pathLen)", "if (64 < rawEnv->pathLen)"),
    ]
    for key, old, new in primitive_hash_mutations:
        if old not in s[key]:
            raise ValueError("inactive primitive hash mutation: " + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            primitive_hash_words(changed)
        except ValueError:
            continue
        raise ValueError("primitive hash source mutation escaped: " + old)
    print("Primitive-bearing hash loop, TappathHash program/domain and whole C boundary match;", len(primitive_hash_mutations), "mutations rejected")
    array_hash_mutations = [
        ("sighash", "hashWord256s32 = hashWord256s word32", "hashWord256s32 = hashWord256s word8"),
        ("sighash", "Sha256.hashLoop vector4 word32 array", "Sha256.hashLoop vector8 word32 array"),
        ("sighash", "hashWord32s array = iden", "hashWord32s array = unit"),
        ("array_port", "@literal_sha_hash_words k 5 term", "@literal_sha_hash_words k 3 term"),
        ("array_port", "@PF.Combinators.prim _ _ alg p", "@PF.Combinators.prim _ _ alg changed"),
        ("btc_primitive", "atInput f = cast . fmap f . lookupInput", "atInput f = cast . fmap f . lookupOutput"),
        ("btc_primitive", "atOutput f = cast . fmap f . lookupOutput", "atOutput f = cast . fmap f . lookupInput"),
        ("btc_primitive", "encodeHash . bslHash . sigTxiScript)", "encodeHash . bslHash . sigTxiScriptSig)"),
        ("btc_primitive", "encodeHash . bslHash . sigTxiScriptSig)", "encodeHash . bslHash . sigTxiScript)"),
        ("btc_primitive", "toWord32 . toInteger . sigTxiSequence)", "toWord32 . toInteger . sigTxiValue)"),
        ("base_primitive", "| InputSequence => atInput (fun txi => fromZ (Int.unsigned (sigTxiSequence txi)))", "| InputSequence => atInput (fun txi => fromZ (Int.signed (sigTxiSequence txi)))"),
        ("base_primitive", "byteStringHash (txoScript txout)", "byteStringHash []"),
        ("ext_primitive", "nth_error (extInScriptHash e)", "nth_error (extInScriptSigHash e)"),
        ("full_primitive", "Bitcoin.sem q a (extBase e)", "Bitcoin.sem q a other"),
    ]
    for tag, hs_name, stem, prim in [
        ("OutputScriptsHash", "outputScriptsHash", "output_scripts", "OutputScriptHash"),
        ("InputScriptsHash", "inputScriptsHash", "input_scripts", "InputScriptHash"),
        ("InputSequencesHash", "inputSequencesHash", "input_sequences", "InputSequence"),
        ("InputScriptSigsHash", "inputScriptSigsHash", "input_script_sigs", "InputScriptSigHash"),
    ]:
        array_hash_mutations += [
            ("bitcoin_catalog", f"specificationSigHash {tag} = SigHash.{hs_name}", f"specificationSigHash {tag} = SigHash.tappathHash"),
            ("sighash_lib", f"{hs_name} = SigHash.{hs_name} SigHash.lib", f"{hs_name} = SigHash.tappathHash SigHash.lib"),
            ("sighash", f"(drop (primitive {prim}))", f"(take (primitive {prim}))"),
            ("array_port", f"Bitcoin.{prim}" if prim in {"OutputScriptHash", "InputSequence"} else f"BitcoinExt.{prim}", "BitcoinExt.Tappath"),
            ("array_port", f"Theorem bitcoin_{stem}_hash_literal_local_spec :", f"Theorem bitcoin_{stem}_hash_literal_local_spec : False ->"),
        ]
    for key, old, new in array_hash_mutations:
        if old not in s[key]:
            raise ValueError("inactive Bitcoin array hash mutation: " + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            bitcoin_array_hashes(changed)
        except ValueError:
            continue
        raise ValueError("Bitcoin array hash source mutation escaped: " + old)
    print("Four Bitcoin array hash programs, primitive projections and whole C boundaries match;", len(array_hash_mutations), "mutations rejected")
    raw_hash_mutations = [
        ("raw_program", "Bitcoin.sem q a (raw_base environment)", "Bitcoin.sem q a changed"),
        ("raw_program", "raw_ext_sem q a environment", "BitcoinExt.sem q a environment"),
        ("raw_program", "(@PF.Mixin _ (@raw_full_sem))", "(@PF.Mixin _ (@changed_sem))"),
        ("raw_program", "option_Monad_Zero", "changed_Monad_Zero"),
        ("raw_program", "f a (project_raw_environment environment Hpath) = g a environment", "True"),
        ("raw_jets", "(length (raw_tap_path logical) <= 128)%nat", "(length (raw_tap_path logical) <= 64)%nat"),
        ("raw_jets", "rep m env (project_raw_environment logical Hpath) fp", "False"),
        ("raw_env", "raw_base : Bitcoin.environment", "raw_base : changed_environment"),
        ("raw_env", "byteStringHash (raw_redeemed_script i)", "byteStringHash (raw_script_sig i)"),
        ("raw_env", "byteStringHash (raw_script_sig i)", "byteStringHash (raw_redeemed_script i)"),
        ("raw_env", "byteStringHash (raw_redeemed_script data)", "byteStringHash (raw_script_sig data)"),
        ("raw_env", "byteStringHash (raw_script_sig data)", "byteStringHash (raw_redeemed_script data)"),
    ]
    for stem in ["output_scripts", "input_scripts", "input_sequences", "input_script_sigs", "tappath"]:
        declaration = f"Theorem bitcoin_{stem}_hash_raw_literal_local_spec :"
        raw_hash_mutations += [
            ("raw_hash", declaration, declaration + " False ->"),
            ("raw_hash", f"@literal_bitcoin_{stem}_hash raw_fullalg", f"@literal_bitcoin_{stem}_hash fullalg"),
        ]
    for key, old, new in raw_hash_mutations:
        if old not in s[key]:
            raise ValueError("inactive raw Bitcoin hash mutation: " + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            bitcoin_raw_hashes(changed)
        except ValueError:
            continue
        raise ValueError("raw Bitcoin hash source mutation escaped: " + old)
    print("Raw primitive/whole-program interpretation and five whole C boundaries match;", len(raw_hash_mutations), "mutations rejected")
    tap_environment_mutations = [
        ("hs", "ctx8InitTag tag = buffer63Empty", "ctx8InitTag tag = unit"),
        ("hs", "prefix = scribe . toWord256", "prefix = scribe . toWord128"),
        ("sighash", 'Sha256.ctx8InitTag "TapLeaf"', 'Sha256.ctx8InitTag "TapBranch"'),
        ("sighash", "primitive TapleafVersion &&& scribe", "primitive InternalKey &&& scribe"),
        ("sighash", "tappathHash &&& primitive InternalKey", "tapleafHash &&& primitive InternalKey"),
        ("tap_hash_port", "@literal_tapdata_one64 term", "@Word.zero 6 term"),
        ("tap_hash_port", 'literal_short_tag_prefix "TapLeaf"%string', 'literal_short_tag_prefix "TapBranch"%string'),
        ("tap_hash_port", "haskell_to_word 3 32", "haskell_to_word 3 33"),
        ("tap_hash_port", "@literal_ctx8_addn 1 term", "@literal_ctx8_addn 2 term"),
        ("tap_hash_port", "@literal_ctx8_addn 6 term", "@literal_ctx8_addn 5 term"),
        ("tap_hash_port", "@literal_bitcoin_tappath_hash alg", "@literal_bitcoin_tapleaf_hash alg"),
        ("tap_hash_port", "@AC.comp _ _ _ core", "@AC.pair _ _ _ core"),
        ("tap_hash_port", "BitcoinFull.Base Bitcoin.ScriptCMR", "BitcoinFull.Ext BitcoinExt.InternalKey"),
        ("tap_hash_port", "BitcoinFull.Ext BitcoinExt.InternalKey", "BitcoinFull.Base Bitcoin.ScriptCMR"),
        ("tap_hash_port", "(hash_getter_rep tapleaf_hash_of 8 8 176)", "(hash_getter_rep tapleaf_hash_of 8 40 176)"),
        ("btc_primitive", "toWord8 . toInteger . tapleafVersion", "toWord8 . toInteger . tapInternalKey"),
        ("btc_primitive", "integerHash256 . tapScriptCMR", "integerHash256 . tapInternalKey"),
        ("raw_env", "Byte.unsigned (raw_leaf_version environment)", "0"),
    ]
    for stem in ["tapleaf", "tap_env"]:
        for suffix in ["literal_local", "raw_literal_local"]:
            declaration = f"Theorem bitcoin_{stem}_hash_{suffix}_spec :"
            tap_environment_mutations.append(("tap_hash_port", declaration, declaration + " False ->"))
    for key, old, new in tap_environment_mutations:
        if old not in s[key]:
            raise ValueError("inactive tap environment mutation: " + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            bitcoin_tap_environment(changed)
        except ValueError:
            continue
        raise ValueError("tap environment source mutation escaped: " + old)
    print("Tapleaf/tapEnv whole canonical trees, tag initialization and four C boundaries match;", len(tap_environment_mutations), "mutations rejected")
    input_hash_mutations = [
        ('sighash', 'primitive InputPrevOutpoint', 'primitive InputSequence'),
        ('sighash', 'primitive InputAnnexHash)) &&& ih', 'primitive InputScriptHash)) &&& ih'),
        ('sighash', 'forWhile word32 body', 'forWhile word8 body'),
        ('sighash', 'match (injl ih) (injr (ih &&& oh >>> outpointHash))', 'match (injr ih) (injr (ih &&& oh >>> outpointHash))'),
        ('sighash', 'match (injl ih) (injr (ih &&& oh >>> annexHash))', 'match (injl ih) (injl (ih &&& oh >>> annexHash))'),
        ('sighash', 'inputOutpointsHash &&& inputSequencesHash', 'inputSequencesHash &&& inputOutpointsHash'),
        ('sighash', '&&& inputAnnexesHash >>> ctx8Addn vector32', '&&& inputAnnexesHash >>> ctx8Addn vector64'),
        ('inputs_port', '@literal_sha_hash_ctx_init core', '@Word.zero 8 core'),
        ('inputs_port', '@for_while_program w Ty.Unit', '@for_while_program 3 Ty.Unit'),
        ('inputs_port', '@literal_ctx8_finalize term', '@literal_ctx8_addn 5 term'),
        ('inputs_port', '(fun term => @literal_bitcoin_outpoint_hash term) 5', '(fun term => @literal_bitcoin_outpoint_hash term) 3'),
        ('inputs_port', 'BitcoinFull.Base Bitcoin.InputPrevOutpoint', 'BitcoinFull.Base Bitcoin.InputSequence'),
        ('inputs_port', 'BitcoinFull.Ext BitcoinExt.InputAnnexHash', 'BitcoinFull.Ext BitcoinExt.InputScriptHash'),
        ('inputs_port', '@literal_ctx8_addn 6 term', '@literal_ctx8_addn 5 term'),
        ('inputs_port', '@literal_bitcoin_input_sequences_hash alg', '@literal_bitcoin_input_scripts_hash alg'),
        ('elems_loop', '@AC.injl _ _ _ core (@AC.drop _ _ _ core (@AC.iden _ core))', '@AC.injr _ _ _ core (@AC.drop _ _ _ core (@AC.iden _ core))'),
        ('elems_loop', '@AC.take _ _ _ core array', '@AC.drop _ _ _ core array'),
        ('btc_primitive', 'cast . fmap (encodeHash . bslHash) . sigTxiAnnex', 'cast . fmap (encodeHash . bslHash) . sigTxiScript'),
        ('ext_primitive', '| Some None => inr (inl tt)', '| Some None => inl tt'),
        ('raw_env', 'extInAnnexHash := map (fun i => option_map byteStringHash (raw_annex i))', 'extInAnnexHash := map (fun i => None)'),
        ('raw_env', '| Some data => inr (cast (option_map (fun bytes => from_hash256 (byteStringHash bytes)) (raw_annex data)))', '| Some data => inl tt'),
    ]
    for tag, hs_name, stem in [('InputOutpointsHash', 'inputOutpointsHash', 'input_outpoints'),
                              ('InputAnnexesHash', 'inputAnnexesHash', 'input_annexes'),
                              ('InputsHash', 'inputsHash', 'inputs')]:
        input_hash_mutations.extend([
            ('bitcoin_catalog', 'specificationSigHash ' + tag + ' = SigHash.' + hs_name,
             'specificationSigHash ' + tag + ' = SigHash.tapleafHash'),
            ('sighash_lib', hs_name + ' = SigHash.' + hs_name + ' SigHash.lib',
             hs_name + ' = SigHash.tapleafHash SigHash.lib'),
        ])
        for suffix in ['literal_local', 'raw_literal_local']:
            declaration = f'Theorem bitcoin_{stem}_hash_{suffix}_spec :'
            input_hash_mutations.append(('inputs_port', declaration, declaration + ' False ->'))
    for key, old, new in input_hash_mutations:
        if old not in s[key]:
            raise ValueError('inactive input hash mutation: ' + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            bitcoin_input_hashes(changed)
        except ValueError:
            continue
        raise ValueError('input hash mutation escaped: ' + old)
    print('Canonical input hash trees and six complete C boundaries match;', len(input_hash_mutations), 'mutations rejected')
    single_input_mutations = [
        ('bitcoin_catalog', 'specificationSigHash InputHash = SigHash.inputHash', 'specificationSigHash InputHash = SigHash.inputsHash'),
        ('sighash_lib', 'inputHash = SigHash.inputHash SigHash.lib', 'inputHash = SigHash.inputsHash SigHash.lib'),
        ('sighash', 'ctx8Add4 = ctx8Addn vector4', 'ctx8Add4 = ctx8Addn vector8'),
        ('sighash', 'inputHash = (primitive InputPrevOutpoint', 'inputHash = (primitive InputValue'),
        ('sighash', '(drop . take . assert $ iden)', '(drop . drop . assert $ iden)'),
        ('sighash', '(drop . drop . assert $ iden)', '(drop . take . assert $ iden)'),
        ('sighash', 'injr ((((unit >>> ctx8Init) &&& oh >>> outpointHash)', 'injl ((((unit >>> ctx8Init) &&& oh >>> outpointHash)'),
        ('single_input_port', '(iden &&& unit)', '(unit &&& iden)'),
        ('single_input_port', 'term assertion_cmr_fail0', 'term assertion_hash0'),
        ('single_input_port', '@AC.comp _ _ _ core', '@AC.pair _ _ _ core'),
        ('single_input_port', '@AC.case _ _ _ _ core', '@AC.pair _ _ _ core'),
        ('single_input_port', '@AC.injl _ _ _ core', '@AC.injr _ _ _ core'),
        ('single_input_port', 'BitcoinFull.Base Bitcoin.InputPrevOutpoint', 'BitcoinFull.Base Bitcoin.InputSequence'),
        ('single_input_port', 'BitcoinFull.Base Bitcoin.InputSequence', 'BitcoinFull.Ext BitcoinExt.InputAnnexHash'),
        ('single_input_port', 'BitcoinFull.Ext BitcoinExt.InputAnnexHash', 'BitcoinFull.Ext BitcoinExt.InputScriptHash'),
        ('single_input_port', '@literal_sha_hash_ctx_init core', '@AC.unit _ core'),
        ('single_input_port', '@literal_ctx8_addn 2 term', '@literal_ctx8_addn 3 term'),
        ('single_input_port', '@literal_bitcoin_assert_iden (Word 5) term', '@literal_bitcoin_assert_iden (Word 6) term'),
        ('single_input_port', '@literal_bitcoin_assert_iden (Ty.Sum Ty.Unit (Word 8)) term', '@literal_bitcoin_assert_iden (Word 8) term'),
        ('single_input_port', '@literal_bitcoin_outpoint_hash term', '@literal_bitcoin_annex_hash term'),
        ('single_input_port', '@literal_ctx8_finalize term', '@literal_ctx8_addn 5 term'),
        ('single_input_port', '(raw_env_rep input_hash_rep)', 'input_hash_rep'),
        ('single_input_port', 'f_simplicity_bitcoin_input_hash sha_ge', 'f_simplicity_bitcoin_input_hash bitcoin_ge'),
    ]
    for suffix in ['literal_local', 'raw_literal_local']:
        declaration = f'Theorem bitcoin_input_hash_{suffix}_spec : memcpy_model ->'
        single_input_mutations.extend([
            ('single_input_port', declaration, declaration.replace('memcpy_model', 'False')),
            ('single_input_port', declaration, declaration.replace('memcpy_model ->', '')),
        ])
    for key, old, new in single_input_mutations:
        if old not in s[key]:
            raise ValueError('inactive single-input mutation: ' + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            bitcoin_single_input_hash(changed)
        except ValueError:
            continue
        raise ValueError('single-input mutation escaped: ' + old)
    print('Canonical single-input hash and two complete conditional C contracts match;', len(single_input_mutations), 'mutations rejected')
    elements_array_mutations = [
        ('elements_array_port', '@literal_sha_hash_words k w term Ty.Unit', '@literal_sha_hash_words k 3 term Ty.Unit'),
        ('elements_sighash', 'hashWord256s32 = hashWord256s word32', 'hashWord256s32 = hashWord256s word8'),
        ('elements_sighash', 'hashWord256s8 = hashWord256s word8', 'hashWord256s8 = hashWord256s word32'),
        ('elements_sighash', 'Sha256.hashLoop vector4 word32 array', 'Sha256.hashLoop vector32 word32 array'),
        ('elements_primitive_coq', '| Explicit _ => []', '| Explicit _ => [Byte.zero]'),
        ('elements_primitive_coq', '| Confidential _ p => p', '| Confidential _ p => []'),
        ('elements_primitive_coq', '| InputSequence => atInput (fun txi => fromZ (Int.unsigned (sigTxiSequence txi)))', '| InputSequence => atInput (fun txi => fromZ (Int.signed (sigTxiSequence txi)))'),
        ('elements_primitive_hs', 'to txoAmount.under amount.prf_', 'to txoAsset.under asset.prf_'),
        ('elements_primitive_hs', 'interpret Tappath = return . cast . fmap encodeHash', 'interpret Tappath = return . cast . fmap encodeKey'),
    ]
    for tag, hs_name, stem, primitive, k, w, ptr, offset, size in [
        ('OutputScriptsHash', 'outputScriptsHash', 'output_scripts', 'OutputScriptHash', 5, 5, 0, 88, 760),
        ('OutputRangeProofsHash', 'outputRangeProofsHash', 'output_range_proofs', 'OutputRangeProof', 5, 5, 0, 120, 760),
        ('OutputSurjectionProofsHash', 'outputSurjectionProofsHash', 'output_surjection_proofs', 'OutputSurjectionProof', 5, 5, 0, 152, 760),
        ('InputScriptsHash', 'inputScriptsHash', 'input_scripts', 'InputScriptHash', 5, 5, 0, 280, 760),
        ('InputSequencesHash', 'inputSequencesHash', 'input_sequences', 'InputSequence', 2, 5, 0, 344, 760),
        ('InputScriptSigsHash', 'inputScriptSigsHash', 'input_script_sigs', 'InputScriptSigHash', 5, 5, 0, 408, 760),
        ('TappathHash', 'tappathHash', 'tappath', 'Tappath', 5, 3, 8, 40, 176),
    ]:
        helper = 'hashWord32s' if k == 2 else ('hashWord256s8' if w == 3 else 'hashWord256s32')
        declaration = f'Theorem elements_{stem}_hash_literal_local_spec :'
        elements_array_mutations.extend([
            ('elements_catalog', f'specificationSigHash {tag} = SigHash.{hs_name}', f'specificationSigHash {tag} = SigHash.tapleafHash'),
            ('elements_sighash_lib', f'{hs_name} = SigHash.{hs_name} SigHash.lib', f'{hs_name} = SigHash.tapleafHash SigHash.lib'),
            ('elements_sighash', f'{hs_name} = {helper} (drop (primitive {primitive}))', f'{hs_name} = {helper} (drop (primitive InternalKey))'),
            ('elements_array_port', f'@literal_elements_array_hash {k} {w} Elements.{primitive} alg', f'@literal_elements_array_hash {k} 2 Elements.{primitive} alg'),
            ('elements_array_port', declaration, declaration + ' False ->'),
            ('elements_array_port', f'(elements_{stem}_words e)) {ptr} {offset} {size}', f'(elements_{stem}_words e)) {ptr} {offset + 8} {size}'),
        ])
    for key, old, new in elements_array_mutations:
        if old not in s[key]:
            raise ValueError('inactive Elements array mutation: ' + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            elements_array_hashes(changed)
        except ValueError:
            continue
        raise ValueError('Elements array mutation escaped: ' + old)
    print('Seven Elements array hash trees, raw primitives and whole C contracts match;', len(elements_array_mutations), 'mutations rejected')


    elements_inputs_mutations = [
        ('elements_sighash', 'body = take (drop (primitive InputPegin))', 'body = take (drop (primitive InputAnnexHash))'),
        ('elements_sighash', 'take (drop (primitive InputPrevOutpoint)) &&& ih', 'take (drop (primitive InputSequence)) &&& ih'),
        ('elements_sighash', 'match (injl iih) (ioh &&&', 'match (injr iih) (ioh &&&'),
        ('elements_sighash', 'match (injl iih) (injr (iih &&& (ioh &&& oh) >>> outpointHash))', 'match (injr iih) (injr (iih &&& (ioh &&& oh) >>> outpointHash))'),
        ('elements_prog', '((oh &&& ioh >>> annexHash) &&& iioh >>> ctx8Add32)', '((oh &&& ioh >>> annexHash) &&& iiih >>> ctx8Add32)'),
        ('elements_prog', 'ctx8Add4 = ctx8Addn vector4', 'ctx8Add4 = ctx8Addn vector8'),
        ('elements_prog', 'take (zero word8) >>> ctx8Add1', 'take (zero word16) >>> ctx8Add1', 2),
        ('elements_prog_lib', 'outpointHash = Elements.outpointHash Elements.libAssert', 'outpointHash = Elements.annexHash Elements.libAssert'),
        ('elements_prog_lib', 'annexHash = Elements.annexHash Elements.libAssert', 'annexHash = Elements.outpointHash Elements.libAssert'),
        ('elements_inputs_port', '@literal_bitcoin_annex_hash term', '@literal_bitcoin_outpoint_hash term'),
        ('elements_inputs_port', '@literal_ctx8_addn 5 term', '@literal_ctx8_addn 6 term'),
        ('elements_inputs_port', '@EFP.Combinators.prim _ _ alg Elements.InputPegin', '@EFP.Combinators.prim _ _ alg Elements.InputAnnexHash'),
        ('elements_inputs_port', '@EFP.Combinators.prim _ _ alg Elements.InputPrevOutpoint', '@EFP.Combinators.prim _ _ alg Elements.InputSequence'),
        ('elements_inputs_port', '@for_while_program 5 _ _ _ core', '@for_while_program 3 _ _ _ core'),
        ('elements_inputs_port', '@for_while_program w Ty.Unit', '@for_while_program 3 Ty.Unit'),
        ('elements_inputs_port', '@literal_sha_hash_ctx_init core', '@AC.unit _ core'),
        ('elements_inputs_port', '@literal_ctx8_finalize term', '@literal_ctx8_addn 5 term'),
        ('elements_inputs_port', '(fun term => @literal_bitcoin_annex_hash term) 5 term', '(fun term => @literal_bitcoin_annex_hash term) 3 term'),
        ('elements_inputs_port', '@literal_elements_input_sequences_hash alg', '@literal_elements_input_scripts_hash alg'),
        ('elements_primitive_hs', 'interpret InputPegin = return . (atInput $ cast . fmap encodeHash . sigTxiPegin)', 'interpret InputPegin = return . (atInput $ cast . fmap encodeHash . sigTxiAnnex)'),
        ('elements_primitive_coq', '| InputPegin => atInput (fun txi => cast (option_map encodeHash (sigTxiPegin txi)))', '| InputPegin => atInput (fun txi => inl tt)'),
        ('elements_primitive_coq', '| InputAnnexHash => atInput (fun txi =>', '| InputAnnexHash => atOutput (fun txi =>'),
    ]
    stop_branch = '@AC.injl _ _ _ core (AC.drop (AC.drop AC.iden))'
    for occurrence in [1, 2]:
        elements_inputs_mutations.append(('elements_inputs_port', stop_branch,
                                         '@AC.injr _ _ _ core (AC.drop (AC.drop AC.iden))', occurrence))
    for tag, hs_name, stem, offset in [
        ('InputOutpointsHash', 'inputOutpointsHash', 'input_outpoints', 216),
        ('InputAnnexesHash', 'inputAnnexesHash', 'input_annexes', 376),
        ('InputsHash', 'inputsHash', 'inputs', 440),
    ]:
        declaration = f'Theorem elements_{stem}_hash_literal_local_spec :'
        elements_inputs_mutations.extend([
            ('elements_catalog', f'specificationSigHash {tag} = SigHash.{hs_name}', f'specificationSigHash {tag} = SigHash.tapleafHash'),
            ('elements_sighash_lib', f'{hs_name} = SigHash.{hs_name} SigHash.lib', f'{hs_name} = SigHash.tapleafHash SigHash.lib'),
            ('elements_inputs_port', declaration, declaration + ' False ->'),
            ('elements_inputs_port', f'hash_getter_rep elements_{stem}_hash_of 0 {offset} 760', f'hash_getter_rep elements_{stem}_hash_of 0 {offset + 8} 760'),
        ])
    for mutation in elements_inputs_mutations:
        key, old, new = mutation[:3]
        occurrence = mutation[3] if len(mutation) == 4 else 1
        start = -1
        for _ in range(occurrence):
            start = s[key].find(old, start + 1)
            if start < 0:
                raise ValueError('inactive Elements input mutation: ' + old)
        changed = dict(s)
        changed[key] = s[key][:start] + new + s[key][start + len(old):]
        try:
            elements_input_hashes(changed)
        except ValueError:
            continue
        raise ValueError('Elements input mutation escaped: ' + old)
    print('Elements outpoint/annex/input trees and three whole C boundaries match;', len(elements_inputs_mutations), 'mutations rejected')
    elements_tap_mutations = [
        ('elements_sighash', 'Sha256.ctx8InitTag "TapLeaf/elements"', 'Sha256.ctx8InitTag "TapLeaf /elements"'),
        ('elements_sighash', 'Sha256.ctx8InitTag "TapLeaf/elements"', 'Sha256.ctx8InitTag "TapLeaf/elements "'),
        ('elements_sighash', 'Sha256.ctx8InitTag "TapLeaf/elements"', 'Sha256.ctx8InitTag "TapLeaf"'),
        ('elements_sighash', 'tappathHash &&& primitive InternalKey', 'tapleafHash &&& primitive InternalKey'),
        ('elements_tap_port', 'literal_short_tag_prefix "TapLeaf/elements"%string', 'literal_short_tag_prefix "TapLeaf /elements"%string', 2),
        ('elements_tap_port', 'literal_short_tag_prefix "TapLeaf/elements"%string', 'literal_short_tag_prefix "TapLeaf/elements "%string', 2),
        ('elements_tap_port', '@literal_sha_tag_ctx (literal_short_tag_prefix "TapLeaf/elements"%string) core', '@literal_sha_tag_ctx (literal_short_tag_prefix "TapLeaf"%string) core'),
        ('elements_tap_port', 'haskell_to_word 3 32', 'haskell_to_word 3 33'),
        ('elements_tap_port', '@literal_ctx8_addn 1 term', '@literal_ctx8_addn 2 term'),
        ('elements_tap_port', '@literal_ctx8_addn 6 term', '@literal_ctx8_addn 5 term'),
        ('elements_tap_port', '@literal_elements_tappath_hash alg', '@literal_elements_tapleaf_hash alg'),
        ('elements_tap_port', '@AC.comp _ _ _ core', '@AC.pair _ _ _ core'),
        ('elements_tap_port', 'Elements.ScriptCMR', 'Elements.InternalKey'),
        ('elements_tap_port', 'Elements.InternalKey', 'Elements.ScriptCMR'),
        ('elements_primitive_hs', 'encodeKey (Schnorr.PubKey x) = toWord256 . toInteger $ x', 'encodeKey (Schnorr.PubKey x) = toWord256 . Schnorr.fe_repr $ x'),
        ('elements_primitive_hs', 'toWord8 . toInteger . tapleafVersion', 'toWord8 . toInteger . tapInternalKey'),
        ('elements_primitive_coq', '| InternalKey => fun _ => Some (from_hash256 (tapInternalKey (envTap e)))', '| InternalKey => fun _ => Some (from_hash256 (tapScriptCMR (envTap e)))'),
        ('native_schnorr', 'data PubKey = PubKey Word256', 'data PubKey = PubKey FE'),
        ('native_spec', 'import Simplicity.LibSecp256k1.Schnorr', 'import Other.Schnorr'),
        ('native_spec', 'PubKey(..), pubkey_unpack', 'FE(..), pubkey_unpack'),
        ('native_spec', 'import Simplicity.Word', 'import Simplicity.Word\ndata PubKey = AlternateKey Word256'),
        ('secp_types', 'type PubKey = Word256', 'type PubKey = FE'),
    ]
    for tag, hs_name, stem, offset in [('TapleafHash', 'tapleafHash', 'tapleaf', 8), ('TapEnvHash', 'tapEnvHash', 'tap_env', 72)]:
        declaration = f'Theorem elements_{stem}_hash_literal_local_spec :'
        elements_tap_mutations.extend([
            ('elements_catalog', f'specificationSigHash {tag} = SigHash.{hs_name}', f'specificationSigHash {tag} = SigHash.tappathHash'),
            ('elements_sighash_lib', f'{hs_name} = SigHash.{hs_name} SigHash.lib', f'{hs_name} = SigHash.tappathHash SigHash.lib'),
            ('elements_tap_port', declaration, declaration + ' False ->'),
            ('elements_tap_port', declaration, declaration + ' memcpy_model ->'),
            ('elements_tap_port', f'hash_getter_rep elements_{stem}_hash_of 8 {offset} 176', f'hash_getter_rep elements_{stem}_hash_of 8 {offset + 8} 176'),
        ])
    for mutation in elements_tap_mutations:
        key, old, new = mutation[:3]
        occurrence = mutation[3] if len(mutation) == 4 else 1
        start = -1
        for _ in range(occurrence):
            start = s[key].find(old, start + 1)
            if start < 0:
                raise ValueError('inactive Elements tap mutation: ' + old)
        changed = dict(s)
        changed[key] = s[key][:start] + new + s[key][start + len(old):]
        try:
            elements_tap_hashes(changed)
        except ValueError:
            continue
        raise ValueError('Elements tap mutation escaped: ' + old)
    print('Elements tapleaf/tapEnv trees, exact tag, native key and C boundaries match;', len(elements_tap_mutations), 'mutations rejected')


    elements_issuance_mutations = [
        ('elements_catalog', 'specificationSigHash IssuanceRangeProofsHash = SigHash.issuanceRangeProofsHash', 'specificationSigHash IssuanceRangeProofsHash = SigHash.issuancesHash'),
        ('elements_sighash_lib', 'issuanceRangeProofsHash = SigHash.issuanceRangeProofsHash SigHash.lib', 'issuanceRangeProofsHash = SigHash.issuancesHash SigHash.lib'),
        ('elements_sighash', 'take (drop (primitive IssuanceAssetProof)) &&&', 'take (drop (primitive IssuanceTokenProof)) &&&'),
        ('elements_sighash', '(take (drop (primitive IssuanceTokenProof)) &&& ih)', '(take (drop (primitive IssuanceAssetProof)) &&& ih)'),
        ('elements_sighash', 'iih &&& (ioh &&& oh) >>> ctx8Addn vector64', 'iih &&& (ioh &&& oh) >>> ctx8Addn vector32'),
        ('elements_issuance_port', 'Elements.IssuanceAssetProof', 'Elements.InputAnnexHash'),
        ('elements_issuance_port', 'Elements.IssuanceTokenProof', 'Elements.IssuanceAssetProof'),
        ('elements_issuance_port', '@literal_ctx8_addn 6 term', '@literal_ctx8_addn 5 term'),
        ('elements_issuance_port', '@for_while_program 5 _ _ _ core', '@for_while_program 3 _ _ _ core'),
        ('elements_issuance_port', '@literal_sha_hash_ctx_init core', '@AC.unit _ core'),
        ('elements_issuance_port', '@literal_ctx8_finalize term', '@literal_ctx8_addn 5 term'),
        ('elements_issuance_port', '@AC.comp _ _ _ core', '@AC.pair _ _ _ core'),
        ('elements_issuance_port', 'haskell_issuance_proof_view false txi.', 'haskell_issuance_proof_view true txi.'),
        ('elements_issuance_port', 'haskell_issuance_proof_view true txi.', 'haskell_issuance_proof_view false txi.'),
    ]
    for occurrence in [1, 2]:
        elements_issuance_mutations.append(('elements_issuance_port', '@AC.injl _ _ _ core (AC.drop (AC.drop AC.iden))',
                          '@AC.injr _ _ _ core (AC.drop (AC.drop AC.iden))', occurrence))
    declaration = 'Theorem elements_issuance_range_proofs_hash_literal_local_spec :'
    elements_issuance_mutations += [
        ('elements_issuance_port', declaration, declaration + ' False ->'),
        ('elements_issuance_port', declaration, declaration + ' memcpy_model ->'),
        ('elements_issuance_port', 'hash_getter_rep elements_issuance_range_proofs_hash_of 0 536 760',
         'hash_getter_rep elements_issuance_range_proofs_hash_of 0 544 760'),
    ]
    for mutation in elements_issuance_mutations:
        key, old, new = mutation[:3]
        occurrence = mutation[3] if len(mutation) == 4 else 1
        start = -1
        for _ in range(occurrence):
            start = s[key].find(old, start + 1)
            if start < 0:
                raise ValueError('inactive issuance mutation: ' + old)
        changed = dict(s)
        changed[key] = s[key][:start] + new + s[key][start + len(old):]
        try:
            elements_issuance_proofs_hash(changed)
        except ValueError:
            continue
        raise ValueError('issuance mutation escaped: ' + old)
    print('Issuance two-primitive loop, reused views and whole C boundary match;', len(elements_issuance_mutations), 'mutations rejected')
    elements_nonce_mutations = [
        ('elements_prog_lib', 'nonceHash = Elements.nonceHash Elements.libAssert', 'nonceHash = Elements.annexHash Elements.libAssert'),
        ('elements_prog', 'scribe (toWord8 0x02)', 'scribe (toWord8 0x03)'),
        ('elements_prog', 'scribe (toWord8 0x03)', 'scribe (toWord8 0x02)'),
        ('elements_prog', '(unit >>> scribe (toWord8 0x01)) &&& iden', '(unit >>> scribe (toWord8 0x00)) &&& iden'),
        ('elements_catalog', 'specificationSigHash OutputNoncesHash = SigHash.outputNoncesHash', 'specificationSigHash OutputNoncesHash = SigHash.outputScriptsHash'),
        ('elements_sighash_lib', 'outputNoncesHash = SigHash.outputNoncesHash SigHash.lib', 'outputNoncesHash = SigHash.outputScriptsHash SigHash.lib'),
        ('elements_sighash', 'body = take (drop (primitive OutputNonce)) &&& ih', 'body = take (drop (primitive OutputScriptHash)) &&& ih'),
        ('elements_sighash', 'ih &&& oh >>> nonceHash', 'ih &&& oh >>> annexHash'),
        ('elements_nonce_port', 'haskell_to_word 3 0x02', 'haskell_to_word 3 0x03'),
        ('elements_nonce_port', 'haskell_to_word 3 0x03', 'haskell_to_word 3 0x02'),
        ('elements_nonce_port', 'haskell_to_word 3 0x01', 'haskell_to_word 3 0x00'),
        ('elements_nonce_port', '@Word.zero 3 (Alg.Assertion.toCore term)', 'Alg.scribe (haskell_to_word 3 0x01)'),
        ('elements_nonce_port', '@literal_ctx8_addn 5 term', '@literal_ctx8_addn 6 term'),
        ('elements_nonce_port', '@literal_ctx8_add1 term', '@literal_ctx8_addn 0 term'),
        ('elements_nonce_port', '(fun term => @literal_elements_nonce_hash term) 5 term', '(fun term => @literal_elements_nonce_hash term) 3 term'),
        ('elements_nonce_port', 'Elements.OutputNonce', 'Elements.OutputScriptHash'),
        ('elements_nonce_port', 'elements_nonce_encode n = encode_nonce_literal n.', 'elements_nonce_encode n = elements_nonce_encode n.'),
        ('elements_nonce_port', 'hash_getter_rep elements_output_nonces_hash_of 0 56 760', 'hash_getter_rep elements_output_nonces_hash_of 0 88 760'),
    ]
    declaration = 'Theorem elements_output_nonces_hash_literal_local_spec :'
    elements_nonce_mutations += [
        ('elements_nonce_port', declaration, declaration + ' False ->'),
        ('elements_nonce_port', declaration, declaration + ' memcpy_model ->'),
    ]
    for key, old, new in elements_nonce_mutations:
        if old not in s[key]:
            raise ValueError('inactive nonce mutation: ' + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            elements_nonce_hashes(changed)
        except ValueError:
            continue
        raise ValueError('nonce mutation escaped: ' + old)
    print('Nonce serializer, primitive loop, native encoder and whole C boundary match;', len(elements_nonce_mutations), 'mutations rejected')
    elements_amount_hash_mutations = [
        ('elements_prog_lib', 'assetAmountHash = Elements.assetAmountHash Elements.libAssert', 'assetAmountHash = Elements.outpointHash Elements.libAssert'),
        ('elements_prog', 'scribe (toWord8 0x0a)', 'scribe (toWord8 0x0b)'),
        ('elements_prog', 'scribe (toWord8 0x08)', 'scribe (toWord8 0x09)'),
        ('elements_prog', 'ctx8Add8 = ctx8Addn vector8', 'ctx8Add8 = ctx8Addn vector32'),
        ('elements_prog', 'assetAmountHash = (oh &&& ioh >>> assetHash) &&& iih >>> amountHash', 'assetAmountHash = (oh &&& ioh >>> amountHash) &&& iih >>> assetHash'),
        ('elements_amounts_port', 'haskell_to_word 3 0x0a', 'haskell_to_word 3 0x0b'),
        ('elements_amounts_port', 'haskell_to_word 3 0x0b', 'haskell_to_word 3 0x0a'),
        ('elements_amounts_port', 'haskell_to_word 3 0x08', 'haskell_to_word 3 0x09'),
        ('elements_amounts_port', 'haskell_to_word 3 0x09', 'haskell_to_word 3 0x08'),
        ('elements_amounts_port', '@literal_ctx8_addn 3 term', '@literal_ctx8_addn 5 term'),
        ('elements_amounts_port', '@literal_ctx8_add1 term', '@literal_ctx8_addn 0 term'),
        ('elements_amounts_port', '(O H &&& I O H >>> @literal_elements_asset_hash term)',
         '(O H &&& I O H >>> @literal_elements_amount_hash term)'),
        ('elements_amounts_port', '(fun term => @literal_elements_asset_amount_hash term) 5 term',
         '(fun term => @literal_elements_asset_amount_hash term) 3 term'),
        ('elements_amounts_port', '(@EFP.Combinators.prim _ _ alg pm) (@EFP.Combinators.prim _ _ alg pa)',
         '(@EFP.Combinators.prim _ _ alg pa) (@EFP.Combinators.prim _ _ alg pm)'),
    ]
    for tag, name, stem, primitive, offset in [
        ('OutputAmountsHash', 'outputAmountsHash', 'output_amounts', 'Output', 24),
        ('InputAmountsHash', 'inputAmountsHash', 'input_amounts', 'Input', 248),
    ]:
        declaration = 'Theorem elements_' + stem + '_hash_literal_local_spec :'
        elements_amount_hash_mutations += [
            ('elements_catalog', 'specificationSigHash ' + tag + ' = SigHash.' + name,
             'specificationSigHash ' + tag + ' = SigHash.outputScriptsHash'),
            ('elements_sighash_lib', name + ' = SigHash.' + name + ' SigHash.lib',
             name + ' = SigHash.outputScriptsHash SigHash.lib'),
            ('elements_amounts_port', 'Elements.' + primitive + 'Amount Elements.' + primitive + 'Asset alg',
             'Elements.' + primitive + 'Asset Elements.' + primitive + 'Amount alg'),
            ('elements_amounts_port', declaration, declaration + ' False ->'),
            ('elements_amounts_port', declaration, declaration + ' memcpy_model ->'),
            ('elements_amounts_port', f'hash_getter_rep elements_{stem}_hash_of 0 {offset} 760',
             f'hash_getter_rep elements_{stem}_hash_of 0 {offset + 8} 760'),
        ]
    for key, old, new in elements_amount_hash_mutations:
        if old not in s[key]:
            raise ValueError('inactive amount-hash mutation: ' + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            elements_amount_hashes(changed)
        except ValueError:
            continue
        raise ValueError('amount-hash mutation escaped: ' + old)
    print('Asset/amount serializers, two primitive loops and whole C boundaries match;', len(elements_amount_hash_mutations), 'mutations rejected')


    elements_composite_mutations = [
        ('elements_sighash', '(outputAmountsHash &&& outputNoncesHash)', '(outputNoncesHash &&& outputAmountsHash)'),
        ('elements_sighash', '(outputScriptsHash &&& outputRangeProofsHash)', '(outputRangeProofsHash &&& outputScriptsHash)'),
        ('elements_sighash', '(inputAmountsHash &&& inputScriptsHash)', '(inputScriptsHash &&& inputAmountsHash)'),
        ('elements_sighash', '>>> ctx8Addn vector128 >>> ctx8Finalize', '>>> ctx8Addn vector64 >>> ctx8Finalize'),
        ('elements_sighash', 'inputUtxosHash = ctx8Init', 'inputUtxosHash = (unit >>> ctx8Init)'),
        ('elements_composite_port', '@literal_ctx8_addn k term', '@literal_ctx8_addn 7 term'),
        ('elements_composite_port', '@literal_sha_hash_ctx_init core', '@AC.unit _ core'),
        ('elements_composite_port', '@literal_ctx8_finalize term', '@literal_ctx8_addn 6 term'),
        ('elements_composite_port', '@literal_elements_fixed_vector_hash 7 alg', '@literal_elements_fixed_vector_hash 6 alg'),
        ('elements_composite_port', '@literal_elements_fixed_vector_hash 6 alg', '@literal_elements_fixed_vector_hash 7 alg'),
        ('elements_composite_port', '@literal_elements_output_amounts_hash alg', '@literal_elements_input_amounts_hash alg'),
        ('elements_composite_port', '@literal_elements_output_nonces_hash alg', '@literal_elements_output_scripts_hash alg'),
        ('elements_composite_port', '@literal_elements_output_scripts_hash alg', '@literal_elements_output_range_proofs_hash alg'),
        ('elements_composite_port', '@literal_elements_input_amounts_hash alg', '@literal_elements_output_amounts_hash alg'),
        ('elements_composite_port', '@literal_elements_input_scripts_hash alg', '@literal_elements_output_scripts_hash alg'),
        ('elements_composite_port', '@AC.pair _ _ _ core', '@AC.comp _ _ _ core'),
    ]
    for tag, hs_name, stem, k, offset in [
        ('OutputsHash', 'outputsHash', 'outputs', 7, 184),
        ('InputUtxosHash', 'inputUtxosHash', 'input_utxos', 6, 312),
    ]:
        declaration = 'Theorem elements_' + stem + '_hash_literal_local_spec :'
        elements_composite_mutations += [
            ('elements_catalog', 'specificationSigHash ' + tag + ' = SigHash.' + hs_name,
             'specificationSigHash ' + tag + ' = SigHash.inputsHash'),
            ('elements_sighash_lib', hs_name + ' = SigHash.' + hs_name + ' SigHash.lib',
             hs_name + ' = SigHash.inputsHash SigHash.lib'),
            ('elements_composite_port', declaration, declaration + ' False ->'),
            ('elements_composite_port', declaration, declaration + ' memcpy_model ->'),
            ('elements_composite_port', f'hash_getter_rep elements_{stem}_hash_of 0 {offset} 760',
             f'hash_getter_rep elements_{stem}_hash_of 0 {offset + 8} 760'),
        ]
    for key, old, new in elements_composite_mutations:
        if old not in s[key]:
            raise ValueError('inactive Elements composite mutation: ' + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            elements_composite_hashes(changed)
        except ValueError:
            continue
        raise ValueError('Elements composite mutation escaped: ' + old)
    print('Elements composite payload order, SHA skeleton and whole C boundaries match;', len(elements_composite_mutations), 'mutations rejected')
    elements_blinding_mutations = [
        ('elements_sighash', 'primitive NewIssuanceContract &&& primitive ReissuanceBlinding', 'primitive ReissuanceEntropy &&& primitive ReissuanceBlinding'),
        ('elements_sighash', 'match (drop issuanceEntropyBody)', 'match (take issuanceEntropyBody)'),
        ('elements_sighash', '((unit >>> zero word256) &&& oh)', '((unit >>> one word256) &&& oh)'),
        ('elements_blinding_model', 'AC.injr (AC.injl AC.unit)', 'AC.injl (AC.injl AC.unit)'),
        ('elements_blinding_model', '@Word.zero 8 core', '@Word.zero 5 core'),
        ('elements_blinding_model', 'Elements.NewIssuanceContract', 'Elements.ReissuanceBlinding'),
        ('elements_blinding_model', 'Elements.ReissuanceEntropy', 'Elements.NewIssuanceContract'),
        ('elements_blinding_port', '@Word.zero 3 (Alg.Assertion.toCore term)', '@one8_spec (Alg.Assertion.toCore term)'),
        ('elements_blinding_port', '@one8_spec (Alg.Assertion.toCore term)', 'Alg.scribe (haskell_to_word 3 1)'),
        ('elements_blinding_port', '@literal_ctx8_addn 6 term', '@literal_ctx8_addn 5 term'),
        ('elements_blinding_port', '@literal_ctx8_add1 term', '@literal_ctx8_addn 0 term'),
        ('elements_blinding_port', '(fun term => @literal_elements_blinding_entropy_absorb term) 5 term', '(fun term => @literal_elements_blinding_entropy_absorb term) 3 term'),
        ('elements_blinding_port', '(@elements_issuance_blinding_entropy_spec alg)', '(@elements_input_outpoints_hash_spec alg)'),
        ('elements_blinding_port', 'hash_getter_rep elements_issuance_blinding_entropy_hash_of 0 568 760', 'hash_getter_rep elements_issuance_blinding_entropy_hash_of 0 536 760'),
        ('elements_catalog', 'specificationSigHash IssuanceBlindingEntropyHash = SigHash.issuanceBlindingEntropyHash', 'specificationSigHash IssuanceBlindingEntropyHash = SigHash.issuanceRangeProofsHash'),
        ('elements_sighash_lib', 'issuanceBlindingEntropyHash = SigHash.issuanceBlindingEntropyHash SigHash.lib', 'issuanceBlindingEntropyHash = SigHash.issuanceRangeProofsHash SigHash.lib'),
        ('hs_arith', 'one w = true >>> left_pad_low word1 w', 'one w = false >>> left_pad_low word1 w'),
        ('hs_word', 'left_pad_pad _ SingleV = iden', 'left_pad_pad _ SingleV = unit'),
        ('one_spec', 'left_pad_low_1_n 3', 'left_pad_low_1_n 4'),
        ('one_spec', '(@Bit.true Ty.Unit term)', '(@Bit.false Ty.Unit term)'),
        ('elements_primitive_hs', 'either (Just . newIssuanceContractHash) (const Nothing)', 'either (const Nothing) (Just . reissuanceEntropy)'),
        ('elements_primitive_coq', '| Some (inr re) => Some (reissuanceEntropy re)', '| Some (inr re) => Some (reissuanceBlindingNonce re)'),
    ]
    declaration = 'Theorem elements_issuance_blinding_entropy_hash_literal_local_spec :'
    elements_blinding_mutations += [
        ('elements_blinding_port', declaration, declaration + ' False ->'),
        ('elements_blinding_port', declaration, declaration + ' memcpy_model ->'),
    ]
    for key, old, new in elements_blinding_mutations:
        if old not in s[key]:
            raise ValueError('inactive blinding entropy mutation: ' + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            elements_blinding_entropy_hash(changed)
        except ValueError:
            continue
        raise ValueError('blinding entropy mutation escaped: ' + old)
    print('Blinding entropy routes, actual one-word program, traversal and whole C boundary match;', len(elements_blinding_mutations), 'mutations rejected')
    elements_status_mutations = [
        ('elements_catalog', 'specificationIssuance Issuance = Issuance.issuance', 'specificationIssuance Issuance = Issuance.issuanceEntropy'),
        ('elements_issuance_lib', 'issuance = Issuance.issuance Issuance.lib', 'issuance = Issuance.issuanceEntropy Issuance.lib'),
        ('elements_issuance_program', 'flip match (injr (injr true))', 'match (injr (injr true))'),
        ('elements_issuance_program', 'primitive ReissuanceEntropy &&& primitive NewIssuanceContract', 'primitive NewIssuanceContract &&& primitive ReissuanceEntropy'),
        ('elements_status_model', 'ISC.injr (ISC.injr Bit.true)', 'ISC.injr (ISC.injr Bit.false)'),
        ('elements_status_model', 'ISC.injr (ISC.injr Bit.false)', 'ISC.injr (ISC.injr Bit.true)'),
        ('elements_status_model', 'ISC.copair (ISC.injl ISC.unit)', 'ISC.copair (ISC.injr ISC.unit)'),
        ('elements_status_model', 'Primitive.Combinators.prim Elements.NewIssuanceContract', 'Primitive.Combinators.prim Elements.ReissuanceEntropy'),
        ('elements_status_model', '| Some (inl _) => inr (inl tt)', '| Some (inl _) => inr (inr tt)'),
        ('elements_status_model', '| None => inl tt', '| None => inr (inl tt)'),
        ('elements_status_exec', '(ofs + 528)', '(ofs + 532)'),
        ('elements_status_exec', '@encode issuance_status_payload (issuance_status_of_input txi)', '@encode issuance_status_payload (inl tt)'),
        ('elements_status_tags', '| Some (inl _) => Int.repr 1', '| Some (inl _) => Int.repr 2'),
        ('elements_status_local', 'issuance_status_enum_rep 544 0 0 696', 'issuance_status_enum_rep 544 0 0 704'),
    ]
    declaration = 'Theorem elements_issuance_status_local_spec :'
    elements_status_mutations += [
        ('elements_status_local', declaration, declaration + ' False ->'),
        ('elements_status_local', declaration, declaration + ' memcpy_model ->'),
        ('elements_status_local', 'application_jet_local_spec_sep f_simplicity_issuance elements_ge', 'application_jet_local_spec_sep f_simplicity_input_amount elements_ge'),
    ]
    for key, old, new in elements_status_mutations:
        if old not in s[key]:
            raise ValueError('inactive issuance status mutation: ' + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            elements_issuance_status(changed)
        except ValueError:
            continue
        raise ValueError('issuance status mutation escaped: ' + old)
    print('Issuance literal flip-match routing, all four cases, enum and whole C boundary match;', len(elements_status_mutations), 'mutations rejected')

    elements_computed_mutations = [
        ('elements_calc_port', '0x6a09e667bb67ae853c6ef372a54ff53a510e527f9b05688c1f83d9ab5be0cd19', '0x6a09e667bb67ae853c6ef372a54ff53a510e527f9b05688c1f83d9ab5be0cd18'),
        ('elements_calc_port', 'haskell_to_word 5 (2 ^ 31)', 'haskell_to_word 5 (2 ^ 30)'),
        ('elements_calc_port', 'haskell_to_word 7 (256 + 32)', 'haskell_to_word 7 (256 + 64)'),
        ('elements_calc_port', 'haskell_to_word 8 (2 ^ 255 + 256)', 'haskell_to_word 8 (2 ^ 255 + 512)'),
        ('elements_calc_port', 'haskell_to_word 8 (2 ^ 248)', 'haskell_to_word 8 (2 * 2 ^ 248)'),
        ('elements_calc_port', 'haskell_to_word 8 (2 * 2 ^ 248)', 'haskell_to_word 8 (2 ^ 248)'),
        ('elements_calc_port', 'LC.drop (LC.pair (LC.drop LC.iden) (LC.take LC.iden))', 'LC.drop (LC.pair (LC.take LC.iden) (LC.drop LC.iden))'),
        ('elements_calc_port', '@Word.zero 6 core', '@Word.zero 5 core'),
        ('elements_calc_port', '@Word.zero 8 core', '@Word.zero 7 core'),
        ('elements_prog', 'drop (drop (ih &&& oh) &&& take (ih &&& oh))', 'drop (take (ih &&& oh) &&& drop (ih &&& oh))'),
        ('elements_prog', 'toWord128 (256+32)', 'toWord128 (256+64)'),
        ('elements_prog', 'toWord256 (2*2^248)', 'toWord256 (2^248)'),
        ('elements_computed_port', 'LC.drop literal_calculate_confidential_token', 'LC.drop literal_calculate_explicit_token'),
        ('elements_computed_port', 'LC.case (LC.injl LC.unit)', 'LC.case (LC.injr LC.unit)'),
        ('elements_computed_port', 'Primitive.Combinators.prim Elements.InputPrevOutpoint', 'Primitive.Combinators.prim Elements.ReissuanceEntropy'),
        ('elements_computed_port', 'Primitive.Combinators.prim Elements.IssuanceAssetAmount', 'Primitive.Combinators.prim Elements.IssuanceTokenAmount'),
        ('elements_issuance_program', 'flip match (take (injr (injr iden)))', 'match (take (injr (injr iden)))'),
        ('elements_issuance_program', 'match (drop calculateConfidentialToken) (drop calculateExplicitToken)', 'match (drop calculateExplicitToken) (drop calculateConfidentialToken)'),
        ('elements_computed_exec', '(ofs + 256 + delta)', '(ofs + 256 + delta + 32)'),
        ('elements_computed_exec', 'issuance_status_enum_rep m b ofs txi /\\', 'True /\\'),
    ]
    for stem, tag, offset in [('entropy', 'IssuanceEntropy', 72), ('asset', 'IssuanceAsset', 168), ('token', 'IssuanceToken', 200)]:
        declaration = 'Theorem elements_issuance_' + stem + '_literal_local_spec :'
        elements_computed_mutations += [
            ('elements_computed_port', declaration, declaration + ' False ->'),
            ('elements_computed_port', declaration, declaration + ' memcpy_model ->'),
            ('elements_computed_port', '(computed_issuance_hash_rep ' + str(offset) + ' issuance_' + stem + '_of_input)',
             '(computed_issuance_hash_rep ' + str(offset + 32) + ' issuance_' + stem + '_of_input)'),
            ('elements_catalog', 'specificationIssuance ' + tag + ' = Issuance.issuance' + stem.capitalize(),
             'specificationIssuance ' + tag + ' = Issuance.issuance'),
            ('elements_issuance_lib', 'issuance' + stem.capitalize() + ' = Issuance.issuance' + stem.capitalize() + ' Issuance.lib',
             'issuance' + stem.capitalize() + ' = Issuance.issuance Issuance.lib'),
        ]
    for key, old, new in elements_computed_mutations:
        if old not in s[key]:
            raise ValueError('inactive computed issuance mutation: ' + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            elements_issuance_computed(changed)
        except ValueError:
            continue
        raise ValueError('computed issuance mutation escaped: ' + old)
    print('Computed issuance literal calculations, primitive routing and whole C contracts match;', len(elements_computed_mutations), 'mutations rejected')

    elements_annex_mutations = [
        ('elements_catalog', 'specificationSigHash AnnexHash = Prog.annexHash', 'specificationSigHash AnnexHash = Prog.nonceHash'),
        ('elements_prog_lib', 'annexHash = Elements.annexHash Elements.libAssert', 'annexHash = Elements.nonceHash Elements.libAssert'),
        ('elements_annex_context_port', 'nonce_elements_partial_local_spec f_simplicity_annex_hash', 'nonce_elements_partial_local_spec f_simplicity_nonce_hash'),
        ('elements_annex_context_port', '(@literal_bitcoin_annex_hash optalg)', '(@literal_bitcoin_outpoint_hash optalg)'),
        ('elements_annex_context_port', '(Ty.Sum Ty.Unit (Word 8))', '(Ty.Sum Ty.Unit (Word 6))'),
        ('elements_annex_exec', 'nonce_sha_partial_local_spec f_simplicity_annex_hash', 'nonce_sha_partial_local_spec f_simplicity_nonce_hash'),
        ('elements_annex_exec', '(fun a => @annex_hash_spec optalg a)', '(fun a => @outpoint_hash_spec optalg a)'),
    ]
    for key, theorem in [
        ('elements_annex_exec', 'elements_annex_hash_local_spec'),
        ('elements_annex_context_port', 'elements_annex_hash_literal_local_spec'),
    ]:
        declaration = 'Theorem ' + theorem + ' : memcpy_model ->'
        elements_annex_mutations += [
            (key, declaration, 'Theorem ' + theorem + ' :'),
            (key, declaration, declaration + ' False ->'),
            (key, declaration, declaration + ' sha_globals_ok Mem.empty ->'),
        ]
    for key, old, new in elements_annex_mutations:
        if old not in s[key]:
            raise ValueError('inactive Elements annex mutation: ' + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            elements_annex_context(changed)
        except ValueError:
            continue
        raise ValueError('Elements annex mutation escaped: ' + old)
    print('Elements annex shared literal program and complete partial C boundary match;', len(elements_annex_mutations), 'mutations rejected')

    elements_builder_mutations = [
        ('elements_prog', 'scribe . toWord8 $ 0xbe', 'scribe . toWord8 $ 0xbc'),
        ('elements_prog', 'lt word256 &&& iden >>> cond iden (ih &&& oh)', 'lt word256 &&& iden >>> cond iden (oh &&& ih)'),
        ('elements_prog', 'toWord512 $ 2^511 + 1024', 'toWord512 $ 2^511 + 512'),
        ('eltap_builders_port', '&&& @literal_build_tapleaf_block term >>> @literal_sha_256_block term.', '&&& @build_tapleaf_block term >>> @literal_sha_256_block term.'),
        ('eltap_builders_port', '@lt_word_spec term 8', '@lt_word_spec term 7'),
        ('eltap_builders_port', 'Bit.cond iden (I H &&& O H)', 'Bit.cond iden (O H &&& I H)'),
        ('eltap_builders_port', 'haskell_to_word 9 (2^511+1024)', 'haskell_to_word 9 (2^511+512)'),
        ('eltap_contract', 'frame_base_valid sbase ->', 'False -> frame_base_valid sbase ->'),
        ('eltap_contract', 'write_prefix_at m mf bw outedge cursor /\\', 'True /\\'),
        ('eltap_contract', 'E0 mf (Vint Int.one)', 'E0 mf Vundef'),
        ('eltap_linkage', 'Clight.globalenv jets_elements.prog', 'Clight.globalenv jets_sha.prog'),
    ]
    for stem, tag, hs_name, label, field, size in [
        ('leaf', 'BuildTapleafSimplicity', 'buildTapleafSimplicity', 'TapLeaf/elements', '_tagName__1', 16),
        ('branch', 'BuildTapbranch', 'buildTapbranch', 'TapBranch/elements', '_tagName__2', 18),
    ]:
        theorem = ('elements_build_tapleaf_simplicity_literal_local_spec' if stem == 'leaf'
                   else 'elements_build_tapbranch_literal_local_spec')
        declaration = 'Theorem ' + theorem + ' : memcpy_model ->'
        elements_builder_mutations += [
            ('elements_catalog', 'specificationSigHash ' + tag + ' = Prog.' + hs_name,
             'specificationSigHash ' + tag + ' = Prog.annexHash'),
            ('elements_prog_lib', hs_name + ' = Elements.' + hs_name + ' Elements.lib',
             hs_name + ' = Elements.annexHash Elements.libAssert'),
            ('eltap_builders_port', '(unit >>> Alg.scribe (literal_short_tag_prefix "' + label + '"%string))',
             '(unit >>> Alg.scribe (literal_short_tag_prefix "' + label + ' "%string))'),
            ('eltap_builders_port', '(unit >>> Alg.scribe (literal_short_tag_prefix "' + label + '"%string))',
             '(unit >>> Alg.scribe (literal_short_tag_prefix "' + label.replace('/', ' /') + '"%string))'),
            ('eltap_builders_port', declaration, declaration + ' False ->'),
            ('eltap_builders_port', declaration, 'Theorem ' + theorem + ' :'),
            ('eltap_' + stem + '_exec', '(i < ' + str(size) + ')%nat', '(i < ' + str(size - 1) + ')%nat'),
            ('eltap_' + stem + '_exec', '(sha_symbol_block ' + field + ')', '(sha_symbol_block _tagName)'),
            ('eltap_' + stem + '_public', 'sha_globals_ok m /\\ el_sha_tap' + stem + '_tag_ok m', 'sha_globals_ok m'),
        ]
    for key, old, new in elements_builder_mutations:
        if old not in s[key]:
            raise ValueError('inactive Elements builder mutation: ' + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            elements_tap_builders(changed)
        except ValueError:
            continue
        raise ValueError('Elements builder mutation escaped: ' + old)
    print('Elements taproot builders share checked literal payloads with exact tags/ge and full C boundaries;', len(elements_builder_mutations), 'mutations rejected')


if __name__ == "__main__":
    test()
