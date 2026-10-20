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
    }.items()}


def test():
    s = sources()
    check(s)
    context_add(s)
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


if __name__ == "__main__":
    test()
