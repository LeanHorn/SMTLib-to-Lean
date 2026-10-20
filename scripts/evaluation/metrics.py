"""Reproducible lexical size metrics for SMT-LIB and emitted Lean statements.

These are lexical measurements, not either language's official parser tokens.
Each SMT atom, quoted symbol, or string is one token; parentheses are separate.
For Lean, identifiers, numeric/string/character literals, and maximal operator
runs are one token; (), [], {}, comma, semicolon, and dot are separate. Quoted
identifiers are one token. Whitespace and comments never contribute tokens.

Output LOC/tokens cover declarations/helpers before the exact ``-- Proofs``
line, excluding standalone imports, options, and namespace/section scaffolding emitted
by Smt2Lean. Mutual declaration blocks remain part of the measured code.
The independently compilable statements source retains scaffolding
and trailing namespace closures. Byte counts include original comments and
whitespace: output_bytes is the entire output, output_statement_bytes is the
metric section. Ratios are output/input, or None for a zero denominator.

cloc counts physical code lines after real comments have been lexically masked.
The SMT custom language intentionally has no comment filter. Native Lean cloc
filters are retained; literal comment delimiters in Lean strings/quoted names
are shielded in a separate counting projection because cloc's filters are not a
Lean lexer. Exact comment-masked files and counting projections are both kept.
"""

from bisect import bisect_right
from collections import Counter
import json
from pathlib import Path
import re
import subprocess
from typing import NamedTuple
import unicodedata


LEAN_NUMBER = re.compile(r"(?:0[xX][0-9a-fA-F]+|0[bB][01]+|[0-9]+(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?)")
LEAN_RAW_STRING = re.compile(r'r#*"')


class LexicalError(ValueError):
    """Input cannot be safely measured with the supported lexical convention."""


class Token(NamedTuple):
    start: int
    end: int
    kind: str
    value: str


def _lex(text, language):
    tokens, comments = [], []
    i, n = 0, len(text)
    lean = language == "lean"
    while i < n:
        start, c = i, text[i]
        if c.isspace():
            i += 1
            continue
        if (not lean and c == ";") or (lean and text.startswith("--", i)):
            i = text.find("\n", i)
            if i < 0:
                i = n
            comments.append(Token(start, i, "comment", text[start:i]))
            continue
        if lean and text.startswith("/-", i):
            i, depth = i + 2, 1
            while i < n and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise LexicalError("Unterminated Lean block comment")
            comments.append(Token(start, i, "comment", text[start:i]))
            continue
        if lean and c == "r" and LEAN_RAW_STRING.match(text, i):
            raise LexicalError("Lean raw strings are outside the supported emitted syntax")
        if c == '"' or (lean and c == "'"):
            quote, kind = c, "string" if c == '"' else "character"
            i += 1
            while i < n:
                if lean and text[i] == "\\":
                    if i + 1 >= n:
                        raise LexicalError("Unterminated Lean literal escape")
                    i += 2
                elif text[i] == quote:
                    if not lean and i + 1 < n and text[i + 1] == '"':
                        i += 2
                        continue
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise LexicalError(f"Unterminated {language} {kind}")
            tokens.append(Token(start, i, kind, text[start:i]))
            continue
        if (not lean and c == "|") or (lean and c == "«"):
            closing = "»" if lean else "|"
            i = text.find(closing, start + 1)
            if i < 0:
                raise LexicalError(f"Unterminated {language} quoted identifier")
            i += 1
            if not lean and "\\" in text[start:i]:
                raise LexicalError("Backslashes are unsupported in SMT-LIB quoted symbols")
            tokens.append(Token(start, i, "quoted", text[start:i]))
            continue
        if c in ("()[]{},;." if lean else "()"):
            i += 1
            tokens.append(Token(start, i, "delimiter", c))
            continue
        if not lean:
            while i < n and not text[i].isspace() and text[i] not in '();"|':
                if text[i] == "\\":
                    raise LexicalError("Backslash outside an SMT-LIB string")
                i += 1
            kind = "atom"
        elif c.isdigit():
            match = LEAN_NUMBER.match(text, i)
            i += len(match.group())
            kind = "number"
        elif _identifier_char(c):
            i += 1
            while i < n and (_identifier_char(text[i]) or text[i] == "'"):
                i += 1
            kind = "identifier"
        else:
            if c in "»`":
                raise LexicalError(f"Unsupported Lean token at character {i}: {c!r}")
            i += 1
            while (i < n and not text[i].isspace() and
                   text[i] not in '()[]{},;."\'«»`' and
                   not _identifier_char(text[i]) and not text[i].isdigit() and
                   not text.startswith(("--", "/-"), i)):
                i += 1
            kind = "operator"
        tokens.append(Token(start, i, kind, text[start:i]))
    return tokens, comments


def _identifier_char(c):
    return c == "_" or unicodedata.category(c)[0] in "LNM"


def smt_tokens(text):
    return [token.value for token in _lex(text, "smt")[0]]


def lean_tokens(text):
    return [token.value for token in _lex(text, "lean")[0]]


def source_info(text):
    """Count top-level commands, never command-looking strings or comments."""
    tokens, _ = _lex(text, "smt")
    counts, depth, command, logic = Counter(), 0, None, None
    for token in tokens:
        if token.value == "(" and token.kind == "delimiter":
            depth += 1
            if depth == 1:
                command = None
        elif token.value == ")" and token.kind == "delimiter":
            depth -= 1
            if depth < 0:
                raise LexicalError("Unbalanced SMT-LIB parentheses")
        elif depth == 0:
            raise LexicalError("Expected a top-level SMT-LIB command")
        elif depth == 1 and command is None:
            if token.kind != "atom":
                raise LexicalError("Expected an unquoted SMT-LIB command name")
            command = token.value
            counts[command] += 1
        elif depth == 1 and command == "set-logic":
            logic = token.value
    if depth:
        raise LexicalError("Unbalanced SMT-LIB parentheses")
    return dict(query_count=sum(counts[name] for name in ("check-sat", "check-sat-assuming", "query")),
                assertion_count=counts["assert"], rule_count=counts["rule"],
                constraint_count=counts["assert"] + counts["rule"], logic=logic,
                source_empty=not tokens, command_counts=dict(counts))


def _input_structure(tokens):
    """Inspect list heads and exact indexed-sort forms without constructing an AST."""
    declarations, quantifiers = Counter(), {"forall": 0, "exists": 0}
    depth, maximum, lets, bitvec_count = 0, 0, 0, 0
    widths = set()
    for index, token in enumerate(tokens):
        if token.kind == "delimiter":
            if token.value == "(":
                depth += 1
                maximum = max(maximum, depth)
            else:
                depth -= 1
                if depth < 0:
                    raise LexicalError("Unbalanced SMT-LIB parentheses")
            continue
        is_head = (index > 0 and tokens[index - 1].kind == "delimiter" and
                   tokens[index - 1].value == "(")
        if token.kind != "atom" or not is_head:
            continue
        if token.value in quantifiers:
            quantifiers[token.value] += 1
        elif token.value == "let":
            lets += 1
        if depth == 1 and token.value.startswith(("declare-", "define-")):
            declarations[token.value] += 1
        if token.value == "_" and index + 3 < len(tokens):
            sort, width, closing = tokens[index + 1:index + 4]
            if (sort.kind == "atom" and sort.value == "BitVec" and
                    width.kind == "atom" and re.fullmatch(r"0|[1-9][0-9]*", width.value) and
                    closing.kind == "delimiter" and closing.value == ")"):
                widths.add(int(width.value))
                bitvec_count += 1
    if depth:
        raise LexicalError("Unbalanced SMT-LIB parentheses")
    widths = sorted(widths)
    return dict(max_parenthesis_depth=maximum, quantifier_counts=quantifiers,
                quantifier_count=sum(quantifiers.values()), let_count=lets,
                declaration_counts=dict(declarations), declaration_count=sum(declarations.values()),
                bitvec_sort_count=bitvec_count, bitvec_widths=widths,
                bitvec_width_min=widths[0] if widths else None,
                bitvec_width_max=widths[-1] if widths else None)


def input_structure(text):
    """Return lexical SMT structure, including comments/quoted-atom exclusions.

    Depth counts all syntactic parentheses. Quantifiers and lets count unquoted
    list heads, not binders or occurrences of the same name in another position.
    Declarations count top-level list heads beginning ``declare-`` or ``define-``
    (including extensions); a multi-declaration command counts once. Bit-vector
    widths count exact ``(_ BitVec N)`` forms with a literal SMT numeral, retaining
    their occurrence count and sorted distinct widths. These are lexical forms
    anywhere in the source, not semantically resolved terms or sorts.
    """
    return _input_structure(_lex(text, "smt")[0])


def _line_groups(text, tokens):
    starts = [0] + [m.end() for m in re.finditer("\n", text)]
    groups = {}
    for token in tokens:
        line = bisect_right(starts, token.start) - 1
        groups.setdefault(line, []).append(token)
    return starts, groups


def split_generated_source(text):
    """Return (compilable statements, metric-only declarations/helpers)."""
    tokens, comments = _lex(text, "lean")
    markers = [c for c in comments if c.value.rstrip("\r") == "-- Proofs" and
               (c.start == 0 or text[c.start - 1] == "\n")]
    if len(markers) != 1:
        raise LexicalError("Expected exactly one standalone '-- Proofs' marker")
    marker = markers[0]
    prefix = text[:marker.start]
    starts, groups = _line_groups(text, tokens)
    remove, scopes = [], []
    for line, group in groups.items():
        first = group[0]
        if first.start >= marker.start:
            break
        # Only unindented standalone commands used by the emitter are scaffolding.
        if first.start != starts[line] or first.kind != "identifier":
            continue
        if first.value not in {"import", "set_option", "namespace", "section", "mutual", "end"}:
            continue
        if first.value == "set_option" and any(t.value == "in" for t in group):
            raise LexicalError("Scoped set_option is outside the emitted scaffolding convention")
        name = "".join(t.value for t in group[1:])
        if first.value == "mutual":
            if name:
                raise LexicalError("Expected a standalone mutual command")
            scopes.append(("mutual", ""))
            continue
        elif first.value in {"namespace", "section"}:
            scopes.append((first.value, name))
        elif first.value == "end":
            if not scopes:
                raise LexicalError("Unexpected end before proofs")
            kind, expected = scopes.pop()
            if name and name != expected:
                raise LexicalError("Block closure does not match its opening")
            if kind == "mutual":
                continue
        end = starts[line + 1] if line + 1 < len(starts) else len(text)
        remove.append((starts[line], end))
    for kind, _ in scopes:
        if kind != "namespace":
            raise LexicalError(f"Unclosed {kind} block before proofs")
    scopes = [name for _, name in scopes]
    closures = []
    scopes.reverse()
    for line in reversed(groups):
        group = groups[line]
        if group[0].start < marker.end or not scopes:
            break
        if group[0].value != "end" or group[0].kind != "identifier":
            break
        name = "".join(t.value for t in group[1:])
        expected = scopes.pop()
        if name and name != expected:
            raise LexicalError("Trailing namespace closure does not match its opening")
        end = starts[line + 1] if line + 1 < len(starts) else len(text)
        closures.append(text[starts[line]:end])
    if scopes:
        raise LexicalError("Missing trailing namespace closure after proofs")
    metric, offset = [], 0
    for start, end in remove:
        metric.append(prefix[offset:start])
        offset = end
    metric.append(prefix[offset:])
    return prefix + "".join(reversed(closures)), "".join(metric)


LEAN_DECLARATION_KINDS = frozenset({
    "def", "abbrev", "axiom", "constant", "opaque", "inductive", "structure",
    "theorem", "lemma", "instance", "class",
})
LEAN_DECLARATION_MODIFIERS = frozenset({
    "noncomputable", "private", "protected", "unsafe", "partial",
})
LEAN_BINDER_TOKENS = ("∀", "forall", "∃", "fun", "λ")


def generated_structure(text):
    """Measure the emitted statement prefix using lexical conventions, not a Lean AST.

    Imports, options, namespaces, sections and proofs are excluded by
    ``split_generated_source``. Declaration starts are unindented lines beginning
    with a listed declaration keyword after optional listed modifiers. A
    declaration's token span ends at the next such start, a standalone unindented
    ``mutual``/``end``, or EOF; mutual wrappers do not enter declaration sizes.
    This matches the emitter's layout, including its unindented mutual members.

    Delimiter depth counts matched (), [] and {} only. Binder counts count exact,
    unquoted tokens ∀, forall, ∃, fun and λ; let counts exact unquoted ``let``
    tokens. Neither counts bound variables, implicit arrow binders, or semantic
    binder/let constructs. Comments, strings, characters and quoted names never
    contribute keywords or delimiters.
    """
    _, metric = split_generated_source(text)
    tokens, _ = _lex(metric, "lean")
    return _generated_structure(metric, tokens)


def _generated_structure(metric, tokens):
    """Use already split/lexed metric text when measuring a translation pair."""
    starts, groups = _line_groups(metric, tokens)
    declarations, boundaries = Counter(), {}
    for line, group in groups.items():
        first = group[0]
        if first.start != starts[line] or first.kind != "identifier":
            continue
        index = 0
        while (index < len(group) and group[index].kind == "identifier" and
               group[index].value in LEAN_DECLARATION_MODIFIERS):
            index += 1
        if (index < len(group) and group[index].kind == "identifier" and
                group[index].value in LEAN_DECLARATION_KINDS):
            kind = group[index].value
            declarations[kind] += 1
            boundaries[first.start] = True
        elif first.value in {"mutual", "end"} and len(group) == 1:
            boundaries[first.start] = False

    stack, maximum, largest, declaration_size = [], 0, 0, None
    binders, lets = dict.fromkeys(LEAN_BINDER_TOKENS, 0), 0
    matching = {")": "(", "]": "[", "}": "{"}
    for token in tokens:
        if token.start in boundaries:
            largest = max(largest, declaration_size or 0)
            declaration_size = 0 if boundaries[token.start] else None
        if declaration_size is not None:
            declaration_size += 1
        if token.kind in {"identifier", "operator"}:
            if token.value in binders:
                binders[token.value] += 1
            if token.value == "let":
                lets += 1
        if token.kind == "delimiter":
            if token.value in "([{":
                stack.append(token.value)
                maximum = max(maximum, len(stack))
            elif token.value in matching:
                if not stack or stack.pop() != matching[token.value]:
                    raise LexicalError("Unbalanced Lean delimiters")
    if stack:
        raise LexicalError("Unbalanced Lean delimiters")
    return dict(declaration_counts=dict(declarations),
                declaration_count=sum(declarations.values()),
                largest_declaration_tokens=max(largest, declaration_size or 0),
                max_delimiter_depth=maximum, binder_token_counts=binders,
                binder_token_count=sum(binders.values()), let_count=lets)


def _mask_comments(text, comments):
    chunks, offset = [], 0
    for token in comments:
        chunks.extend((text[offset:token.start], re.sub(r"[^\r\n]", " ", token.value)))
        offset = token.end
    chunks.append(text[offset:])
    return "".join(chunks)


def _cloc_projection(text, tokens):
    chunks, offset = [], 0
    for token in tokens:
        if token.kind not in {"string", "character", "quoted"}:
            continue
        chunks.extend((text[offset:token.start], re.sub(r"--|/-|-/", "xx", text[token.start:token.end])))
        offset = token.end
    chunks.append(text[offset:])
    return "".join(chunks)


SMT_CLOC_CONFIG = """SMT-LIB
    filter remove_matches ^$
    extension smt2
    3rd_gen_scale 1.00
"""


def measure_input(text, artifact_dir, cloc_path="cloc"):
    """Measure an input independently of translation; retain the cloc artifacts.

    Uses the same comment masking and cloc language definition as ``measure``.
    For successful translations, callers can use ``measure`` and
    ``input_structure`` instead to avoid running cloc on the input twice.
    """
    tokens, comments = _lex(text, "smt")
    structure = _input_structure(tokens)
    masked = _mask_comments(text, comments)
    artifact_dir = Path(artifact_dir).resolve()
    artifact_dir.mkdir(parents=True, exist_ok=True)
    (artifact_dir / "input.masked.smt2").write_bytes(masked.encode("utf-8"))
    (artifact_dir / "smt-cloc.lang").write_text(SMT_CLOC_CONFIG)
    command = [str(cloc_path), "--json", "--by-file", "--quiet", "--skip-uniqueness",
               "--read-lang-def=" + str(artifact_dir / "smt-cloc.lang"),
               str(artifact_dir / "input.masked.smt2")]
    (artifact_dir / "cloc-command.json").write_text(json.dumps(command, indent=2) + "\n")
    process = subprocess.run(command, capture_output=True, text=True, timeout=60)
    (artifact_dir / "cloc.json").write_text(process.stdout)
    (artifact_dir / "cloc.stderr").write_text(process.stderr)
    if process.returncode:
        raise RuntimeError(f"cloc exited {process.returncode}: {process.stderr.strip()}")
    report = json.loads(process.stdout)
    record = report.get(str(artifact_dir / "input.masked.smt2"))
    if record is None and masked.strip():
        raise RuntimeError("cloc did not report input.masked.smt2")
    return dict(input_code_loc=record["code"] if record is not None else 0,
                input_tokens=len(tokens), input_bytes=len(text.encode("utf-8")),
                input_structure=structure)


def measure(input_text, generated_text, artifact_dir, cloc_path="cloc"):
    """Measure one pair with one cloc invocation; retain counting artifacts and structure."""
    artifact_dir = Path(artifact_dir).resolve()
    artifact_dir.mkdir(parents=True, exist_ok=True)
    statements, metric = split_generated_source(generated_text)
    input_tokens, input_comments = _lex(input_text, "smt")
    output_tokens, output_comments = _lex(metric, "lean")
    masked_input = _mask_comments(input_text, input_comments)
    masked_output = _mask_comments(metric, output_comments)
    files = {"statements.lean": statements, "statement-metrics.lean": metric,
             "input.masked.smt2": masked_input, "output.masked.txt": masked_output,
             "output.cloc.lean": _cloc_projection(masked_output, output_tokens),
             "smt-cloc.lang": SMT_CLOC_CONFIG}
    for name, content in files.items():
        (artifact_dir / name).write_bytes(content.encode("utf-8"))
    command = [str(cloc_path), "--json", "--by-file", "--quiet", "--skip-uniqueness",
               "--read-lang-def=" + str(artifact_dir / "smt-cloc.lang"),
               str(artifact_dir / "input.masked.smt2"), str(artifact_dir / "output.cloc.lean")]
    (artifact_dir / "cloc-command.json").write_text(json.dumps(command, indent=2) + "\n")
    process = subprocess.run(command, capture_output=True, text=True, timeout=60)
    (artifact_dir / "cloc.json").write_text(process.stdout)
    (artifact_dir / "cloc.stderr").write_text(process.stderr)
    if process.returncode:
        raise RuntimeError(f"cloc exited {process.returncode}: {process.stderr.strip()}")
    report = json.loads(process.stdout)
    def code_lines(filename, masked):
        record = report.get(str(artifact_dir / filename))
        if record is None:
            if masked.strip():
                raise RuntimeError(f"cloc did not report {filename}")
            return 0
        return record["code"]
    result = dict(input_code_loc=code_lines("input.masked.smt2", masked_input),
                  output_code_loc=code_lines("output.cloc.lean", masked_output),
                  input_tokens=len(input_tokens), output_tokens=len(output_tokens),
                  input_bytes=len(input_text.encode("utf-8")),
                  output_bytes=len(generated_text.encode("utf-8")),
                  output_statement_bytes=len(metric.encode("utf-8")),
                  input_structure=_input_structure(input_tokens),
                  output_structure=_generated_structure(metric, output_tokens))
    for name, numerator, denominator in (
        ("code_loc_ratio", "output_code_loc", "input_code_loc"),
        ("token_ratio", "output_tokens", "input_tokens"),
        ("byte_ratio", "output_bytes", "input_bytes"),
        ("statement_byte_ratio", "output_statement_bytes", "input_bytes"),
    ):
        result[name] = result[numerator] / result[denominator] if result[denominator] else None
    return result
