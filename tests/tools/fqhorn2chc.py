#!/usr/bin/env python3
"""Translate a liquid-fixpoint horn file (the `(var $k ..)` / `(constraint ..)`
s-expression format that LiquidHaskell and Flux emit) into a CHC-COMP style
SMT-LIB file for z3/Spacer.

Each kvar becomes an uninterpreted predicate; each leaf of the nested
`forall` tree becomes one Horn clause.  Concrete heads `p` become query
clauses `(=> (and guards (not p)) false)`.
"""
import re
import sys


def tokenize(s):
    s = re.sub(r";[^\n]*", "", s)
    return re.findall(r'\(|\)|"[^"]*"|[^\s()]+', s)


def parse(tokens):
    stack = [[]]
    for t in tokens:
        if t == "(":
            stack.append([])
        elif t == ")":
            x = stack.pop()
            stack[-1].append(x)
        else:
            stack[-1].append(t)
    return stack[0]


def sanitize(name):
    name = name.lstrip("$")
    name = re.sub(r"_?#+", "_", name)
    return name


SORTS = {"int": "Int", "Int": "Int", "bool": "Bool", "Bool": "Bool", "real": "Real", "Real": "Real"}


def sort(s):
    if isinstance(s, str):
        return SORTS[s]
    if s[0] == "BitVec":
        return f"(_ BitVec {s[1].replace('Size', '')})"
    raise ValueError(f"unsupported sort {s}")


OPS = {"/": "div", "<=>": "=", "!=": "distinct", "&&": "and", "||": "or"}


class Translator:
    def __init__(self, kvars):
        self.kvars = kvars  # original name -> (clean name, arg sorts)
        self.clauses = []
        self.counter = 0

    def fresh(self, x, used):
        base = sanitize(x) if x != "_$" else "_g"
        if base not in used:
            return base
        while True:
            self.counter += 1
            cand = f"{base}_{self.counter}"
            if cand not in used:
                return cand

    def expr(self, e, env):
        if isinstance(e, str):
            return env.get(e, e)
        if len(e) == 1:
            return self.expr(e[0], env)
        if e[0] == "-" and len(e) == 2 and isinstance(e[1], str) and e[1].isdigit():
            return ["-", e[1]]
        head = OPS.get(e[0], e[0]) if isinstance(e[0], str) else self.expr(e[0], env)
        return [head] + [self.expr(a, env) for a in e[1:]]

    def is_kapp(self, p):
        return isinstance(p, list) and p and isinstance(p[0], str) and p[0] in self.kvars

    def preds(self, p, env):
        """Flatten a predicate into a list of atoms (SMT exprs)."""
        if isinstance(p, list) and len(p) == 1 and isinstance(p[0], list):
            return self.preds(p[0], env)
        if isinstance(p, list) and p and p[0] == "and":
            return [a for q in p[1:] for a in self.preds(q, env)]
        if isinstance(p, list) and p and p[0] == "tag":
            return self.preds(p[1], env)
        if self.is_kapp(p):
            return [[self.kvars[p[0]][0]] + [self.expr(a, env) for a in p[1:]]]
        e = self.expr(p, env)
        return [] if e == "true" else [e]

    def walk(self, c, env, binders, guards):
        if isinstance(c, list) and c and c[0] == "and":
            for sub in c[1:]:
                self.walk(sub, env, binders, guards)
            return
        if isinstance(c, list) and c and c[0] == "forall":
            (x, s), p = c[1][0][:2], c[1][1] if len(c[1]) > 1 else ["true"]
            if len(c[1][0]) == 3:  # ((x S) P) packed as one list in some dumps
                p = c[1][0][2]
            used = {b for b, _ in binders}
            x2 = self.fresh(x, used)
            env2 = dict(env)
            env2[x] = x2
            self.walk(c[2], env2, binders + [(x2, sort(s))], guards + self.preds(p, env2))
            return
        if isinstance(c, list) and c and c[0] == "tag":
            self.walk(c[1], env, binders, guards)
            return
        for head in self.head_atoms(c, env):
            self.clauses.append((binders, guards, head))

    def head_atoms(self, c, env):
        if isinstance(c, list) and len(c) == 1 and isinstance(c[0], list) and c[0] and c[0][0] in ("and", "tag"):
            return self.head_atoms(c[0], env)
        if isinstance(c, list) and c and c[0] == "and":
            return [a for q in c[1:] for a in self.head_atoms(q, env)]
        if isinstance(c, list) and c and c[0] == "tag":
            return self.head_atoms(c[1], env)
        if self.is_kapp(c):
            return [("kapp", self.preds(c, env)[0])]
        return [("query", a) for a in self.preds(c, env)]


def fmt(e):
    if isinstance(e, str):
        return e
    return "(" + " ".join(fmt(a) for a in e) + ")"


def symbols(e, acc):
    if isinstance(e, str):
        acc.add(e)
    else:
        for a in e:
            symbols(a, acc)
    return acc


def translate(src):
    top = parse(tokenize(src))
    kvars = {}
    constraint = None
    for item in top:
        if item[0] == "var":
            kvars[item[1]] = (sanitize(item[1]), [sort(s) for s in item[2]])
        elif item[0] == "constraint":
            constraint = item[1]
    t = Translator(kvars)
    t.walk(constraint, {}, [], [])

    out = ["(set-logic HORN)", ""]
    for _, (name, sorts) in kvars.items():
        out.append(f"(declare-fun {name} ({' '.join(sorts)}) Bool)")
    out.append("")
    for binders, guards, (kind, head) in t.clauses:
        body = list(guards)
        if kind == "query":
            body.append(["not", head])
            hd = "false"
        else:
            hd = fmt(head)
        body_s = "true" if not body else fmt(body[0]) if len(body) == 1 else "(and " + " ".join(fmt(g) for g in body) + ")"
        occ = set()
        for g in body:
            symbols(g, occ)
        if kind == "kapp":
            symbols(head, occ)
        bs = [(b, s) for b, s in binders if b in occ]
        clause = f"(=> {body_s} {hd})"
        if bs:
            clause = f"(forall ({' '.join(f'({b} {s})' for b, s in bs)})\n          {clause})"
        out.append(f"(assert {clause})")
    out += ["", "(check-sat)", "(exit)"]
    return "\n".join(out) + "\n"


if __name__ == "__main__":
    sys.stdout.write(translate(open(sys.argv[1]).read()))
