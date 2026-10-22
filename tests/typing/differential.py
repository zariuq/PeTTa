#!/usr/bin/env python3
"""Differential typing audit: generated typed programs run checked, with every
check (--oracle) and erased (--no-type-checks).

The invariants are those tests/typing/run.sh checks on its fixed programs:
- the checked run and the oracle run give the same output and exit status
  (which check reports a type error first is not compared);
- a checked run that raises no type error gives what the erased run gives.

The generator samples the surface where check elimination and held checks can
go wrong: a value of each kind of type (primitives, a closed name with
constructors, a union, a list, a tuple, a refinement, a parameterized
constructor), given literally, hidden behind an untyped function (no static
evidence), or left open and bound after its check, and passed by a direct
call, a call through a variable, reduce, a space, a curried function, an
overload, a polymorphic function, a typed space, or collapse. A program that
breaks an invariant is shrunk to a minimal one and printed.

Usage: python3 tests/typing/differential.py [--n N] [--seed S] [--jobs J] [--keep DIR]
"""
import argparse
import concurrent.futures
import os
import random
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

PRELUDE = """\
(: Shape Type)
(: circle (-> Number Shape))
(: rect (-> Number Number Shape))
(: Colour Type)
(: red Colour)
(: green Colour)
(: is-even (-> Number Bool))
(= (is-even $n) (== (% $n 2) 0))
(: Even (Refine Number is-even))
(: Maybe (-> Type Type))
(: some (-> $a (Maybe $a)))
(: none (Maybe $a))
(= (hide $x) $x)
(: poly-id (-> $a $a))
(= (poly-id $x) $x)
(: poly-bad (-> $a $a))
(= (poly-bad $x) (hide "s"))
(: Meters (Newtype Number))
!(bind! &fns (new-space))
!(bind! &rows (new-space))"""

# For each type: good values, bad values, and open values (a template with one
# variable $x and the type that variable must have).
TYPES = {
    'Number': (['3', '-2'], ['"s"', 'True', 'red'], [('$x', 'Number')]),
    'String': (['"a"'], ['1'], [('$x', 'String')]),
    'Bool': (['True', 'False'], ['1', '"t"'], [('$x', 'Bool')]),
    'Shape': (['(circle 1)', '(rect 1 2)'], ['(circle "x")', 'red', '3'],
              [('(circle $x)', 'Number'), ('(rect 1 $x)', 'Number')]),
    'Colour': (['red', 'green'], ['blue', '1'], [('$x', 'Colour')]),
    '(List Number)': (['(1 2)', '()'], ['(1 "a")'], [('($x 2)', 'Number'), ('(1 $x)', 'Number')]),
    '(List Shape)': (['((circle 1))'], ['((circle 1) red)'], [('((circle $x))', 'Number')]),
    '(Number String)': (['(1 "a")'], ['("a" 1)', '(1)'], [('($x "a")', 'Number'), ('(1 $x)', 'String')]),
    '(| Number String)': (['1', '"a"'], ['True'], [('$x', '(| Number String)')]),
    '(| Shape Colour)': (['red', '(circle 2)'], ['3'], [('(circle $x)', 'Number')]),
    'Even': (['4'], ['3'], [('$x', 'Even')]),
    '(Maybe Number)': (['(some 1)', 'none'], ['(some "s")'], [('(some $x)', 'Number')]),
    'Meters': (['(brand Meters 3)'], ['"s"'], [('$x', 'Number')]),
    '(List (| Number Shape))': (['(1 (circle 2))'], ['(1 red)'], [('($x (circle 2))', '(| Number Shape)'),
                                                                   ('((circle $x))', 'Number')]),
}
SCALAR = {'Number': '"s"', 'String': '1', 'Bool': '1'}   # a primitive other than the type


def value(rng, t, pbad):
    good, bad, _ = TYPES[t]
    return rng.choice(bad) if rng.random() < pbad else rng.choice(good)


def leaf(rng, t, pbad):
    """A value bound to an open part of type t: good or bad."""
    if t in TYPES:
        return value(rng, t, pbad)
    return '"s"' if rng.random() < pbad else '1'


def program(rng):
    t = rng.choice(sorted(TYPES))
    pbad = rng.choice([0.0, 0.0, 0.15, 0.4])          #half the programs have no bad value
    other = rng.choice([u for u in ['Number', 'String', 'Bool'] if u != t] or ['Bool'])
    defs = [f"(: f (-> {t} {t}))", "(= (f $x) $x)"]
    runs = []
    for _ in range(rng.randint(2, 5)):
        kind = rng.choice(['direct', 'hidden', 'result', 'open', 'var', 'reduce', 'space', 'curried',
                           'overload', 'poly', 'polybad', 'the', 'typed-space', 'collapse', 'effect', 'hold',
                           'open-hidden', 'open-var', 'open-overload', 'open-curried', 'open-the', 'open-rows',
                           'open-equation', 'open-two-types'])
        if pbad == 0 and kind in ('polybad', 'open-two-types'):
            kind = 'direct'
        v = value(rng, t, pbad)
        tmpl, lt = rng.choice(TYPES[t][2])
        lv = leaf(rng, lt, pbad)
        bound = tmpl.replace('$x', lv)
        if kind == 'direct':
            runs.append(f"!(f {v})")
        elif kind == 'hidden':
            runs.append(f"!(f (hide {v}))")
        elif kind == 'result':
            n = len(defs)
            defs += [f"(: g{n} (-> {t}))", f"(= (g{n}) (hide {v}))"]
            runs.append(f"!(g{n})")
        elif kind == 'open':
            runs.append(f"!(let $v {tmpl} (let $_ (f $v) (let {bound} $v $v)))")
        elif kind == 'var':
            runs.append(f"!(let $h f ($h (hide {v})))")
        elif kind == 'reduce':
            runs.append(f"!(reduce (f (hide {v})))")
        elif kind == 'space':
            runs.append("!(add-atom &fns f)")
            runs.append(f"!(match &fns $h ($h (hide {v})))")
        elif kind == 'curried':
            if "(: cur " not in "\n".join(defs):
                defs += [f"(: base2 (-> Number {t} {t}))", "(= (base2 $n $x) $x)",
                         f"(: cur (-> Number (-> {t} {t})))", "(= (cur $n) (base2 $n))"]
            runs.append(rng.choice([f"!(cur 1 (hide {v}))", f"!((cur 1) (hide {v}))",
                                    f"!(let $c (cur 1) ($c (hide {v})))"]))
        elif kind == 'overload':
            if "(: ov " not in "\n".join(defs):
                defs += [f"(: ov (-> {t} {t}))", f"(: ov (-> {other} {other}))", "(= (ov $x) $x)"]
            runs.append(rng.choice([f"!(ov (hide {v}))", f"!(let $o ov ($o (hide {v})))"]))
        elif kind == 'poly':
            runs.append(f"!(f (poly-id (hide {v})))")
        elif kind == 'polybad':
            runs.append(f"!(f (poly-bad {rng.choice(TYPES[t][0])}))")
        elif kind == 'the':
            runs.append(f"!(the {t} (hide {v}))")
        elif kind == 'typed-space':
            if "(: &typed " not in "\n".join(defs):
                defs.append(f"(: &typed (SpaceOf (box {t})))")
                runs.append("!(bind! &typed (new-space))")
            runs.append(rng.choice([f"!(add-atom &typed (box (hide {v})))",
                                    f"!(let $r (hide {v}) (add-atom &typed (box $r)))",
                                    f"!(let $v {tmpl} (add-atom &typed (box $v)))"]))
            runs.append(rng.choice(["!(collapse (match &typed (box $y) (f $y)))",
                                    f"!(collapse (match &typed (box {bound}) found))"]))
        elif kind == 'collapse':
            runs.append(f"!(let ($c) (collapse (let $u {tmpl} (let $_ (f $u) $u))) (let {bound} $c $c))")
        elif kind == 'effect':
            runs.append(f"!(f (progn (println! effect) (hide {v})))")
        elif kind == 'open-hidden':
            runs.append(f"!(let $v {tmpl} (let $_ (f (hide $v)) (let {bound} (hide $v) $v)))")
        elif kind == 'open-var':
            runs.append(f"!(let $v {tmpl} (let $h f (let $_ ($h $v) (let {bound} $v $v))))")
        elif kind == 'open-overload':
            if "(: ov " not in "\n".join(defs):
                defs += [f"(: ov (-> {t} {t}))", f"(: ov (-> {other} {other}))", "(= (ov $x) $x)"]
            runs.append(f"!(let $v {tmpl} (let $_ (ov $v) (let {bound} $v $v)))")
        elif kind == 'open-curried':
            if "(: cur " not in "\n".join(defs):
                defs += [f"(: base2 (-> Number {t} {t}))", "(= (base2 $n $x) $x)",
                         f"(: cur (-> Number (-> {t} {t})))", "(= (cur $n) (base2 $n))"]
            runs.append(f"!(let $v {tmpl} (let $_ (cur 1 $v) (let {bound} $v $v)))")
        elif kind == 'open-the':
            runs.append(f"!(let $v {tmpl} (let $_ (the {t} $v) (let {bound} $v $v)))")
        elif kind == 'open-rows':
            runs.append(f"!(let $v {tmpl} (let $_ (f $v) (add-atom &rows (r $v))))")
            runs.append(f"!(collapse (match &rows (r {bound}) found))")
        elif kind == 'open-equation':
            n = len(defs)
            runs.append(f"!(let $v {tmpl} (let $_ (f $v) (add-atom &self (= (cap{n}) $v))))")
            runs.append(f"!(let {bound} (cap{n}) ok)")
        elif kind == 'open-two-types':
            u = rng.choice(sorted(TYPES))
            n = len(defs)
            defs += [f"(: k{n} (-> {u} {u}))", f"(= (k{n} $x) $x)"]
            runs.append(f"!(let $v {tmpl} (let $_ (f $v) (let $_ (k{n} $v) (let {bound} $v $v))))")
        elif kind == 'hold':
            if "(: keep " not in "\n".join(defs):
                defs += ["(: keep (-> Atom Number Atom))", "(= (keep $x $n) $x)"]
            src = f"(progn (println! held) {v})"
            runs.append(rng.choice([f"!(keep {src} 1)", f"!(let $k keep ($k {src} 1))",
                                    f"!(reduce (keep {src} 1))"]))
    return PRELUDE.split("\n") + defs + runs


def normalize(text):
    text = text.replace(ROOT + "/", "")
    text = re.sub(r"\$_[0-9]+", "$_", text)
    return re.sub(r"^\(Error \(.*\) typecheck\)$", "(Error typecheck)", text, flags=re.M)


def run(path, flag):
    cmd = ["sh", os.path.join(ROOT, "run.sh"), path, "--silent"] + ([flag] if flag else [])
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
        return p.returncode, normalize(p.stdout)
    except subprocess.TimeoutExpired:
        return 'timeout', ''


def divergence(lines, tmpdir, erased=None):
    """None if the program keeps the invariants, else what breaks; erased
    collects whether the erasure invariant applied."""
    fd, path = tempfile.mkstemp(suffix=".metta", dir=tmpdir)
    with os.fdopen(fd, "w") as f:
        f.write("\n".join(lines) + "\n")
    try:
        c = run(path, None)
        o = run(path, "--oracle")
        if c != o:
            return "oracle", c, o
        if c[0] == 0:
            if erased is not None:
                erased.append(1)
            e = run(path, "--no-type-checks")
            if c != e:
                return "erasure", c, e
        return None
    finally:
        os.unlink(path)


def shrink(lines, kind, tmpdir):
    """Drop lines while the same invariant still breaks."""
    changed = True
    while changed:
        changed = False
        for i in range(len(lines)):
            cand = lines[:i] + lines[i + 1:]
            d = divergence(cand, tmpdir)
            if d and d[0] == kind:
                lines, changed = cand, True
                break
    return lines


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=40)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--keep", help="directory to write shrunk counterexamples to")
    a = ap.parse_args()
    programs = [program(random.Random(a.seed * 100003 + i)) for i in range(a.n)]
    with tempfile.TemporaryDirectory() as tmpdir:
        with concurrent.futures.ThreadPoolExecutor(a.jobs) as pool:
            erased = []
            results = list(pool.map(lambda p: divergence(p, tmpdir, erased), programs))
        failures = [(p, r) for p, r in zip(programs, results) if r]
        for k, (p, r) in enumerate(failures):
            small = shrink(p, r[0], tmpdir)
            d = divergence(small, tmpdir) or r
            print(f"--- counterexample {k + 1}: {d[0]} differs")
            print("\n".join(small))
            print(f"--- checked: {d[1]}\n--- other:   {d[2]}")
            if a.keep:
                os.makedirs(a.keep, exist_ok=True)
                with open(os.path.join(a.keep, f"seed{a.seed}-{k + 1}.metta"), "w") as f:
                    f.write("\n".join(small) + "\n")
    print(f"differential typing audit: {a.n} programs (seed {a.seed}, {len(erased)} without a type error), "
          f"{len(failures)} break an invariant")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
