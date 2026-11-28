#!/usr/bin/env python3
"""Generate the case scripts of `StepInstr.exec_complete` / `StepTerm.exec_complete`
(LeanNanoLlvm/Semantics/Determinism.lean) from the rules of LeanNanoLlvm/Semantics/Step.lean.

Every premise of a regular rule is an operand evaluation (`EvalExp`/`EvalExpList`, ok or error),
an oracle existential (`∃ o o', f o = .ok _` / `∃ o, f o = .error _`), or an equation; the script
runs the interpreter with the rule's oracle (or `default`), rewrites each operand evaluation with
its interpreter result (`EvalExp.exec_ok`/`exec_err`), and closes the goal by `simp`. Rules listed
in MANUAL are written by hand in Determinism.lean.

Usage: det_cases.py StepInstr|StepTerm > cases.lean
"""
import re
import sys

MANUAL = set()


def rules(rel):
    s = open("LeanNanoLlvm/Semantics/Step.lean").read()
    i = s.index("inductive " + rel)
    ends = [x for x in (s.find("\ninductive", i + 10), s.find("\ntheorem", i + 10)) if x > 0]
    body = s[i:min(ends)]
    parts = re.split(r"\n  \| ", body)[1:]
    out = []
    for p in parts:
        name = p.split()[0]
        p = re.sub(r"\n\s*/-.*?-/", "", p, flags=re.S)
        sig = p[p.index(":") + 1:] if "} :" in p or ":\n" in p else p
        sig = sig[sig.index(":") + 1:] if sig.startswith(" {") else sig
        # premises: split at top-level arrows
        prem, depth, cur = [], 0, ""
        for ch_i, ch in enumerate(sig):
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
            if ch == "→" and depth == 0:
                prem.append(cur.strip()); cur = ""
            else:
                cur += ch
        out.append((name, prem, cur.strip()))
    return out


def kind(pr):
    if pr.startswith("EvalExpList "):
        return "listok" if "(.ok" in pr else "listerr"
    if pr.startswith("EvalExp "):
        return "expok" if "(.ok" in pr else "experr"
    if pr.startswith("(∃ o o'"):
        return "exok"
    if pr.startswith("(∃ o,"):
        return "exerr"
    return "eq"


def script(name, prem, concl, rel):
    hs = [f"h{i}" for i in range(len(prem))]
    ks = [kind(p) for p in prem]
    if any(k == "eq" and not re.match(r"^[\w.\s()]*=|.*= \.(ok|error|some|none)", p) for k, p in zip(ks, prem)):
        pass
    lines = [f"  | {name} {' '.join(hs)} =>"]
    unf = "Instruction.choiceFreeSyn" if rel == "StepInstr" else "Terminator.choiceFreeSyn"
    lines.append(f"    simp only [{unf}, Bool.and_eq_true] at hcf")
    O = "default"
    rw = []
    errs = 0
    for h, k in zip(hs, ks):
        if k == "exok":
            lines.append(f"    obtain ⟨o, _, {h}⟩ := {h}"); O = "o"; rw.append(h)
        elif k == "exerr":
            lines.append(f"    obtain ⟨o, {h}⟩ := {h}"); O = "o"; rw.append(h)
    for h, k in zip(hs, ks):
        if k in ("expok", "listok"):
            lines.append(f"    have {h}' := {h}.exec_ok (by simp_all) {O}"); rw.append(h + "'")
        elif k in ("experr", "listerr"):
            lines.append(f"    obtain ⟨e', {h}', he⟩ := {h}.exec_err (by simp_all) {O}"); rw.append(h + "'"); errs += 1
        elif k == "eq":
            rw.append(h)
    fn = "execInstr" if rel == "StepInstr" else "execTerm"
    rws = ", ".join([fn] + rw)
    if errs:
        lines.append(f"    exact ⟨{O}, by simp [{rws}], by simp [{rws}, -Config.ofError]; exact Config.ofError_erase_eq he⟩")
    else:
        lines.append(f"    exact ⟨{O}, by simp [{rws}]⟩")
    return "\n".join(lines)


if __name__ == "__main__":
    rel = sys.argv[1]
    skip = set(sys.argv[2:])
    for name, prem, concl in rules(rel):
        if name in skip:
            continue
        print(script(name, prem, concl, rel))
