"""Readable, independently expandable notations for packed reference material.

These are display abbreviations, not Isabelle syntax or new logical rules.
Names retain their original order. Declaration bodies are never factored.
"""
import re

NAME = r"[A-Za-z_][A-Za-z_0-9']*"
FACTS = re.compile(r"\(\* proved here: ([^\n]*?) \*\)")
FACT_GROUP = re.compile(r"(" + NAME + r"_)\{([A-Za-z_0-9']+(?:,[A-Za-z_0-9']+)*)\}|(" + NAME + r")")


def fact_groups(names):
    """Find short contiguous prefix groups, keeping the original names/order."""
    n = len(names)
    costs, choices = [0] * (n + 1), [None] * n
    for i in range(n - 1, -1, -1):
        costs[i], choices[i] = len(names[i]) + 2 + costs[i + 1], (i + 1, "")
        for boundary in re.finditer("_", names[i]):
            prefix = names[i][:boundary.end()]
            if prefix == "_":
                continue
            group_size = len(prefix) + 2
            for j in range(i, n):
                if not names[j].startswith(prefix) or names[j] == prefix:
                    break
                group_size += len(names[j]) - len(prefix) + (1 if j > i else 0)
                cost = group_size + 2 + costs[j + 1]
                if j > i and cost < costs[i]:
                    costs[i], choices[i] = cost, (j + 1, prefix)
    out, i = [], 0
    while i < n:
        j, prefix = choices[i]
        out.append(prefix + "{" + ",".join(name[len(prefix):] for name in names[i:j]) + "}"
                   if prefix else names[i])
        i = j
    return ", ".join(out)


def expand_fact_body(body):
    names, position = [], 0
    while position < len(body):
        match = FACT_GROUP.match(body, position)
        if not match:
            raise ValueError("invalid packed fact-name group")
        if match[1]:
            names.extend(match[1] + suffix for suffix in match[2].split(","))
        else:
            names.append(match[3])
        position = match.end()
        if position < len(body):
            if body[position:position + 2] != ", ":
                raise ValueError("invalid separator in fact-name list")
            position += 2
            if position == len(body):
                raise ValueError("trailing separator in fact-name list")
    return ", ".join(names)


def fact_edits(text, literal_notes=()):
    edits = []
    for match in FACTS.finditer(text):
        if match[0] in literal_notes:
            continue
        names = match[1].split(", ")
        if not all(re.fullmatch(NAME, name) for name in names):
            continue
        body = fact_groups(names)
        if len(body) < len(match[1]):
            if expand_fact_body(body) != match[1]:
                raise ValueError("fact factoring changed names or order")
            edits.append((match.start(1), match.end(1), body))
    return edits


def expand_facts(text, literal_notes=()):
    def expand(match):
        if match[0] in literal_notes or "{" not in match[1]:
            return match[0]
        return "(* proved here: " + expand_fact_body(match[1]) + " *)"
    return FACTS.sub(expand, text)


def theory_name(text):
    match = re.match(r"theory\s+(" + NAME + r")(?=\s|$)", text)
    return match[1] if match else None
