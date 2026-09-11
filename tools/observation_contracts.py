"""Read the typed subject equations exported by their checked Isabelle owner."""
from __future__ import annotations

from pathlib import Path


def parse_yxml(raw):
    """Read Isabelle's XML tree representation without changing term nodes."""
    roots = []
    stack = [roots]
    for chunk in raw.split("\x05"):
        if not chunk:
            continue
        if chunk == "\x06":
            if len(stack) == 1:
                raise ValueError("Unmatched YXML closing element.")
            stack.pop()
        elif chunk.startswith("\x06"):
            fields = chunk.split("\x06")[1:]
            if not fields[0]:
                raise ValueError("A YXML element must have a name.")
            attributes = []
            for field in fields[1:]:
                key, separator, value = field.partition("=")
                if not key or not separator or key in dict(attributes):
                    raise ValueError("Malformed or repeated YXML attribute.")
                attributes.append((key, value))
            node = {"tag": fields[0], "attributes": dict(attributes), "body": []}
            stack[-1].append(node)
            stack.append(node["body"])
        else:
            if "\x06" in chunk:
                raise ValueError("Unframed YXML control character.")
            stack[-1].append(chunk)
    if len(stack) != 1 or len(roots) != 1 or not isinstance(roots[0], dict):
        raise ValueError("Expected one complete YXML document.")
    return roots[0]


def only_element(body):
    if len(body) != 1 or not isinstance(body[0], dict):
        raise ValueError("Expected one complete typed term element.")
    return body[0]


def constant_head(body):
    """Select a Const head from Term_XML.Encode.term_raw applications."""
    node = only_element(body)
    while node["tag"] == "5":
        pair = node["body"]
        if len(pair) != 2 or any(p["tag"] != ":" for p in pair):
            raise ValueError("Malformed typed application.")
        node = only_element(pair[0]["body"])
    if node["tag"] != "0" or set(node["attributes"]) != {"0"} or not node["body"]:
        raise ValueError("Expected an explicitly typed constant head.")
    return node["attributes"]["0"]


def read_contract(path, theory, function):
    root = parse_yxml(Path(path).read_text())
    if root["tag"] != "finite_observation_contract":
        raise ValueError("Expected a checked finite-observation contract.")
    fields = {}
    for node in root["body"]:
        if not isinstance(node, dict) or node["tag"] in fields:
            raise ValueError("Malformed or repeated contract field.")
        fields[node["tag"]] = node
    expected = {"candidate_indices", "facet_indices", "function", "observer", "relation", "subjects", "calculation",
                "observation_equation", "functional_maps", "at_subject",
                "comparison_at_subject", "definitions", "context_constants"}
    if fields.keys() != expected or len(fields["subjects"]["body"]) != 4:
        raise ValueError("The complete subject contract must retain every field.")
    names = {field: constant_head(fields[field]["body"])
             for field in ["function", "observer", "relation"]}
    required = {"function": function, "observer": function + "_observations",
                "relation": function + "_relation"}
    for field, name in names.items():
        if name.split(".")[-2:] != [theory, required[field]]:
            raise ValueError("The typed contract belongs to a different runtime operation.")
    if root["attributes"] != {"function": names["function"]}:
        raise ValueError("The contract identity must equal its actual typed function.")
    definitions = fields["definitions"]["body"]
    if not definitions or any(d["tag"] != "definition" for d in definitions):
        raise ValueError("The contract must retain its actual defining equations.")
    domains = {}
    for field in ["candidate_indices", "facet_indices"]:
        rows = fields[field]["body"]
        if any(not isinstance(row, dict) or row["tag"] != ":" or row["attributes"]
               or len(row["body"]) != 1 or not isinstance(row["body"][0], str)
               or not row["body"][0].isdigit() for row in rows):
            raise ValueError("The candidate and facet domains must be actual natural-number lists.")
        domains[field] = [int(row["body"][0]) for row in rows]
    return {**domains, "function": names["function"], "observer": names["observer"],
            "relation": names["relation"], "definition_count": len(definitions),
            "context_constant_count": len(fields["context_constants"]["body"]),
            "term_format": "Isabelle Term_XML.Encode.term_raw in YXML",
            "boundary": "The checked owner connects this calculation to these actual subject maps and their exact observation equation. Reachable kernel definitions accompany the full typed theorem terms; remaining constants belong to the accepted Isabelle context."}
