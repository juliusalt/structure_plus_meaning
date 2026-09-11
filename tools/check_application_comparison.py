#!/usr/bin/env python3
"""Compare actual construction operations on complete structural problems."""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path

import check_reasoning as review
import investigate
import proved_code
import review_investigations


def ml_application(row):
    bindings = investigate.ml_list(row["bindings"], review.ml_call)
    premises = investigate.ml_list(row["premises"], review.ml_premise)
    return "(" + review.ml_term(row["conclusion"]) + ",(fs " + bindings + ",fs " + premises + "))"


def ml_problem(row):
    return ("(" + investigate.ml_nat(row["id"]) + ",N.make_application_problem (" + investigate.ml_nat(row["entry"])
            + ") (" + review.ml_schema(row["schema"], schema_constructor="N.make_finite_schema",
                                       material_constructor="N.make_finite_material") + ") "
            + investigate.ml_list(row["enumeration"], lambda p: review.ml_premise(p, True))
            + " (fs " + investigate.ml_list(row["frontier"], review.ml_call) + ") (fs "
            + investigate.ml_list(row["requests"], review.ml_call) + ") (fs "
            + investigate.ml_list(row["required"], ml_application) + "))")


PRELUDE = "structure N = Application_Comparison;\n" + review.FSET_TERM_SCHEMA_JSON_PRELUDE + review.LOCAL_APPLICATION_JSON_PRELUDE + r'''
fun jmethod N.Separate_Application_Sources = "\"Separate_Application_Sources\""
 | jmethod N.Joined_Application_Observations = "\"Joined_Application_Observations\"";
fun jcondition N.Complete_Instance_Condition = "\"Complete_Instance_Condition\""
 | jcondition N.Existing_Application_Condition = "\"Existing_Application_Condition\""
 | jcondition N.Required_Application_Condition = "\"Required_Application_Condition\"";
fun jsubject value (i,x) = "[" ^ jnat i ^ "," ^ value x ^ "]";
fun jproblem (i,p) = "{\"id\":" ^ jnat i ^ ",\"entry\":" ^ jnat (N.application_entry p) ^
 ",\"schema\":" ^ jschema (N.application_schema p) ^
 ",\"enumeration\":" ^ jlist jsymbolic (N.application_enumeration p) ^
 ",\"frontier\":" ^ jf jcall (N.application_frontier p) ^
 ",\"requests\":" ^ jf jcall (N.application_requests p) ^
 ",\"required\":" ^ jf jlocal (N.application_required p) ^ "}";
fun jpair (a,b) = "[" ^ jnat a ^ "," ^ jnat b ^ "]";
fun jtriple (a,(b,c)) = "[" ^ jnat a ^ "," ^ jnat b ^ "," ^ jnat c ^ "]";
fun jquad (a,(b,(c,d))) = "[" ^ jnat a ^ "," ^ jnat b ^ "," ^ jnat c ^ "," ^ jnat d ^ "]";
fun jprofile (c,p) = "{\"candidate\":" ^ jnat c ^ ",\"profile\":" ^ jlist jpair p ^ "}";
fun jloss (c,(d,p)) = "{\"from\":" ^ jnat c ^ ",\"to\":" ^ jnat d ^ ",\"losses\":" ^ jlist jpair p ^ "}";
fun report ws selected = let
 val (formed,(residual,(profiles,losses))) = N.application_investigation ws selected;
 val observations = N.application_investigation_observations ws;
 val relation = N.application_investigation_relation ws;
 val cs = map #1 (elements N.application_candidate_subjects);
 val fs = map #1 (elements N.application_condition_subjects);
 val (safe,(conflicts,(repairs,unrepairable))) = N.investigation_repairs cs fs selected observations relation;
 val extension = N.investigation_extend selected repairs;
 val (retained,(withdrawn,(newRepairs,(revised,newResidual)))) = N.investigation_revision cs fs selected observations relation;
 val text = "{\"input_formed\":" ^ Bool.toString formed ^ ",\"residual\":" ^ jlist jpair residual ^
  ",\"profiles\":" ^ jlist jprofile profiles ^ ",\"losses\":" ^ jlist jloss losses ^
  ",\"observations\":" ^ jlist jtriple observations ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"safe_facets\":" ^ jlist jnat safe ^ ",\"conflicts\":" ^ jlist jquad conflicts ^
  ",\"repairs\":" ^ jlist jquad repairs ^ ",\"unrepairable\":" ^ jlist jpair unrepairable ^
  ",\"extension\":" ^ jlist jnat extension ^ ",\"revision\":{\"retained\":" ^ jlist jnat retained ^
  ",\"withdrawn\":" ^ jlist jnat withdrawn ^ ",\"repairs\":" ^ jlist jquad newRepairs ^
  ",\"selection\":" ^ jlist jnat revised ^ ",\"residual\":" ^ jlist jpair newResidual ^ "}}"
 in (revised,text) end;
'''


def program(engine, spec):
    source = "use " + investigate.ml_string(str(engine)) + ";\n" + PRELUDE
    source += "val workloads = " + investigate.ml_list(spec["problems"], ml_problem) + ";\n"
    source += "val selected = " + investigate.ml_list(spec["selected"], investigate.ml_nat) + ";\n"
    return source + r'''
val subjects = "{\"formed\":" ^ Bool.toString (N.application_observation_scope workloads) ^
 ",\"candidates\":" ^ jf (jsubject jmethod) N.application_candidate_subjects ^
 ",\"conditions\":" ^ jf (jsubject jcondition) N.application_condition_subjects ^
 ",\"problems\":" ^ jlist jproblem workloads ^ "}";
val () = print ("APPLICATION_SUBJECTS " ^ subjects ^ "\n");
val () = List.app (fn (w,p) => List.app (fn (c,m) => print
 ("APPLICATION_RESULTS " ^ jnat w ^ " " ^ jnat c ^ " " ^
   jf jlocal (N.application_construction_result m p) ^ "\n"))
 (elements N.application_candidate_subjects)) workloads;
val (revised,initial) = report workloads selected;
val (_,followed) = report workloads revised;
val () = print ("APPLICATION_INITIAL " ^ initial ^ "\n");
val () = print ("APPLICATION_FOLLOWED " ^ followed ^ "\n");
'''


def normalized_problem(row):
    return {**row, "schema": {**row["schema"],
            "premises": set(map(review.freeze, row["schema"]["premises"])),
            "materials": set(map(review.freeze, row["schema"]["materials"]))},
            **{key: set(map(review.freeze, row[key])) for key in ["frontier", "requests"]},
            "required": {application_key(a) for a in row["required"]}}


def application_key(row):
    return (review.freeze(row["conclusion"]), frozenset(map(review.freeze, row["bindings"])),
            frozenset(map(review.freeze, row["premises"])))


def assess(spec, raw):
    parsed, application_rows = {}, []
    for line in raw.splitlines():
        if line.startswith("APPLICATION_RESULTS "):
            _, w, c, value = line.split(" ", 3)
            application_rows.append((int(w), int(c), json.loads(value)))
        elif line.startswith(("APPLICATION_SUBJECTS ", "APPLICATION_INITIAL ", "APPLICATION_FOLLOWED ")):
            key, value = line.split(" ", 1)
            assert key not in parsed
            parsed[key] = json.loads(value)
    subjects = parsed["APPLICATION_SUBJECTS"]
    assert subjects["formed"], "Ambiguous source indices cannot establish an observation subject."
    assert [normalized_problem(p) for p in subjects["problems"]] == [normalized_problem(p) for p in spec["problems"]]
    candidates = {i: value for i, value in subjects["candidates"]}
    conditions = {i: value for i, value in subjects["conditions"]}
    assert Counter((w, c) for w, c, _ in application_rows) == Counter(
        (p["id"], c) for p in spec["problems"] for c in candidates)
    applications = {}
    for w, c, values in application_rows:
        if (w, c) in applications:
            assert set(map(application_key, applications[w, c])) == set(map(application_key, values))
        applications[w, c] = values
    initial, followed = parsed["APPLICATION_INITIAL"], parsed["APPLICATION_FOLLOWED"]
    for selected, result in [(spec["selected"], initial), (initial["revision"]["selection"], followed)]:
        assert len(result["profiles"]) == len(candidates)
        assert {p["candidate"] for p in result["profiles"]} == set(candidates)
        case = {"candidates": [p["candidate"] for p in result["profiles"]],
                "facets": list(conditions), "selected": selected}
        mismatches, _, facts = review_investigations.basis_analysis(case, result, {})
        assert not mismatches and result["input_formed"], mismatches
    assert not followed["residual"]
    mandatory = {(f, p["id"]) for f in conditions for p in spec["problems"]}
    observations = set(map(tuple, followed["observations"]))
    for p in spec["problems"]:
        w = p["id"]
        item = {"library": [{"entry": p["entry"], "schema": p["schema"], "enumeration": p["enumeration"]}],
                "frontier": p["frontier"]}
        expected = {
            "Separate_Application_Sources": review.reconstruct_applications(item)[0]
                + review.reconstruct_requested_applications(item, p["requests"]),
            "Joined_Application_Observations": review.reconstruct_observed_applications(item, p["requests"]),
        }
        separate = next(c for c, subject in candidates.items() if subject == "Separate_Application_Sources")
        original = {application_key(a) for a in applications[w, separate]}
        required = {application_key(a) for a in p["required"]}
        for c in candidates:
            returned = {application_key(a) for a in applications[w, c]}
            assert returned == {application_key(a) for a in expected[candidates[c]]}, (w, c)
            for f, subject in conditions.items():
                if subject == "Existing_Application_Condition":
                    assert ((f, c, w) in observations) == (original <= returned)
                elif subject == "Required_Application_Condition":
                    assert ((f, c, w) in observations) == (required <= returned)
    eligible = [c for c in candidates if mandatory <= {(f,w) for f,d,w in observations if d == c}]
    return {"subjects": subjects, "initial": initial, "followed": followed,
            "applications": [{"problem": w, "candidate": c, "values": a} for (w,c), a in applications.items()],
            "mandatory": sorted(mandatory), "eligible": eligible,
            "contract": "application_observation_subject",
            "boundary": "Conditions are computed on the retained structural subjects by the proved operation. Scope is the supplied complete problem family; premise truth and wider method coverage remain separate."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ["specification", "proof", "poly", "output"]:
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if not __debug__:
        raise ValueError("Structural comparison requires Python assertions.")
    spec = json.loads(args.specification.read_text())
    assert set(spec) == {"selected", "problems"}, "Observation rows and prose ratings are not inputs to this operation."
    assert all(investigate.natural(x) for x in spec["selected"])
    receipt = proved_code.checked_execution(args.proof, args.poly, args.output,
        required_theories=["Factor_Application_Execution", "Finite_Derived_Observations"], inputs=spec,
        input_paths=[args.specification], program=program, assess=assess,
        question="Compare complete application construction on the actual supplied schema problems.",
        boundary="The exported candidate, condition and problem subjects own every observation index.")
    print(json.dumps({k:v for k,v in receipt.items() if k not in {"assessment", "execution_inputs", "evidence_archive"}}, indent=2))
    if receipt["status"] == "accepted":
        print(json.dumps({"eligible":receipt["assessment"]["eligible"],
                          "contract":receipt["assessment"]["contract"]}))
    return int(receipt["status"] != "accepted")


if __name__ == "__main__":
    raise SystemExit(main())
