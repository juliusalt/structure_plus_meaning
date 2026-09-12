"""Complete application subjects shared by construction and observation adapters."""
import investigate
import check_reasoning as review

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


def normalized_schema(schema):
    return {**schema, "premises": set(map(review.freeze, schema["premises"])),
            "materials": set(map(review.freeze, schema["materials"]))}


def normalized_problem(row):
    return {**row, "schema": normalized_schema(row["schema"]),
            **{key: set(map(review.freeze, row[key])) for key in ["frontier", "requests"]},
            "required": {application_key(a) for a in row["required"]}}


def application_key(row):
    return (review.freeze(row["conclusion"]), frozenset(map(review.freeze, row["bindings"])),
            frozenset(map(review.freeze, row["premises"])))

PROBLEM_JSON_PRELUDE='fun jproblem (i,p) = "{\\"id\\":" ^ jnat i ^ ",\\"entry\\":" ^ jnat (N.application_entry p) ^\n ",\\"schema\\":" ^ jschema (N.application_schema p) ^\n ",\\"enumeration\\":" ^ jlist jsymbolic (N.application_enumeration p) ^\n ",\\"frontier\\":" ^ jf jcall (N.application_frontier p) ^\n ",\\"requests\\":" ^ jf jcall (N.application_requests p) ^\n ",\\"required\\":" ^ jf jlocal (N.application_required p) ^ "}";\n'


def validate_term(term, *, pattern=False):
    assert type(term) is dict and len(term) == 1, "Expected one complete term constructor."
    if "var" in term:
        assert pattern and investigate.natural(term["var"])
    elif "pair" in term:
        assert type(term["pair"]) is list and len(term["pair"]) == 2
        for child in term["pair"]:
            validate_term(child, pattern=pattern)
    elif "payload" in term:
        assert type(term["payload"]) is list and all(investigate.natural(x) for x in term["payload"])
    else:
        assert set(term) == {"empty_artifact"} and term["empty_artifact"] is True


def validate_rows(rows, *, premise=False, pattern=False):
    assert type(rows) is list
    for row in rows:
        assert type(row) is list and len(row) == (3 if premise else 2)
        assert all(investigate.natural(x) for x in row[:-1])
        validate_term(row[-1], pattern=pattern)


def validate_application(row, *, owner=None):
    fields = {"conclusion", "bindings", "premises"}
    assert type(row) is dict and fields <= set(row) <= fields | {"entry", "schema"}
    if set(row) != fields:
        assert owner is not None and set(row) == fields | {"entry", "schema"}
        assert investigate.natural(row["entry"]) and row["entry"] == owner["entry"]
        validate_schema(row["schema"])
        assert normalized_schema(row["schema"]) == normalized_schema(owner["schema"])
    validate_term(row["conclusion"])
    validate_rows(row["bindings"])
    validate_rows(row["premises"], premise=True)


def validate_schema(schema):
    assert type(schema) is dict and set(schema) == {"head", "premises", "materials"}
    validate_term(schema["head"], pattern=True)
    validate_rows(schema["premises"], premise=True, pattern=True)
    assert type(schema["materials"]) is list
    for material in schema["materials"]:
        assert type(material) is list and len(material) == 2 and investigate.natural(material[0])
        assert type(material[1]) is list and len(material[1]) == 5
        for field in material[1]:
            validate_term(field, pattern=True)


def validate_problem(row):
    assert type(row) is dict and set(row) == {"id", "entry", "schema", "enumeration", "frontier", "requests", "required"}
    assert investigate.natural(row["id"]) and investigate.natural(row["entry"])
    validate_schema(row["schema"])
    validate_rows(row["enumeration"], premise=True, pattern=True)
    validate_rows(row["frontier"])
    validate_rows(row["requests"])
    assert type(row["required"]) is list
    for target in row["required"]:
        validate_application(target, owner=row)
