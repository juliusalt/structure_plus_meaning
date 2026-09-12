"""Rebuild native child validation from its complete source and fixture boundary."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name="native-child",
    roots=("Inference_Claim_Input_Execution",),
    export="Inference_Claim_Input_Execution:inference_claim_input.ML",
    session="Native_Child_Reconstruction",
    groups=(
        (Execution("baseline", "check_nonempty_construction_inputs.py"),
         Execution("catalog", "check_child_primitives.py", ("--project", "{project}"))),
        (Execution("inputs", "check_proved_nonempty_inputs.py", ("--baseline", "{output}/baseline")),),
        (Execution("reasoning", "check_proved_nonempty_reasoning.py",
                   ("--catalog", "{output}/catalog", "--inputs", "{output}/inputs"), 1200),)),
    boundary=("A run without --proof reconstructs proof, exported code, baseline inputs and all native checks "
              "from repository sources. The optional supplied-export mode rechecks execution only. "
              "The assertion child remains an assumption; whole-graph and closed-proof admission are separate."))


if __name__ == "__main__":
    raise SystemExit(main(RECIPE, __file__))
