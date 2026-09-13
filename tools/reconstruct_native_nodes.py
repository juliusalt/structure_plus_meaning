"""Rebuild complete native proof-node construction and its actual source investigation."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name="native-nodes",
    roots=("Native_Node_Investigation_Execution",),
    export="Native_Node_Investigation_Execution:native_node_investigation.ML",
    session="Native_Node_Reconstruction",
    groups=((Execution("comparison", "check_native_nodes.py",
                       ("--project", "{project}"), 2100),),),
    boundary=("A run without --proof reconstructs the complete contracts from HOL. The node compiler "
              "constructs both node forms with the original clause, complete binding family and every "
              "indexed target. Local installation retains the actual source and recovers the complete "
              "node through the existing native reader. Every original input, candidate environment, "
              "native reading, condition assessment, comparison and revision is reproduced. "
              "The finite scope does not establish arbitrary-method coverage, inference validity, "
              "whole proof-graph construction or replay, native mathematical-proof checking, complete "
              "development-cycle enforcement, the whole cost account or genesis."))


if __name__ == "__main__":
    raise SystemExit(main(RECIPE, __file__))
