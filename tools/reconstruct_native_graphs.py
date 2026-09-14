"""Rebuild whole native graphs and their complete original-subject comparisons."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name="native-graphs",
    roots=("Native_Graph_Investigation_Execution",),
    export="Native_Graph_Investigation_Execution:native_graph_investigation.ML",
    session="Native_Graph_Reconstruction",
    groups=((Execution("comparison", "check_native_graphs.py",
                       ("--project", "{project}"), 2100),),),
    boundary=("A run without --proof reconstructs the complete contracts from HOL. The graph "
              "constructor receives the complete original environment, graph and root. It preserves "
              "every original node and indexed discharge through a fresh injective correspondence, "
              "installs the whole artifact and reference family, and recovers the graph through the "
              "actual native reader. Every original input, candidate environment, complete map, "
              "graph, reading, assessment, comparison and revision is reproduced. The independent "
              "mapping condition permits alternative placements. These conditions do not validate "
              "inference claims, position certificates, provide native mathematical-proof checking, "
              "enforce the complete development cycle, establish the full physical cost account "
              "or authorize genesis."))


if __name__ == "__main__":
    raise SystemExit(main(RECIPE, __file__))
