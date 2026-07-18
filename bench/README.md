# Empirical reduction anchor

These standalone CUDA programs compare an unordered `atomicAdd` reduction with
a fixed shared-memory tree. They are intentionally not part of `make demo`
because the artifact build does not assume a CUDA GPU or toolkit.

The verified Coq kernel is an 8-element model of the tree kernel's
synchronization structure. This benchmark demonstrates the phenomenon the
theorem is about; it is not a verified binary.

The recorded canonical run is in
[`bench/results/b200-sm100-paper-run/`](results/b200-sm100-paper-run/): on an
NVIDIA B200 it produced 965 distinct atomic result patterns versus one fixed
tree pattern, from Git commit `0646418`.

## One-command run

On an NVIDIA CUDA machine, run this from the repository root, replacing
`sm_80` with the architecture of the tested GPU:

```sh
./bench/run_bench.sh sm_80
```

The command compiles and executes both kernels 1,000 times, asserts that the
tree produces one bit pattern, and creates a timestamped directory under
`bench/results/` containing:

- `atomic_histogram.csv` and `tree_histogram.csv`, the raw frequencies;
- `environment.txt`, containing the GPU model, UUID, driver-reported CUDA
  version, CUDA compiler version, requested architecture, Git commit, and UTC
  timestamp;
- `commands.txt`, containing the exact compilation and execution commands;
- the raw program logs.

Pass an explicit output directory as the second argument when desired:

```sh
./bench/run_bench.sh sm_80 bench/results/paper-run
```

Each program reduces the same deterministic array of 1,048,576 floats. The
atomic program records the frequency of every raw result bit pattern; the tree
program fails immediately if a run differs from the first.

The CSV files are ready to plot with any preferred graphing tool. The number
of atomic outcomes is hardware- and run-dependent; the script does not assert
a minimum. The expected qualitative contrast is multiple outcomes for the
unordered atomic reduction and exactly one for the fixed tree.
