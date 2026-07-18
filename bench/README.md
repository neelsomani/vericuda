# Empirical reduction anchor

These standalone CUDA programs compare an unordered `atomicAdd` reduction with
a fixed shared-memory tree. They are intentionally not part of `make demo`
because the artifact build does not assume a CUDA GPU or toolkit.

Record the environment before reporting results:

```sh
nvidia-smi --query-gpu=name,driver_version --format=csv
nvcc --version
```

Build and run:

```sh
nvcc -O3 -arch=sm_80 atomic_reduce.cu -o atomic_reduce
nvcc -O3 -arch=sm_80 tree_reduce.cu -o tree_reduce
./atomic_reduce
./tree_reduce
```

Replace `sm_80` with the tested GPU architecture. Each program reduces the
same deterministic array of 1,048,576 floats 1,000 times. The atomic program
prints every distinct result bit pattern; the tree program aborts if any run
differs from the first.

The verified Coq kernel is an 8-element model of this kernel's synchronization
structure; the benchmark demonstrates the phenomenon the theorem is about,
not a verified binary.
