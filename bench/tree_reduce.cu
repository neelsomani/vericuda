#include <cuda_runtime.h>

#include <cassert>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>

#define CUDA_OK(call) do { \
  cudaError_t status = (call); \
  if (status != cudaSuccess) { \
    std::fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, \
                 cudaGetErrorString(status)); \
    return 1; \
  } \
} while (0)

__global__ void fixed_tree_reduce(const float* input, float* result, int count) {
  __shared__ float partial[256];
  float local = 0.0f;
  for (int index = threadIdx.x; index < count; index += blockDim.x) {
    local += input[index];
  }
  partial[threadIdx.x] = local;
  __syncthreads();
  for (int stride = blockDim.x / 2; stride > 0; stride >>= 1) {
    if (threadIdx.x < stride) partial[threadIdx.x] += partial[threadIdx.x + stride];
    __syncthreads();
  }
  if (threadIdx.x == 0) *result = partial[0];
}

int main(int argc, char** argv) {
  const char* csv_path = nullptr;
  if (argc == 3 && std::strcmp(argv[1], "--csv") == 0) {
    csv_path = argv[2];
  } else if (argc != 1) {
    std::fprintf(stderr, "usage: %s [--csv output.csv]\n", argv[0]);
    return 2;
  }

  constexpr int count = 1 << 20;
  constexpr int runs = 1000;
  std::vector<float> host(count);
  for (int i = 0; i < count; ++i) {
    host[i] = (static_cast<int>(i % 257) - 128) * 0.0001f;
  }

  float* device_input = nullptr;
  float* device_result = nullptr;
  CUDA_OK(cudaMalloc(&device_input, count * sizeof(float)));
  CUDA_OK(cudaMalloc(&device_result, sizeof(float)));
  CUDA_OK(cudaMemcpy(device_input, host.data(), count * sizeof(float),
                     cudaMemcpyHostToDevice));

  std::uint32_t expected = 0;
  for (int run = 0; run < runs; ++run) {
    fixed_tree_reduce<<<1, 256>>>(device_input, device_result, count);
    CUDA_OK(cudaGetLastError());
    float result = 0.0f;
    CUDA_OK(cudaMemcpy(&result, device_result, sizeof(float),
                       cudaMemcpyDeviceToHost));
    std::uint32_t bits = 0;
    std::memcpy(&bits, &result, sizeof(bits));
    if (run == 0) expected = bits;
    if (bits != expected) {
      std::fprintf(stderr,
                   "fixed tree changed result at run %d: expected 0x%08x, "
                   "observed 0x%08x\n",
                   run, expected, bits);
      assert(bits == expected && "fixed tree changed its result bit pattern");
      return 1;
    }
  }

  std::printf("fixed tree: one result bit pattern in %d runs: 0x%08x\n",
              runs, expected);

  if (csv_path != nullptr) {
    std::FILE* csv = std::fopen(csv_path, "w");
    if (csv == nullptr) {
      std::perror(csv_path);
      return 1;
    }
    std::fprintf(csv, "bits,count\n0x%08x,%d\n", expected, runs);
    std::fclose(csv);
  }

  cudaFree(device_result);
  cudaFree(device_input);
  return 0;
}
