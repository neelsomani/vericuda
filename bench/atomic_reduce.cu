#include <cuda_runtime.h>

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <set>
#include <vector>

#define CUDA_OK(call) do { \
  cudaError_t status = (call); \
  if (status != cudaSuccess) { \
    std::fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, \
                 cudaGetErrorString(status)); \
    return 1; \
  } \
} while (0)

__global__ void atomic_reduce(const float* input, float* result, int count) {
  int index = blockIdx.x * blockDim.x + threadIdx.x;
  if (index < count) atomicAdd(result, input[index]);
}

int main() {
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

  std::set<std::uint32_t> patterns;
  for (int run = 0; run < runs; ++run) {
    CUDA_OK(cudaMemset(device_result, 0, sizeof(float)));
    atomic_reduce<<<(count + 255) / 256, 256>>>(device_input, device_result,
                                                count);
    CUDA_OK(cudaGetLastError());
    float result = 0.0f;
    CUDA_OK(cudaMemcpy(&result, device_result, sizeof(float),
                       cudaMemcpyDeviceToHost));
    std::uint32_t bits = 0;
    std::memcpy(&bits, &result, sizeof(bits));
    patterns.insert(bits);
  }

  std::printf("atomicAdd: %zu distinct result bit patterns in %d runs\n",
              patterns.size(), runs);
  for (std::uint32_t bits : patterns) std::printf("0x%08x\n", bits);
  cudaFree(device_result);
  cudaFree(device_input);
  return 0;
}
