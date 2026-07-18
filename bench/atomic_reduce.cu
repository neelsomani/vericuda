#include <cuda_runtime.h>

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <map>
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

  std::map<std::uint32_t, int> histogram;
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
    ++histogram[bits];
  }

  std::printf("atomicAdd: %zu distinct result bit patterns in %d runs\n",
              histogram.size(), runs);
  for (const auto& [bits, frequency] : histogram) {
    std::printf("0x%08x,%d\n", bits, frequency);
  }

  if (csv_path != nullptr) {
    std::FILE* csv = std::fopen(csv_path, "w");
    if (csv == nullptr) {
      std::perror(csv_path);
      return 1;
    }
    std::fprintf(csv, "bits,count\n");
    for (const auto& [bits, frequency] : histogram) {
      std::fprintf(csv, "0x%08x,%d\n", bits, frequency);
    }
    std::fclose(csv);
  }

  cudaFree(device_result);
  cudaFree(device_input);
  return 0;
}
