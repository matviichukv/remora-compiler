#include <cstdio>
#include <algorithm>
#include <iostream>
#include <vector>
#include <highfive/highfive.hpp>

static void HandleError(cudaError_t err, const char *file, int line) {
  if (err != cudaSuccess) {
    printf("%s in %s at line %d\12", cudaGetErrorString(err),
            file, line);
    exit(EXIT_FAILURE);
  }
}
#define HANDLE_ERROR(err) (HandleError( err, __FILE__, __LINE__ ))

template<typename T>
T *mallocHost(int64_t count) {
  return (T *) malloc(count * sizeof(T));
};

template<typename T>
__host__ T *mallocDevice(int64_t count) {
  T* array;
  HANDLE_ERROR(cudaMalloc((void **) &array, count * sizeof(T)));
  return array;
};

template<typename T>
__device__ T *mallocDeviceOnDevice(int64_t count) {
  return (T *) malloc(count * sizeof(T));
};

template<typename T>
T* copyHostToDeviceMalloc(T* hostArray, int64_t count) {
  T* deviceArray = mallocDevice<T>(count);
  HANDLE_ERROR(cudaMemcpy(deviceArray, hostArray, count * sizeof(T), cudaMemcpyHostToDevice));
  return deviceArray;
};

template<typename T>
T* copyDeviceToHostMalloc(T* deviceArray, int64_t count) {
  T* hostArray = mallocHost<T>(count);
  HANDLE_ERROR(cudaMemcpy(hostArray, deviceArray, count * sizeof(T), cudaMemcpyDeviceToHost));
  return hostArray;
};

template<typename T>
T* copyHostToDevice(T* deviceArray, T* hostArray, int64_t count) {
  HANDLE_ERROR(cudaMemcpy(deviceArray, hostArray, count * sizeof(T), cudaMemcpyHostToDevice));
  return deviceArray;
};

template<typename T>
T* copyDeviceToHost(T* hostArray, T* deviceArray, int64_t count) {
  HANDLE_ERROR(cudaMemcpy(hostArray, deviceArray, count * sizeof(T), cudaMemcpyDeviceToHost));
  return hostArray;
};

template<typename T>
void copyHostToHost(T* dest, T* source, int64_t count) {
  memcpy(dest, source, count * sizeof(T));
};

template<typename T>
void copyDeviceToDevice(T* dest, T* source, int64_t count) {
  HANDLE_ERROR(cudaMemcpy(dest, source, count * sizeof(T), cudaMemcpyDeviceToDevice));
};

template<typename T>
__host__ __device__ void copySameLoc(T* dest, T* source, int64_t count) {
  for (int64_t i = 0; i < count; i++) {
    dest[i] = source[i];
  }
};

struct Slice {
  int64_t* dims;
  int64_t dimCount;
};

int64_t sum(int64_t* arr, int64_t count) {
  int64_t s = 0;
  for(int64_t i = 0; i < count; i++) {
    s += arr[i];
  }
  return s;
};

__host__ __device__ int64_t sum(Slice slice) {
  int64_t s = 0;
  for(int64_t i = 0; i < slice.dimCount; i++) {
    s += slice.dims[i];
  }
  return s;
};

__host__ __device__ int64_t product(Slice slice) {
  int64_t p = 1;
  for(int64_t i = 0; i < slice.dimCount; i++) {
    p *= slice.dims[i];
  }
  return p;
};

template<typename T>
T at(T* elements, std::vector<int64_t> shape, std::vector<int64_t> index) {
  int64_t elementIndex = 0;
  int64_t stride = 1;
  for (auto i = index.size() - 1;; i--) {
    elementIndex += stride * index[i];
    stride *= shape[i];

    if (i == 0) break;
  }
  return elements[elementIndex];
};

template<typename T>
void printArray(T* elements, int64_t* dims, int64_t dimCount) {
  if (dimCount == 0) {
    std::cout << elements[0] << "\12";
    return;
  }

  std::vector<int64_t> indexes(dimCount, 0);

  while (true) {
    for (auto i = (int64_t)indexes.size() - 1; i >= 0; i--) {
      if (indexes[i] == 0) std::cout << "[";
      else break;
    }

    std::cout << at(elements, std::vector<int64_t>(dims, dims + dimCount), indexes);

    long i = (long)indexes.size() - 1;
    while (true) {
      if (i < 0) {
        std::cout << "\12";
        return;
      }

      indexes[i]++;
      if (indexes[i] == dims[i]) {
        std::cout << "]";
        indexes[i] = 0;
        i--;
      } else {
        if (i == indexes.size() - 1) std::cout << " ";
        else {
          std::cout << "\12";
          for (long j = 0; j <= i; j++) {
            std::cout << " ";
          }
        }
        break;
      }
    }
  }
};

std::unordered_map<std::string, HighFive::File> files;

template <typename T>
void readH5(std::string filename, std::string dataset_name, T* data, size_t size) {
  auto entry = files.find(filename);
  if (entry == files.end()) {
    HighFive::File file(filename);
    files.insert(std::make_pair(filename, file));
    entry = files.find(filename);
  }
  auto dataset = (*entry).second.getDataSet(dataset_name);
  size_t datasetSize = dataset.getElementCount();
  assert(datasetSize == size);
  dataset.read(data);
}

int main() {
    HANDLE_ERROR(cudaDeviceSetLimit(cudaLimitMallocHeapSize, (INT64_C(8589934592) / INT64_C(10))));
    cudaEvent_t start;
    cudaEvent_t stop;
    cudaEventCreate(&start);
    cudaEventCreate(&stop);
    cudaEventRecord(start);
    float* readH5Result_160 = mallocHost<float>((INT64_C(1) * INT64_C(64)));
    readH5<float>("/home/vadym/Downloads/imagenet-vgg-verydeep-16-vadym.h5", "/conv1_1/conv1_1_B", readH5Result_160, (INT64_C(1) * INT64_C(64)));
    cudaEventRecord(stop);
    cudaEventSynchronize(stop);
    auto dimCount_161 = INT64_C(1);
    auto dims_162 = mallocHost<int64_t>(dimCount_161);
    dims_162[INT64_C(0)] = INT64_C(64);
    printArray<float>(readH5Result_160, dims_162, dimCount_161);
    float millis = 0.;
    cudaEventElapsedTime(&millis, start, stop);
    ((std::cout << millis) << '\12');
}
