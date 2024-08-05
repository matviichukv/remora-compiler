#include <highfive/highfive.hpp>

std::unordered_map<std::string, HighFive::File> files;

template <typename T>
void readH5(std::string filename, std::string dataset_name, size_t size,
            T *data) {
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
  std::string foo =
      "/home/vadym/Downloads/vgg16_weights_tf_dim_ordering_tf_kernels.h5";
  // HighFive::File file(foo);

  auto dataset_name = "/block3_conv3/block3_conv3_W_1:0";
  float *data = (float *)malloc(sizeof(float) * 3 * 3 * 256 * 256);
  // dataset.read(&data);
  readH5<float>(foo, dataset_name, 3 * 3 * 256 * 256, data);
  std::cout << data[0] << std::endl;
  free(data);
}
