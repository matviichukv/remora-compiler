cmake_minimum_required(VERSION 3.6 FATAL_ERROR)

project(H5Test LANGUAGES CXX CUDA)

SET(GCC_COVERAGE_COMPILE_FLAGS "-g -G")

#find_package(HighFive REQUIRED)
set(HIGHFIVE_USE_BOOST Off)
find_package(HDF5 REQUIRED)
include(FetchContent)
FetchContent_Declare(HighFive
  GIT_REPOSITORY "https://github.com/BlueBrain/HighFive"
  GIT_TAG "v2.9.0"
)
FetchContent_MakeAvailable(HighFive)
#set(HDF5_USE_STATIC_LIBRARIES On)

add_executable(h5test h5test.cpp)
target_link_libraries(h5test HighFive HDF5::HDF5)

add_executable(test test.cu)
target_link_libraries(test HighFive HDF5::HDF5)
