cmake_minimum_required(VERSION 3.10.2 FATAL_ERROR)

set(CMAKE_BUILD_TYPE Release)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_STANDARD 20)

set(PROJECT_NAME AnthonyWilliamsStack)
project(${PROJECT_NAME})

add_executable(tests tests.cpp)
target_link_options(tests PRIVATE -latomic -pthread)
