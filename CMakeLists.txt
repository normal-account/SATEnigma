cmake_minimum_required(VERSION 3.16)
project(TP)

set(CMAKE_CXX_STANDARD 20)
SET(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++1z -Wall -O3")
add_executable(TP cadical.hpp main.cpp)
target_link_libraries(TP ${CMAKE_SOURCE_DIR}/libcadical.a)
