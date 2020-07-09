cmake_minimum_required(VERSION 3.3)
project(telomare-c-tests)

#rapid check, property based testing for C++
add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/rapidcheck/)

#Include Telomare.h files.
include_directories(../cbits/include)


set (Telomare_FILES ../cbits/Telomare.c)
set (Telomare_TEST_FILES tests.cpp)

add_executable(telomare-c-tests ${Telomare_FILES} ${Telomare_TEST_FILES})
target_link_libraries(telomare-c-tests rapidcheck)

