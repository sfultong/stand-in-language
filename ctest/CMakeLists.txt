cmake_minimum_required(VERSION 3.3)
project(stand-in-language-c-tests)

#rapid check, property based testing for C++
add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/rapidcheck/)

#Include SIL.h files.
include_directories(../cbits/include)


set (SIL_FILES ../cbits/SIL.c)
set (SIL_TEST_FILES tests.cpp)

add_executable(sil-c-tests ${SIL_FILES} ${SIL_TEST_FILES})
target_link_libraries(sil-c-tests rapidcheck)

