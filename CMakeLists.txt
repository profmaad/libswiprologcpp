cmake_minimum_required(VERSION 2.6 FATAL_ERROR)

project(libswiprologcpp)

include(FindPkgConfig)

pkg_check_modules(SWIPL REQUIRED swipl)
include_directories(${SWIPL_INCLUDE_DIRS})
link_directories(${SWIPL_LIBRARY_DIRS})
add_definitions(${SWIPL_DEFINITIONS})

add_library(swiprologcpp SHARED src/prolog.cpp)
target_link_libraries(swiprologcpp ${SWIPL_LIBRARIES})

configure_file(libswiprologcpp.pc.in libswiprologcpp.pc @ONLY)

install(TARGETS swiprologcpp LIBRARY DESTINATION lib)
install(FILES src/prolog.hpp DESTINATION include/swiprolog-cpp)
install(FILES ${PROJECT_BINARY_DIR}/libswiprologcpp.pc DESTINATION lib/pkgconfig)