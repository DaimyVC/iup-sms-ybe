add_executable(ybe_sms "main.cpp" "clause.cpp"  "domains.cpp" "useful.cpp" "solveCadicalClass.cpp" "solveGeneral.cpp" "minCheckCommon.cpp" "minCheck_V2.cpp" "incr_minCheck.cpp") 
target_link_libraries(ybe_sms PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/../../cadical-master/build/libcadical.a")

include_directories(${Boost_INCLUDE_DIRS}) 
target_link_libraries(ybe_sms PRIVATE ${Boost_LIBRARIES})

find_package(OpenMP REQUIRED)
target_link_libraries(ybe_sms PRIVATE OpenMP::OpenMP_CXX)

set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -fopenmp") 

target_compile_options(ybe_sms PRIVATE "-Wall" "-Wextra" "-pedantic" "-O3")


add_executable(diag_maker "main_diagMaker.cpp" "useful.cpp" "domains.cpp")
