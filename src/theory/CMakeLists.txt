###############################################################################
# Top contributors (to current version):
#   José Neto, Aina Niemetz, Mathias Preiner
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
##

libcvc5_add_sources(GENERATED
  rewriter_tables.h
  theory_traits.h
  pbv/theory_pbv_rewriter.cpp
  pbv/theory_pbv_rewriter.h
  pbv/theory_piand_rewriter.cpp
  pbv/theory_piand_rewriter.h
  pbv/theory_exp_rewriter.cpp
  pbv/theory_exp_rewriter.h
  type_enumerator.cpp
)

set(mktheorytraits_script ${CMAKE_CURRENT_LIST_DIR}/mktheorytraits.py)
set(mkrewriter_script ${CMAKE_CURRENT_LIST_DIR}/mkrewriter.py)

add_custom_command(
  OUTPUT rewriter_tables.h
  COMMAND
    ${Python_EXECUTABLE}
    ${mkrewriter_script}
    --template ${CMAKE_CURRENT_LIST_DIR}/rewriter_tables_template.h
    --output ${CMAKE_CURRENT_BINARY_DIR}/rewriter_tables.h
    --kinds ${KINDS_TOML_FILES}
  DEPENDS mkrewriter.py rewriter_tables_template.h ${KINDS_TOML_FILES}
)

add_custom_command(
  OUTPUT theory_traits.h
  COMMAND
    ${Python_EXECUTABLE}
    ${mktheorytraits_script}
    --template ${CMAKE_CURRENT_LIST_DIR}/theory_traits_template.h
    --output ${CMAKE_CURRENT_BINARY_DIR}/theory_traits.h
    --kinds ${KINDS_TOML_FILES}
  DEPENDS mktheorytraits.py theory_traits_template.h ${KINDS_TOML_FILES}
)

add_custom_command(
  OUTPUT type_enumerator.cpp
  COMMAND
    ${Python_EXECUTABLE}
    ${mktheorytraits_script}
    --template ${CMAKE_CURRENT_LIST_DIR}/type_enumerator_template.cpp
    --output ${CMAKE_CURRENT_BINARY_DIR}/type_enumerator.cpp
    --kinds ${KINDS_TOML_FILES}
  DEPENDS mktheorytraits.py type_enumerator_template.cpp ${KINDS_TOML_FILES}
)

set(gen_pbv_rewriter_script
  ${CMAKE_CURRENT_LIST_DIR}/pbv/generate_rewriter.py)

# Format the generated PBV rewriters with the project's .clang-format, if
# clang-format is available (otherwise the files are left as generated).
find_program(CLANG_FORMAT_EXECUTABLE NAMES clang-format)
set(pbv_clang_format_style ${PROJECT_SOURCE_DIR}/.clang-format)
if(CLANG_FORMAT_EXECUTABLE)
  set(pbv_format_deps ${pbv_clang_format_style})
endif()

# Generate pbv/<base>.h and pbv/<base>.cpp from the RARE file pbv/<rewrites>
# with generate_rewriter.py --profile <profile>. The header does not depend on
# the rules, so editing a rule recompiles only the generated .cpp.
function(pbv_generate_rewriter profile rewrites base)
  set(out_dir ${CMAKE_CURRENT_BINARY_DIR}/pbv)
  if(CLANG_FORMAT_EXECUTABLE)
    set(fmt_h COMMAND ${CLANG_FORMAT_EXECUTABLE} -i
      --style=file:${pbv_clang_format_style} ${out_dir}/${base}.h)
    set(fmt_cpp COMMAND ${CLANG_FORMAT_EXECUTABLE} -i
      --style=file:${pbv_clang_format_style} ${out_dir}/${base}.cpp)
  endif()
  add_custom_command(
    OUTPUT
      pbv/${base}.h
    COMMAND
      ${Python_EXECUTABLE}
      ${gen_pbv_rewriter_script}
      --profile ${profile}
      --only header
      --output-dir ${out_dir}
    ${fmt_h}
    DEPENDS
      ${gen_pbv_rewriter_script}
      ${pbv_format_deps}
    COMMENT
      "Generating ${base}.h"
  )
  add_custom_command(
    OUTPUT
      pbv/${base}.cpp
    COMMAND
      ${Python_EXECUTABLE}
      ${gen_pbv_rewriter_script}
      --profile ${profile}
      --only impl
      --output-dir ${out_dir}
    ${fmt_cpp}
    DEPENDS
      ${gen_pbv_rewriter_script}
      ${pbv_format_deps}
      ${CMAKE_CURRENT_LIST_DIR}/pbv/${rewrites}
      ${CMAKE_CURRENT_LIST_DIR}/../rewriter/mkrewrites.py
      ${CMAKE_CURRENT_LIST_DIR}/../rewriter/node.py
      ${CMAKE_CURRENT_LIST_DIR}/../rewriter/rule.py
      ${CMAKE_CURRENT_LIST_DIR}/../rewriter/rw_parser.py
      ${CMAKE_CURRENT_LIST_DIR}/../rewriter/util.py
    COMMENT
      "Generating ${base}.cpp from pbv/${rewrites}"
  )
endfunction()

pbv_generate_rewriter(pbv rewrites theory_pbv_rewriter)
pbv_generate_rewriter(piand rewrites-piand theory_piand_rewriter)
pbv_generate_rewriter(exp rewrites-exp theory_exp_rewriter)

add_custom_target(gen-theory
  DEPENDS
    type_enumerator.cpp
    theory_traits.h
    rewriter_tables.h
    pbv/theory_pbv_rewriter.cpp
    pbv/theory_pbv_rewriter.h
    pbv/theory_piand_rewriter.cpp
    pbv/theory_piand_rewriter.h
    pbv/theory_exp_rewriter.cpp
    pbv/theory_exp_rewriter.h
)
