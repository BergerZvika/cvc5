/******************************************************************************
 * Top contributors (to current version):
 *   Diego Della Rocca de Camargos, Haniel Barbosa, Vinícius Braga Freire
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for printing dot proofs.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__DOT__DOT_PRINTER_H
#define CVC5__PROOF__DOT__DOT_PRINTER_H

#include <iostream>

#include "printer/let_binding.h"
#include "proof/proof_node.h"

namespace cvc5::internal {
namespace proof {

class DotPrinter
{
 public:
  DotPrinter();
  ~DotPrinter();

  /**
   * Print the full proof of assertions => false by pn using the dot format.
   * @param out the output stream
   * @param pn the root node of the proof to print
   */
  void print(std::ostream& out, const ProofNode* pn);

 private:
  /**
   * Print the nodes of the proof in the format:
   * $NODE_ID [ label = "{$CONCLUSION|$RULE_NAME($RULE_ARGUMENTS)}",
   * $COLORS_AND_CLASSES_RELATED_TO_THE_RULE ]; and then for each child of the
   * node $CHILD_ID -> $NODE_ID; and then recursively calls the function with
   * the child as argument.
   * @param out the output stream
   * @param pn the proof node to print
   * @param pfLet the map of the hashs of proof nodes already printed to their ids
   * @param scopeCounter counter of how many SCOPE were already depth-first
   * traversed in the proof up to this point
   * @param inPropositionalView flag used to mark the proof node being traversed
   * was generated by the SAT solver and thus belong to the propositional view
   * @return the id of the proof node printed
   */
  uint64_t printInternal(std::ostream& out,
                         const ProofNode* pn,
                         std::map<size_t, uint64_t>& pfLet,
                         uint64_t scopeCounter,
                         bool inPropositionalView);

  /**
   * Return the arguments of a ProofNode
   * @param currentArguments an ostringstream that will store the arguments of
   * pn formatted as "$ARG[0], $ARG[1], ..., $ARG[N-1]"
   * @param pn a ProofNode
   */
  void ruleArguments(std::ostringstream& currentArguments, const ProofNode* pn);

  /** Add an escape character before special characters of the given string.
   * @param s The string to have the characters processed.
   * @return The string with the special characters escaped.
   */
  static std::string sanitizeString(const std::string& s);

  /** As above, but quotes are doubly escaped. */
  static std::string sanitizeStringDoubleQuotes(const std::string& s);

  /** Traverse proof node and populate d_subpfCounter, mapping each proof node
   * to the number of subproofs it contains, including itself
   *
   * @param pn the proof node to be traversed
   */
  void countSubproofs(const ProofNode* pn);

  /** Traverse proof node and populate d_lbind
   *
   * @param pn the proof node to be traversed
   */
  void letifyResults(const ProofNode* pn);

  /** All unique subproofs of a given proof node (counting itself). */
  std::map<const ProofNode*, size_t> d_subpfCounter;

  /** Let binder for terms in proof nodes */
  LetBinding d_lbind;

  /** Counter that indicates the current rule ID */
  uint64_t d_ruleID;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
