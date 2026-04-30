#ifndef CVC5__UTIL__PBV_VALUE_H
#define CVC5__UTIL__PBV_VALUE_H

#include <string>
#include <iosfwd>
#include "util/integer.h" // Assuming we use Integer to represent the bits initially

namespace cvc5::internal {

namespace pbv {
  struct PbvHashFunction;
}  // namespace pbv


/**
 * A class representing a concrete Parametric Bit-Vector value.
 * For now, it wraps an integer, but in your full implementation, 
 * this might need to hold size information or be distinct from standard BV.
 */
class Pbv {
  friend pbv::PbvHashFunction;

 public:
  Pbv(const Integer& val);
  Pbv(const Integer& val, const Integer& size);
  Pbv() = default;
  ~Pbv() {}

  const Integer& getValue() const;
  const Integer& getSize() const;

  // Comparison operators required for the theory mechanism
  bool operator==(const Pbv& other) const;
  bool operator!=(const Pbv& other) const;
  bool operator<(const Pbv& other) const;

  // String representation for printing
  std::string toString() const;

 private:
  Integer d_val;
  Integer d_size;
};


namespace pbv {

struct PbvHashFunction {
  size_t operator()(const cvc5::internal::Pbv& s) const;
};

}  // namespace pbv


// Stream operator for debugging
std::ostream& operator<<(std::ostream& os, const Pbv& val);

/* Arithmetic operations ------------------------------------------------- */
/**
* @return A bit-vector representing the addition of bit-vectors `a` and `b`.
*/
Pbv operator+(const Pbv& a, const Pbv& b);

// struct PbvType
// {
//   unsigned d_size;
//   PbvType() : d_size(0) {}
//   PbvType(unsigned size) : d_size(size) {}
//   operator unsigned() const { return d_size; }
// }; /* struct PbvType */

}  // namespace cvc5::internal

#endif