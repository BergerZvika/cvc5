#include "util/pbv.h"
#include <iostream>

namespace cvc5::internal {


Pbv::Pbv(const Integer& val) : d_val(val), d_size(0) {}

Pbv::Pbv(const Integer& val, const Integer& size) : d_val(val), d_size(size) {}

const Integer& Pbv::getValue() const { return d_val; }

const Integer& Pbv::getSize() const { return d_size; }

bool Pbv::operator==(const Pbv& other) const {
  return d_val == other.d_val && d_size == other.d_size;
}

bool Pbv::operator!=(const Pbv& other) const {
  return !(*this == other);
}

bool Pbv::operator<(const Pbv& other) const {
  return d_val < other.d_val;
}

/* Arithmetic operations ------------------------------------------------- */

Pbv operator+(const Pbv& a, const Pbv& b)
{
  Integer sum = a.getValue() + b.getValue();
  return Pbv(sum, a.getSize());
}

std::string Pbv::toString() const {
  // Render as `(_ pbv <value> <width>)` so the printed model carries both
  // the integer value and the symbolic bit-width.
  std::string s = "(_ pbv ";
  s += d_val.toString();
  s += " ";
  s += d_size.toString();
  s += ")";
  return s;
}

std::ostream& operator<<(std::ostream& out, const Pbv& val) {
    return out << val.toString();
}




namespace pbv {


size_t PbvHashFunction::operator()(const cvc5::internal::Pbv& s) const {
  return 0;
}

}  // namespace pbv

}  // namespace cvc5::internal