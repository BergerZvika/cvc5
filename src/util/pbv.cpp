#include "util/pbv.h"
#include <iostream>

namespace cvc5::internal {


Pbv::Pbv(const Integer& val) : d_val(val) {}

const Integer& Pbv::getValue() const { return d_val; }

bool Pbv::operator==(const Pbv& other) const {
  return d_val == other.d_val;
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
  return Pbv( sum);
}

std::string Pbv::toString() const {
  return d_val.toString();
}

std::ostream& operator<<(std::ostream& out, const Pbv& val) {
    return out << val.toString() << " " << "PBitVec";
}




namespace pbv {


size_t PbvHashFunction::operator()(const cvc5::internal::Pbv& s) const {
  return 0;
}

}  // namespace pbv

}  // namespace cvc5::internal