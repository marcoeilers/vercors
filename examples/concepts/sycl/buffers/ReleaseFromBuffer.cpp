#include <sycl/sycl.hpp>

/*@ 
  requires \pointer(a, 10, write);
*/
void main(bool* a) {
  {
    sycl::buffer<bool, 1> aBuffer = sycl::buffer(a, sycl::range<1>(10));

    int b = 20;
  }
  // Buffer should be destroyed now, so permissions should have been given back
  a[5] = true;
}