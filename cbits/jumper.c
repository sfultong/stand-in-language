#include <stdio.h>
#include <setjmp.h>
#include <stdint.h>

static jmp_buf buf;

// note: setjmp/longjump uses int, not int64_t. May be a problem?
int64_t w_setjmp () {
  return setjmp(buf);
}

void w_longjmp (int64_t x) {
  longjmp(buf,x);
}
