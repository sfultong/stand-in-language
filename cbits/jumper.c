#include <stdio.h>
#include <setjmp.h>
#include <stdint.h>
#define GC_THREADS 1
#include <gc.h>

static jmp_buf buf;

// note: setjmp/longjump uses int, not int64_t. May be a problem?
int64_t w_setjmp () {
  return setjmp(buf);
}

void w_longjmp (int64_t x) {
  longjmp(buf,x);
}

void SIL_register_my_thread(void) {
    struct GC_stack_base sb;
    GC_get_stack_base(&sb);
    GC_register_my_thread(&sb);
}
