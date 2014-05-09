typedef void (*VOIDFUN)();
void EntryPoint() {
  static char bytes[] =
#include "x86/wrapperdata.c"
  ;
  { VOIDFUN vf = (VOIDFUN) bytes;
    (*vf)(); }
}
