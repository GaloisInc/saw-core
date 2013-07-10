#include <stdlib.h>
#include "HsFFI.h"

#include "saw.h"

void saw_init() {
  int argc = 0;
  char *argv[] = { NULL };
  char **pargv = argv;

  hs_init(&argc, &pargv);
}

void saw_cleanup() {
  hs_exit();
}
