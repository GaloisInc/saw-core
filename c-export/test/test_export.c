#include <stdio.h>

#include "Verifier/SAW/ForeignExport_stub.h"
#include "saw.h"

int main(int argc, char **argv) {
    hs_init(&argc, &argv);
    HsStablePtr sc = saw_new_context();
    HsStablePtr bt = saw_bool_type(sc);
    printf("Shared context: %p\n", sc);
    printf("Bool type: %p\n", bt);
    printf("Bool type pretty-printed: %s\n", (char *)saw_pretty_print(bt));
    saw_free(bt);
    saw_free(sc);
    hs_exit();
}
