#include <stdio.h>

#include "Verifier/SAW/ForeignExport_stub.h"
#include "saw.h"

int main(int argc, char **argv) {
    hs_init(&argc, &argv);
    HsStablePtr sc = saw_new_context();
    HsStablePtr bt = saw_bool_type(sc);
    HsStablePtr nc = saw_nat_const(sc, 12839);
    printf("Shared context: %p\n", sc);
    printf("Bool type: %p\n", bt);
    printf("Bool type pretty-printed: %s\n", (char *)saw_pretty_print(bt));
    printf("Nat const pretty-printed: %s\n", (char *)saw_pretty_print(nc));
    saw_free(bt);
    saw_free(nc);
    saw_free(sc);
    hs_exit();
}
