#include <stdlib.h>
int main(int argc,char **argv) { (void)argv; unsigned *p=malloc(sizeof(*p)); if (!p) return 2; ((volatile unsigned *)p)[argc]=42; free(p); return 0; }
