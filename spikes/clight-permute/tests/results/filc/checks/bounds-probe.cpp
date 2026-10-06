#include <vector>
int main(int argc,char **argv) { (void)argv; std::vector<unsigned> p(1); volatile unsigned *q=p.data(); q[argc]=42; return 0; }
