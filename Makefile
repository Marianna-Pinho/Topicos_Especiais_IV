CFLAGS = -I  cudd-3.0.0 cudd-3.0.0/cudd -I cudd-3.0.0/util -I /cudd-3.0.0
LFLAGS = -static -L cudd-3.0.0/cudd/.libs/ -lcudd -lm

teste = transitions04
ext =  cpp
comp = g++ -std=c++11
default:	testprogram

testprogram: $(teste).o
	$(comp) $(teste).o -o testprogram -I cudd-3.0.0/cudd -I cudd-3.0.0/util -I cudd-3.0.0/ -static -L cudd-3.0.0/cudd/.libs/ -lcudd -lm
$(teste).o:	$(teste).$(ext)
	$(comp) $(teste).$(ext) -c -o $(teste).o -I cudd-3.0.0/cudd -I cudd-3.0.0/util -I cudd-3.0.0/ -static -L cudd-3.0.0/cudd/.libs/ -lcudd -lm
$(teste).$(ext):
	$(comp) $(teste).$(ext) -c -I cudd-3.0.0/cudd -I cudd-3.0.0/util -I cudd-3.0.0/ -static -L cudd-3.0.0/cudd/.libs/ -lcudd -lm
clean:
	rm -f *.o testprogram