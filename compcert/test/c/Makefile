include ../../Makefile.config

CCOMP=../../ccomp
CCOMPFLAGS=-stdlib ../../runtime -dc -dclight -dasm
CLANG=clang
CLANGFLAGS=-O1 -Wall -m32 
ifeq ($(CCHECKLINK),true)
CCHECK=../../cchecklink
CCOMPFLAGS+= -sdump
endif

CFLAGS=-O2 -Wall -mfpmath=sse -msse -msse2

LIBS=$(LIBMATH)

#TIME=xtime -o /dev/null -mintime 2.0     # Xavier's hack
TIME=time >/dev/null                    # Otherwise

PROGS=aes almabench binarytrees bisect chomp \
  fannkuch fft fftw fib integr knucleotide \
  lists mandelbrot nbody nsieve nsievebits \
  perlin qsort sha1 sha3 siphash24 spectral \
  vmach verif_hmac

all: $(PROGS:%=%.compcert)

all_nopeep : $(PROGS:%=%.compcert_nopeep)

all_s: $(PROGS:%=%.s)

all_handtuned : $(PROGS:%=%.handtuned)

all_gcc: $(PROGS:%=%.gcc)

all_gcc_nopeep: $(PROGS:%=%.gcc_nopeep)

all_clang: $(PROGS:%=%.clang)

%.compcert: %.c $(CCOMP)
	$(CCOMP) $(CCOMPFLAGS) -o $*.compcert $*.c $(LIBS)
	mv $*.s $*_peeps.s

%.handtuned: %.handtuned.s
	$(CC) $(CFLAGS) -o $*.handtuned $*.handtuned.s $(LIBS)

%.compcert_nopeep: %.c $(CCOMP)
	$(CCOMP) -fno-peeps $(CCOMPFLAGS) -o $*.compcert_nopeep $*.c $(LIBS)
	mv $*.s $*_nopeeps.s

%.s: %.c $(CCOMP)
	$(CCOMP) $(CCOMPFLAGS) -S $*.c

%.gcc: %.c
	$(CC) $(CFLAGS) -o $*.gcc $*.c $(LIBS)
	$(CC) $(CFLAGS) -o $*_gcc.s $*.c $(LIBS) -S

%.gcc_nopeep: %.c
	$(CC) $(CFLAGS) -o $*.gcc $*.c $(LIBS) -fno-peephole -fno-peephole2
	$(CC) $(CFLAGS) -o $*_gccnopeep.s $*.c $(LIBS) -fno-peephole -fno-peephole2 -S	

%.clang: %.c
	$(CLANG) $(CLANGFLAGS) -o $*.clang $*.c $(LIBS)

test:
	@for i in $(PROGS); do \
	   if ./$$i.compcert | cmp -s - Results/$$i; \
           then echo "$$i: passed"; \
           else echo "$$i: FAILED"; \
	   fi; \
         done

ccheck:
	@for i in $(PROGS); do \
           echo "---- $$i"; \
           $(CCHECK) -exe $$i.compcert $$i.sdump; \
         done

test_gcc:
	@for i in $(PROGS); do \
	   if ./$$i.gcc | cmp -s - Results/$$i; \
           then echo "$$i: passed"; \
           else echo "$$i: FAILED"; \
	   fi; \
         done

bench_gcc:
	@for i in $(PROGS); do \
	   echo -n "$$i: "; $(TIME) ./$$i.gcc; \
         done

bench:
	@for i in $(PROGS); do \
	   echo -n "$$i: "; $(TIME) ./$$i.compcert; \
         done

bench_handtuned:
	@for i in $(PROGS); do \
	   echo -n "$$i: "; $(TIME) ./$$i.handtuned; \
         done

bench_nopeep:
	@for i in $(PROGS); do \
	   echo -n "$$i: "; $(TIME) ./$$i.compcert_nopeep; \
         done

bench_clang:
	@for i in $(PROGS); do \
	  echo -n "$$i: "; $(TIME) ./$$i.clang; \
	done

cminor_roundtrip:
	@for i in $(PROGS); do \
	   $(CCOMP) -dcminor -S $$i.c; \
	   cp $$i.cm $$i.1.cm; \
           $(CCOMP) -dcminor -S $$i.cm; \
           if cmp -s $$i.1.cm $$i.cm; \
           then echo "$$i: round trip passed"; rm -f $$i.1.cm $$i.cm; \
           else echo "$$i: round trip FAILED"; diff -u $$i.1.cm $$i.cm; \
           fi; \
         done

clean:
	rm -f *.compcert *.gcc *.gcc_nopeep *.compcert_nopeep *.clang *.handtuned
	rm -f *.compcert.c *.light.c *.parsed.c *.o *.sdump *~ 
