

# "make" and "make test" are the same thing: build the bigint library
#        and the regression test program

# "make clean" cleans up

# "make realclean" cleans even better

# "make depend" Creates the dependencies to help make know what needs
#       to be rebuilt. You only need to run this once after unpacking.

# "make tarfile" Does a "make realclean" then creates a compressed tar file.

# CHANGE THE FOLLOWING TWO LINES TO YOUR FIRST AND LAST NAME.

FIRST_NAME=patrick
LAST_NAME=mcbride

# You can add more assembly files as you go.  Just edit the C code and
# put #ifdef around the function you want to change to assembly (look
# at bigint_adc() for an example), then create the new assembly (.S)
# file and add it to the ASMOBJS list.  Use .o instead of .S in the
# ASMOBJS list (see commented example below), and make will find the
# .S file. Do "make clean" to force a complete rebuild.

MAINOBJ = regression.o
COBJS = bigint.o

#ASMOBJS =
#DEFINES = -DSIXTYFOUR_BIT

ASMOBJS = bigint_negate.o bigint_cmp.o bigint_adc.o bigint_add.o bigint_zero.o
DEFINES = -DUSE_ASM -DSIXTYFOUR_BIT

#ASMOBJS = bigint_negate.o bigint_add.o
#DEFINES = -DUSE_ASM -DSIXTYFOUR_BIT

CC = gcc
DEPENDFLAGS = -M 
INCLUDES = -I.
LIBDIRS = -L.
LIBS = -lbigint

# Use the following flags for profiling
# CFLAGS = -pg -Wall -O2
# LFLAGS = -pg -O2

# Use the following flags for debugging
#CFLAGS = -g -Wall
#LFLAGS = -g

# Use the following flags for SPEED TESTS!
CFLAGS = -Wall -O2
LFLAGS = -O2

FIRST_NAMEL=$(shell echo $(FIRST_NAME) | tr '[:upper:]' '[:lower:]')
LAST_NAMEL=$(shell echo $(LAST_NAME) | tr '[:upper:]' '[:lower:]')

regression: libbigint.a $(MAINOBJ)
	$(CC) $(LFLAGS) -o $@ $(COBJS) $(ASMOBJS) $(MAINOBJ) $(LIBDIRS) $(LIBS) -lm

libbigint.a: $(COBJS) $(ASMOBJS)
	ar crs libbigint.a $(COBJS) $(ASMOBJS)

.c.o:
	$(CC) -c $(DEFINES) $(CFLAGS) $(INCLUDES) $<

.s.o:
	$(CC) -c $(DEFINES) $(CFLAGS) $(INCLUDES) $<

.S.o:
	$(CC) -c $(DEFINES) $(CFLAGS) $(INCLUDES) $<

tarfile: realclean report.pdf
	rm -f $(LAST_NAMEL)_$(FIRST_NAMEL).tgz
	cp -rp . /tmp/$(LAST_NAMEL)_$(FIRST_NAMEL)
	rm /tmp/$(LAST_NAMEL)_$(FIRST_NAMEL)/regression_tests.dat
	cd /tmp; tar cfz $(LAST_NAMEL)_$(FIRST_NAMEL).tgz $(LAST_NAMEL)_$(FIRST_NAMEL)
	mv /tmp/$(LAST_NAMEL)_$(FIRST_NAMEL).tgz .
	rm -rf /tmp/$(LAST_NAMEL)_$(FIRST_NAMEL)
	make depend

report.pdf:
	$(error report.pdf not found. Aborting.)

clean:
	rm -f *.o regression core.* libbigint.a $(LAST_NAMEL)_$(FIRST_NAMEL).tgz testdata/*.o testdata/gentestdata testdata/*~ testdata/core.*

realclean: clean
	rm -f *~ .depend 

# make depend will *create a file ".depend" with all the C dependencies
depend:
	rm -f .depend
	$(CC) $(DEFINES) $(INCLUDES) $(DEPENDFLAGS) $(COBJS:.o=.c) $(MAINOBJ:.o=.c) $(ASMOBJS:.o=.S) -lm > .depend

# if we have a .depend file, include it
ifeq (.depend,$(wildcard .depend))
include .depend
endif
