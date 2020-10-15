######
#
# Note that
# certain installations require the following changes:
#
# atscc -> patscc
# atsopt -> patsopt
# ATSHOME -> PATSHOME
#
######
#
#
######
#
ATSHOME=$(shell dirname $(shell dirname $(shell readlink -f $(shell which patscc))))
ATSCC=patscc
ATSOPT=patsopt
#
ATSCCFLAGS=-O2 -DATS_MEMALLOC_LIBC -I"../libs/" -I"$(ATSHOME)/lib/ats2-postiats-0.3.13/contrib/atscntrb/"
ATSLIBS=-ljansson
# ATSCCFLAGS=-O2
#
# '-flto' enables link-time optimization such as inlining lib functions
#
# ATSCCFLAGS=-O2 -flto
#
#
ATS_DATS=\
	../libs/ats-bytestring/DATS/bytestring_flat.dats \
	../libs/ats-base64/DATS/ats-base64.dats \
	../libs/ats-vicpack/src/DATS/vicpack.dats \
	jansson.dats
ATS_SATS=\
	../libs/ats-bytestring/SATS/bytestring.sats \
	../libs/ats-base64/SATS/ats-base64.sats \
	../libs/ats-vicpack/src/SATS/vicpack.sats
######
#

ATS_OBJS= $(ATS_SATS:.sats=_sats.o) $(ATS_DATS:.dats=_dats.o)

.PHONY: all clean

all: mqtt2csv-vicpack-payload-decoder

cleanall::
#
######
#
# Please uncomment the following three lines and replace the name [foo]
# with the name of the file you want to compile
#

jansson_dats.o: $(ATSHOME)/lib/ats2-postiats-0.3.13/contrib/atscntrb/atscntrb-hx-libjansson/DATS/jansson.dats
		$(ATSCC) $(ATSCCFLAGS) -c -o $@ $<


mqtt2csv-vicpack-payload-decoder: $(ATS_OBJS)
	$(ATSCC) $(ATSCCFLAGS) -o $@ $(ATS_OBJS) --constraint-ignore DATS/main.dats $(ATSLIBS)

cleanall:: ; $(RMF) test*
#
######
#
# You may find these rules useful
#
%_sats.o: %.sats ; $(ATSCC) $(ATSCCFLAGS) -c -o $@ $<
%_dats.o: %.dats ; $(ATSCC) $(ATSCCFLAGS) -c -o $@ $<
#
######
#
RMF=rm -f
#
######
#
clean:: ; $(RMF) test*
clean:: ; $(RMF) mqtt2csv-vicpack-payload-decoder
clean:: ; $(RMF) *~
clean:: ; find -name '*_?ats.o' -exec $(RMF) {} \;
clean:: ; find -name '*_?ats.c' -exec $(RMF) {} \;
#
cleanall:: clean
#
###### end of [Makefile] ######

