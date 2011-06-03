
.PHONY: all clean

.SUFFIXES: .hs .hsc

EXE = ZooClient

ZK_INCLUDE = /usr/local/include/c-client-src
ZK_LIBS    = /usr/local/lib

LD_LIBRARY_PATH = $(ZK_LIBS)

GHC_OPTS = -O3 -optc-O3 -L$(ZK_LIBS) -lzookeeper_mt -threaded

CLIENT_SRC = Zookeeper.hs ZooClient.hs

.hsc.hs:
	hsc2hs -v -I$(ZK_INCLUDE) -L"-I$(ZK_INCLUDE)" -L"-L$(ZK_LIBS)" -L"-lzookeeper_mt" $<

all: $(EXE)

ZooClient: $(CLIENT_SRC)
	ghc $(GHC_OPTS) --make $@

interact: Zookeeper.o
	-ghci -L$(ZK_LIBS) -lzookeeper_mt Zookeeper.hs

clean:
	-rm *.hi *.o $(EXE) Zookeeper.hs Zookeeper_hsc_make* Zookeeper_stub.*

