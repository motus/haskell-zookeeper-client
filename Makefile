
.PHONY: all clean

.SUFFIXES: .hs .hsc

EXE = ZooClient

ZK_INCLUDE = c/include
ZK_LIBS    = c/.libs

GHC_OPTS = -O3 -optc-O3 -L$(ZK_LIBS) -lzookeeper_mt -threaded

CLIENT_SRC = Zookeeper.hs ZooClient.hs

.hsc.hs:
	hsc2hs -I$(ZK_INCLUDE) $<

all: $(EXE)

ZooClient: $(CLIENT_SRC)
	ghc $(GHC_OPTS) --make $@

interact: Zookeeper.o
	-ghci -L$(ZK_LIBS) -lzookeeper_mt Zookeeper.hs

clean:
	-rm *.hi *.o $(EXE) Zookeeper.hs

