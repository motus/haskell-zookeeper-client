
.PHONY: all clean

.SUFFIXES: .hs .hsc

EXE = ZooClient

ZK_INCLUDE = -I/usr/local/include
ZK_LIBS    = -L/usr/local/libs

GHC_OPTS = -O3 -optc-O3 $(ZK_LIBS) -lzookeeper_mt -threaded

CLIENT_SRC = Zookeeper.hs ZooClient.hs

.hsc.hs:
	hsc2hs $(ZK_INCLUDE) $<

all: $(EXE)

ZooClient: $(CLIENT_SRC)
	ghc $(GHC_OPTS) --make $@

interact: Zookeeper.o
	-ghci $(ZK_LIBS) -lzookeeper_mt Zookeeper.hs

clean:
	-rm *.hi *.o $(EXE) Zookeeper.hs

