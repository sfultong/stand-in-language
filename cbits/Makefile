.PHONY: clean
all: libjumper.so
#jumper.o: jumper.c
#	gcc -fPIC -c -o $@ $^
#jumper.so: jumper.o
#	gcc -shared -o $@ $^
libjumper.so: jumper.c
	gcc -fPIC -shared -o $@ $^
clean:
	rm -f *.so *.o
install:
	mkdir -p $(out)/lib
	cp libjumper.so $(out)/lib
