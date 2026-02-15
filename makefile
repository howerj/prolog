CFLAGS=-std=c99 -Wall -Wextra -pedantic -O2 -g
DEBUG=valgrind
TARGET=prolog

.PHONY: all default test run clean

all default: ${TARGET}

test run: ${TARGET}
	${DEBUG} ./${TARGET} -t

${TARGET}: ${TARGET}.c makefile
	${CC} ${CFLAGS} ${TARGET}.c -o $@

clean:
	rm -fv ${TARGET} *.exe
