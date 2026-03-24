CFLAGS=-std=c99 -Wall -Wextra -pedantic -O2 -g
DEBUG=valgrind
TARGET=prolog

.PHONY: all default test run debug clean

all default: ${TARGET}

run: ${TARGET}
	./${TARGET}

test: ${TARGET}
	./${TARGET} -t

debug:
	${DEBUG} ./${TARGET} -t

${TARGET}: ${TARGET}.c makefile
	${CC} ${CFLAGS} ${TARGET}.c -o $@

clean:
	git clean -dffx
