The following is a nanopass compiler for a subset of typed Racket. The compiler handles booleans and logical operators, loops, conditionals and functions.

Tests can be defined in a directory `./tests`. Tests are run with the
`run-tests.rkt` module. You can run these tests either from the command
line with:

```
   racket run-tests.rkt
```

Or by opening and running `run-tests.rkt` in DrRacket.

Before running the compiler tests, you need to compile
`runtime.c` (see below).

## Public student code

Utility code, test suites, etc. for the compiler course.

This code will be described in the Appendix of the book.

The `runtime.c` file needs to be compiled and linked with the assembly
code that your compiler produces. To compile `runtime.c`, do the
following
```
   gcc -c -g -std=c99 runtime.c
```
This will produce a file named `runtime.o`. The -g flag is to tell the
compiler to produce debug information that you may need to use
the gdb (or lldb) debugger.

On a Mac with an M1 (ARM) processor, use the `-arch x86_64` flag to
compile the runtime:
```
   gcc -c -g -std=c99 -arch x86_64 runtime.c
```

Next, suppose your compiler has translated the Racket program in file
`foo.rkt` into the x86 assembly program in file `foo.s` (The .s filename
extension is the standard one for assembly programs.) To produce
an executable program, you can then do
```
  gcc -g runtime.o foo.s
```
which will produce the executable program named a.out.

The compiler passes are defined in `compiler.rkt`
and are tested using the `interp-tests` function from `utilities.rkt`. It
tests the passes on the programs in the tests
subdirectory. Note that `interp-tests` does not
test the final output assembly code; you need to use `compiler-tests`
for that purpose. The usage of `compiler-tests` is quite similar to
`interp-tests`. Example uses of these testing procedures appear in
`run-tests.rkt`.
