# Oat v.1 Compiler #
This was the fourth project for my compilers class. I worked with a partner on a compiler that compiles Oat, a C like language, to LLVM. Oat supports `boolean`, `int`, and `string` types as well as arrays of such types. It also supports top-level mutually recursive functions and global variables. The formal specification for the language is available [here](http://www.cis.upenn.edu/~cis341/15sp/hw/hw4/oat.pdf).

Ocamllex was used to generate the lexer as defined by `lexer.mll`. Menhir was the parser generator we used, and `parser.mly` defines how that happens. It's a pretty straightforward encoding of the context-free grammar in the language specification.

## Setup ##

Setup instructions for a relatively recent version of Ubuntu (>= 14.04):

### GCC ###

    sudo apt-get install gcc

### Clang <= 3.6 ###

Note that LLVM version 3.7 changes the syntax of the load instruction. Thus, only version 3.6 and earlier is supported.

    sudo apt-get install clang-3.6
    sudo update-alternatives --install /usr/bin/clang clang /usr/bin/clang-3.6 100

### OCaml >= 4.01.0 ###

    sudo apt-get install m4 ocaml-native-compilers camlp4-extra opam

### Menhir ###

    opam install menhir

## Build ##

To build:
    
    make

To build and run the test harness:

    make install

## Testing ##

`main.native` is the executable that is built. It is setup to run the test harness for the compiler, which are defined by the `gradedtests.mll` and `providedtests.ml` files.

On Linux, run:

    main.native -linux --test

On OSX, run:
    
    main.native --test

More details about how to use `main.native` for testing can be found in `README_TESTING`.

## Use ##

To use the compiler, import the following:

    open Driver

Setup the output path and file names:

    let output_path = !Platform.output_path in
    let dot_ll_file = Platform.gen_name output_path "test" ".ll" in
    let exec_file = Platform.gen_name output_path "exec" "" in
    let tmp_file = Platform.gen_name output_path "tmp" ".txt" in  

Parse the oat file at path:

    let oat_ast = parse_oat_file path in
  
Compile the ast:
  
    let ll_ast = Frontend.cmp_prog oat_ast in
    let ll_str = Driver.string_of_ll_ast path ll_ast in
  
Write the compiled program to disk and link any C files that you call:
  
    let _ = write_file dot_ll_file ll_str in
    let _ = Platform.link (dot_ll_file::["runtime.c"]) exec_file in

As an example of an oat program, here's a function that computes the maximum monotonically increasing subsequence in an array:

    int maxsum(int[] arr, int size) {
        int[] maxarr = new int[size]{i => 0};
        int maxs = 0;
        maxarr[0] = arr[0];
        for(int i = 0; i < size; i = i+1;){
            for(int j = 0; j < i; j=j+1;){
                if(arr[i] > arr[j] & maxarr[i] < maxarr[j] + arr[i]){
                    maxarr[i] = maxarr[j] + arr[i];
                }
            }
            if(maxs < maxarr[i]){
                maxs = maxarr[i];
            }
        } 
        return maxs;
    }
    
    int program (int argc, string[] argv) {
        int[] array = {1,101,2,3,101,4,5};
        int max_ans = maxsum(array, 7);
        return max_ans;
    }
