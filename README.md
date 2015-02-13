
## COMPILATION

This Coq theory compiles under Coq 8.3pl5, available from https://coq.inria.fr/distrib/V8.3pl5/files/ .
Earlier patch levels should also work; I have tested with 8.3pl2.

Create a Makefile by calling
```bash    
$ coq_makefile -f Make > Makefile
```  
and compile by calling
```bash    
$ make
```

WARNING : The compilation of some of the files consumes up to 2GB of memory. Make sure you dispose of sufficient reserves of ram before compiling the code.


## WORK WITH THE CODE

Call coqide as follows from the root of the library:
```bash
$ coqide -R . CatSem
```

## CONTENT

Read the file "./DESCRIPTION" for a description of the content of each file.


