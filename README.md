
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

## BRANCHES

Each branch below, printed in **boldface**, corresponds to an article, printed in _italic_.

* [**JFR**](https://github.com/benediktahrens/monads/tree/JFR): [_Initial Semantics for higher-order typed syntax in Coq_](http://jfr.cib.unibo.it/article/view/2066)
* [**MSCS**](https://github.com/benediktahrens/monads/tree/MSCS): [_Modules over relative monads for syntax and semantics_](http://dx.doi.org/10.1017/S0960129514000103)
* [**REDUCTION_RULES**](https://github.com/benediktahrens/monads/tree/REDUCTION_RULES): [_Initial Semantics for Reduction Rules_](http://arxiv.org/abs/1212.5668)

All the articles are also available from my [webpage](http://benedikt-ahrens.de/publications).


