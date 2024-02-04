#！/bin/bash                                                                    

clang -S -O0 -emit-llvm test.c -o test.ll
opt -load ../CFGPass/build/llvm_CFGPass/libLLVMCFG.so  -CFGPass <test.ll> /dev/null  -enable-new-pm=0
dot -Tpng main.dot -o main.png
eog main.png


