CPSC521 Assignment 4 - Mike Simister
Acknowledgments to Edward Rochester and Clayto Vis, this submisson is the result of many discussions amongst the 3 of us

*****To compile and create test files*****

./setup from cmd line  ***./setup will create 26 test files in the directory where it is run from***

To run a test file:

./main <testfile>

Example:

> ./setup

[1 of 4] Compiling A4               ( A4.hs, A4.o )
[2 of 4] Compiling GenEquations     ( GenEquations.hs, GenEquations.o )
[3 of 4] Compiling SolveEquations   ( SolveEquations.hs, SolveEquations.o )
[4 of 4] Compiling Main             ( main.hs, main.o )
Linking main ...

> ./main test2
> ((4->3)->3)

*****To run from prelude*****

>l: SolveEquations.hs

SolveEquations> showType $ infer <term>

**note**
** <term> can be found at bottom of A4.hs 
** there is a <testfile> matching each term i.e. test1 = term1
** however terms are useful for testing individual components of the program.


**Names and Contents of Test files**

*filename*     *file contents*

test1       |    (LApp (LVar 1) (LVar 1))
test2       |    (LAbst 1 (LApp (LVar 1)(LVar 2)))
test3       |    (LAbst 1 (LAbst 1 (LAbst 3 (LVar 2))))
test4       |    (LApp ( LAbst 1 (LApp (LVar 1) (LAbst 2 (LVar 2)))) (LVar 3))
test5       |    (LApp ( LAbst 1 (LApp (LVar 1) (LAbst 2 (LVar 2)))) (LVar 2))
test6       |    (LAbst 1 (LApp (LVar 1) (LVar 2)))
test7       |    (LAbst 1 (LAbst 2 (LApp (LVar 1) (LVar 2))))
test8       |    (LFix (LApp (LVar 1) (LVar 1)))
test9       |    (LPair (LVar 1) (LVar 2))
test10      |    (LAbst 1 (LPCase 2 3 (LVar 1) (LPair (LVar 3)(LVar 2))))
test11      |    (LApp (LAbst 1 (LAbst 1 (LAbst 3 (LVar 2)))) (LPCase 1 4 (LVar 3) (LPair (LVar 2)(LVar 1))))
test12      |    (LAbst 1 (LUCase (LVar 1) (LPair (LVar 2)(LVar 3))))
test13      |    (LAbst 1 (LUCase (LVar 1) (LAbst 2 (LApp (LVar 2) (LVar 3)))))
test14      |    (LApp (LSucc) (LZero))
test15      |    (LApp (LAbst 1 (LApp (LVar 1)(LVar 1))) (LAbst 2 (LApp(LVar 1)(LVar 2))))
test16      |    (LApp (LAbst 1 (LApp(LVar 1)(LVar 1))) (LAbst 2(LApp (LVar 1)(LVar 2))))
test17      |    (LApp (LPair(LVar 1)(LVar 2))(LPair(LVar 2)(LVar 3)))
test18      |    (LApp (LPair(LPair(LVar 1)(LVar 2))(LPair(LVar 3)(LVar 1))) (LAbst 1 (LApp (LVar 1)(LVar 1))))
test19      |    (LApp(LApp (LVar 1)(LVar 1))(LApp(LVar 1)(LVar 1)))
test21      |    (LApp(LApp(LApp(LVar 1)(LVar 1))(LVar 1))(LVar 1))
test22      |    (LAbst 4 (LLCons))
test23      |    (LAbst 1 (LLNil))
test24      |    (LAbst 1 (LApp (LVar 1)(LVar 1)))
test25      |    (LLCase 88 (LVar 1)(LVar 2)(LVar 3))
test26      |    (LAbst 1 (LApp (LSucc)(LZero)))


--test terms
term1  = (LApp (LVar 1) (LVar 1))
term2 = (LAbst 1 (LApp (LVar 1)(LVar 2)))
term3 = (LAbst 1 (LAbst 1 (LAbst 3 (LVar 2))))
term4 = (LApp ( LAbst 1 (LApp (LVar 1) (LAbst 2 (LVar 2)))) (LVar 3))
term5 = (LApp ( LAbst 1 (LApp (LVar 1) (LAbst 2 (LVar 2)))) (LVar 2))
term6 = (LAbst 1 (LApp (LVar 1) (LVar 2)))
term7 = (LAbst 1 (LAbst 2 (LApp (LVar 1) (LVar 2))))
term8 = (LFix term)
term9 = (LPair (LVar 1) (LVar 2))
term10 = (LAbst 1 (LPCase 2 3 (LVar 1) (LPair (LVar 3)(LVar 2))))
term11 = (LApp (term3) (LPCase 1 4 (LVar 3) (LPair (LVar 2)(LVar 1))))
term12 = (LAbst 1 (LUCase (LVar 1) (LPair (LVar 2)(LVar 3))))
term13 = (LAbst 1 (LUCase (LVar 1) (LAbst 2 (LApp (LVar 2) (LVar 3)))))
term14 = (LApp (LSucc) (LZero))
term15 = (LApp (LAbst 1 (LApp (LVar 1)(LVar 1))) (LAbst 2 (LApp(LVar 1)(LVar 2))))
term16 = (LApp (LAbst 1 (LApp(LVar 1)(LVar 1))) (LAbst 2(LApp (LVar 1)(LVar 2))))
term17 = (LApp (LPair(LVar 1)(LVar 2))(LPair(LVar 2)(LVar 3)))
term18 = (LApp (LPair(LPair(LVar 1)(LVar 2))(LPair(LVar 3)(LVar 1))) (LAbst 1 (LApp (LVar 1)(LVar 1))))
term19 = (LApp(LApp (LVar 1)(LVar 1))(LApp(LVar 1)(LVar 1)))
term20 = (LApp(LApp(LApp(LVar 1)(LVar 1))(LVar 1))(LVar 1))
term21 = (LAbst 4 (LLCons))
term22 = (LAbst 1 (LLNil))
term23 = (LAbst 1 (LApp (LVar 1)(LVar 1)))
term24 = (LLCase 88 (LVar 1)(LVar 2)(LVar 3))
term25 = (LAbst 1 (LApp (LSucc)(LZero)))

subs = [(5,TFun ((TVar 4),(TVar 3))),(6,TVar 2), (5,TFun ((TVar 4),(TVar 3))),(6,TVar 2)]::[Subst]
test = (((TFun ((TVar 6),(TVar 5))),(TProd((TFun((TVar 4),(TVar 3))),(TFun((TVar 2),(TVar 1)))))))
