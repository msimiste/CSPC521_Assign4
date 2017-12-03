module Assign4 where

import Control.Monad.State

type LInt = Int

type TInt = Int

data Lam = LAbst LInt Lam
    | LVar LInt
    | LPair Lam Lam
    | LPCase LInt LInt Lam Lam
    | LPUnit
    | LUCase Lam Lam
    | LApp Lam Lam
    | LZero
    | LSucc
    | LNCase LInt Lam Lam Lam
    | LLNil
    | LLCons
    | LLCase LInt Lam Lam LInt
    | LFix Lam
    


data Type = TVar TInt  --We want to create a show func such as shoow:: TVar n -> "n", TFun (t,t') -> (|[t}|,|[t']|))
    | TFun (Type, Type)
    | TProd (Type, Type)
    | TList Type
    | TUnit
    | TNat

data TEqn = Simp (Type, Type) --"="
        | Exists ([TInt],[TEqn])
        
data Context = Context [(LInt, TInt)]

--functions    
typeInfer:: Lam -> Type
typeInfer lam = TNat

showType:: Type -> String
showType typ = ""


--addAbst:: State (Context,TInt) ()
--addAbst st =  state (\(l,n) -> (Exists[n+1,n+2], Simp(TVar n, TFun (n+1,n+2), (_,n+2))))st

--genTypeEqns:: Lam -> [TEqn]
--genTypeEqns l = fst (runState (genTypeEqnsHelper l) ([],0))


--To Generate type equations, Cole suggests to have a helper function

                                 ---a -> a xb
                                 --a   b               
--genTypeEqnsHelper:: Lam -> State (Context, TInt) ([TEqn])
--genTypeEqnsHelper lam = state (_,_) ([])

unify::[TEqn] -> Type
unify list = TNat

--1. Generate type equations
--    -build up the tree
--    -Generate equations
--    -solve all equations -- easier to do these all in one step when programming, easier to do all steps when doing by hand.
--
--2. Unify Type equations

