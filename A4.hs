module A4 where

import Control.Monad.State
import Data.List
import Data.Maybe

type LInt = Int
type TInt = Int
type Subst = (TInt, Type)

data Lam = LAbst LInt Lam
    | LApp Lam Lam
    | LVar LInt
    | LPair Lam Lam
    | LPCase LInt LInt Lam Lam
    | LUnit
    | LUCase Lam Lam  
    | LZero
    | LSucc
    | LNCase LInt Lam Lam Lam
    | LLNil
    | LLCons
    | LLCase LInt Lam Lam Lam
    | LFix Lam deriving (Eq, Show, Read) 


data Type = TVar TInt  --We want to create a show func such as show:: TVar n -> "n", TFun (t,t') -> (|[t}|,|[t']|))
    | TFun (Type, Type) -- Arrow
    | TProd (Type, Type) -- Pair
    | TList Type -- List
    | TUnit -- 
    | TNat deriving (Eq, Show, Read)

data TEqn = Simp (Type, Type) --"="
        | Exists ([TInt],[TEqn]) deriving (Eq, Show, Read)
        
data Context = Context [(LInt, TInt)]

showType:: Type -> String
showType (TVar n) = show n
showType (TFun (t1,t2)) = "(" ++ (showType t1) ++ "->" ++ (showType t2) ++ ")"
showType (TProd (t1,t2)) = "(" ++ (showType t1) ++ "x" ++ (showType t2) ++ ")"
showType (TList t1) = "[" ++ (showType t1) ++ "] "
showType (TUnit) = "()"
showType (TNat) = "N"


--test terms
term = (LApp (LVar 1) (LVar 1))

term1 = (LAbst 1 (LApp (LVar 1)(LVar 2)))

term2 = (LAbst 1 (LAbst 1 (LAbst 3 (LVar 2))))

term3 = (LApp ( LAbst 1 (LApp (LVar 1) (LAbst 2 (LVar 2)))) (LVar 3))

term4 = (LApp ( LAbst 1 (LApp (LVar 1) (LAbst 2 (LVar 2)))) (LVar 2))

term5 = (LAbst 1 (LApp (LVar 1) (LVar 2)))

term6 = (LAbst 1 (LAbst 2 (LApp (LVar 1) (LVar 2))))

term7 = (LFix term)

term8 = (LPair (LVar 1) (LVar 2))

term9 = (LAbst 1 (LPCase 2 3 (LVar 1) (LPair (LVar 3)(LVar 2))))

term10 = (LApp (term3) (LPCase 1 4 (LVar 3) (LPair (LVar 2)(LVar 1))))

term11 = (LAbst 1 (LUCase (LVar 1) (LPair (LVar 2)(LVar 3))))

term12 = (LAbst 1 (LUCase (LVar 1) (LAbst 2 (LApp (LVar 2) (LVar 3)))))

term13 = (LApp (LSucc) (LZero))

term14 = (LApp (LAbst 1 (LApp (LVar 1)(LVar 1))) (LAbst 2 (LApp(LVar 1)(LVar 2))))

term15 = (LApp (LAbst 1 (LApp(LVar 1)(LVar 1))) (LAbst 2(LApp (LVar 1)(LVar 2))))

term16 = (LApp (LPair(LVar 1)(LVar 2))(LPair(LVar 2)(LVar 3)))

term17 = (LApp (LPair(LPair(LVar 1)(LVar 2))(LPair(LVar 3)(LVar 1))) (LAbst 1 (LApp (LVar 1)(LVar 1))))

term18 = (LApp(LApp (LVar 1)(LVar 1))(LApp(LVar 1)(LVar 1)))

term19 = (LApp(LApp(LApp(LVar 1)(LVar 1))(LVar 1))(LVar 1))

term20 = (LAbst 4 (LLCons))

term21 = (LAbst 1 (LLNil))

term22 = (LAbst 1 (LApp (LVar 1)(LVar 1)))

subs = [(5,TFun ((TVar 4),(TVar 3))),(6,TVar 2), (5,TFun ((TVar 4),(TVar 3))),(6,TVar 2)]::[Subst]

term23 = (LLCase 88 (LVar 1)(LVar 2)(LVar 3))

test = (((TFun ((TVar 6),(TVar 5))),(TProd((TFun((TVar 4),(TVar 3))),(TFun((TVar 2),(TVar 1)))))))

term24 = (LAbst 1 (LApp (LSucc)(LZero)))
