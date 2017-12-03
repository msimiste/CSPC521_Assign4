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

--Tutorial Nov 27 - Cole

Solving Type Equations

type Subst = (Tint, Type)

--1. Vars on left of TEQN
--2. Vars on right
--3. boud vars
--4. Lis of substitutions

type Package (([TInt]1,[TInt]2),[TInt]3[Subst]4)

therexists 1,2.1 = 2 x 3 => ([1],[2,3],[1,2]...)

foldType:: (TInt -> a ) -> ((a,a) -> a) . _ ._ -> Type -> a

foldTEqn::((Type,TYpe) -> a -> ([TInt] -> [a[] -> a) -> TEqn -> a

solveTEqns:: [TEqn] -> Package
--use (foldTEqn) to solve things here

infer:: Lam -> Type
infer2 = rename(fix(TVar 0))
    where
        fix ty = case ty == (substituteAll ty subs) of
            True -> 
            False -> fix (substituteAll, ty subs)
        (_,_, subs) = solve TEqns (genEqns2)
        
        
substituteAll:: Type -> [Subst] -> Type
substituteAll  = foldr substitute

substitute:: Subst -> Type -> Type


combinePackage:: [Package] -> Package
--in this function you will have to call the linearize
-- each time you combine the package, you are doing the unifcation, i.e. this is the unification step

linearize::[Subst] -> [Subst]
linearize [] = []
linearize (sub:subs) = sub:linearize(coalesce sub subs)

coalesce:: Subst -> [Subst] -> [Subst]
coalesce _ [] = []
colaesce (t,ty) ((t',ty'):subs) = union subs' subs''
    where
        sbus' coalesce (t,ty) subs
        subs'' case (t==t') of
            True ->  match (ty,ty')
            False -> [occurseCheck(t',(substitute(t,ty) ty'))]

occursCheck:: Subst -> Subst
--1 = 1 x 2 would be a fail

match:: (Type, Type) -> [(TInt, Type)]
--use a zip, recursion
-- f(x,y) = f(z * y, w)
--  x = z * y 
-- y = w
-- we have 3 functions
-- 1. (_ -> _)
-- 2. (_ * _)
-- 3. [_]

--cole example
--[0 = 1x2, 1=3, 3=2 -> 4, 3 = 4 -> 2]subst
--[0 = 1 x 2, 1 = 2 -> 4, 1 = 4 -> 2] match
--[0 = 1 x 2, 1 = 2 -> 4, 2=4, 4=2]subst
--[0 = 1 x 2, 1 = 2 -> 2]
--[0 = (2 -> 2) x 2]
-- [0 = (1 -> 1) x 1]




