module Assign4 where

import Control.Monad.State
import Data.List
import Data.Maybe

type LInt = Int
type TInt = Int
type Subst = (TInt, Type)
--newtype State (Context,Int) (Context, Int, [TEqn])

--1. Vars on left of TEQN
--2. Vars on right
--3. bound vars
--4. Lis of substitutions

--type Package (([TInt]1,[TInt]2),([TInt]3,[Subst]4))
type Package = (([TInt], [TInt]), ([TInt], [Subst]))

data Lam = LAbst LInt Lam
    | LApp Lam Lam
    | LVar LInt
    | LPair Lam Lam
    | LPCase LInt LInt Lam Lam
    | LPUnit
    | LUCase Lam Lam  
    | LZero
    | LSucc
    | LNCase LInt Lam Lam Lam
    | LLNil
    | LLCons
    | LLCase LInt Lam Lam LInt
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

--functions    
typeInfer:: Lam -> Type
typeInfer lam = retType where
    eqns = genTypeEqns lam
    retType = unify eqns

showType:: Type -> String
showType typ = show typ

addToContext:: LInt -> Context -> TInt -> Context
addToContext l (Context c) t = ctex where
     ctex = Context ((l,t+1):c)   
      
addAbst:: State (Context,TInt) TEqn 
--addAbst st =  state (\(l,n) -> (Exists[n+1,n+2], Simp(TVar n, TFun (n+1,n+2), (_,n+2)))) st
addAbst = state (\(c,n) -> ((Exists ([n+1,n+2],[Simp(TVar n, TFun (TVar (n+1),TVar (n+2)))])), (c,n+2)))

--addVar:: State(Context,TInt) TEqn
--addVar lint = state (\(c,n) ->  case ((varHelper lint c n)) of
--    Nothing -> (Simp (TVar (-1), TVar (n+1)), (c,n+1))
--    Just num -> (Simp (TVar num, TVar (n+1)), (c,n+1)))

addVar:: LInt -> State(Context, TInt) TEqn
addVar num = state(\(c,n) -> ((Simp (TVar num, TVar (n))), (c,n+1)))

addApp:: State (Context, TInt) TEqn
addApp = state (\(c,n) -> ((Exists ([n+2,n+1],[Simp(TVar (n+1), TFun (TVar (n+2),TVar (n)))])), (c,n+1)))

addFix:: State (Context, TInt) TEqn
addFix = state (\(c,n) -> ((Exists ([n+1], [Simp(TVar (n+1), TFun (TVar n, TVar n))])), (c, n+1)))

addPair:: State (Context, TInt) TEqn
addPair  = state (\(c,n) -> ((Exists ([n+1,n+2],[Simp(TVar n, TProd (TVar (n+1),TVar (n+2)))])), (c,n+1)))
--addUVar:: State(Context, TInt) TEqn
--addUVar = state(\(c,n) -> (Simp (TVar (-1), TVar (n)), (c,n+1)))




varHelper:: LInt -> Context -> Maybe Int
varHelper l (Context c) = lint where
    lint = case (l `elem` firstsOfContext) of 
        True -> Just (li)
        False -> Nothing 
    firstsOfContext = (map fst c)
    secondsOfContext = (map snd c)
    indexOfL = (getIndex l firstsOfContext)
    li = secondsOfContext !! indexOfL

getIndex::(Eq a) => a -> [a] -> Int
getIndex a la = fromJust (elemIndex a la)

genTypeEqns:: Lam -> [TEqn]
genTypeEqns l = fst (runState (genTypeEqnsHelper l) (Context [],1))


--To Generate type equations, Cole suggests to have a helper function

                                 ---a -> a xb
                                 --a   b               
genTypeEqnsHelper:: Lam -> State (Context, TInt) [TEqn]
--genTypeEqnsHelper lam = state (_,_) ([])
genTypeEqnsHelper lam = case lam of
    
    LAbst lint lam1 -> do
        (ctex,tint) <- get
        let c = addToContext lint ctex tint       
        put(c,tint)
        eqs <- addAbst
        eqs1 <- genTypeEqnsHelper lam1
        return (eqs:eqs1)
        
    LApp lam1 lam2 -> do
        eq <- addApp
        eqs1 <- genTypeEqnsHelper lam1
        eqs2 <- genTypeEqnsHelper lam2
        return (eq:(eqs1 ++ eqs2))
        
    LVar lint -> do
        (ctex,tint) <- get
        let compVal = varHelper lint ctex       
        case compVal of 
            Just val -> do
                aVar <- addVar val
                return [aVar]
            Nothing -> do
                --aUVar <- addUVar
                return []  
    LFix lam1 -> do
        eq <- addFix
        eqs <- genTypeEqnsHelper lam1
        return (eq:eqs)
    
    LPair lam1 lam2 -> do
        eq <- addPair
        eqs1 <- genTypeEqnsHelper lam1
        eqs2 <- genTypeEqnsHelper lam2
        return (eq:(eqs1 ++ eqs2))
        
    _ -> error("error")
    --LPair lam1 lam2 ->
    --LPCase lint1 lint2 lam1 lam2 -> 
    --LPUnit -> 
    --LUCase lam1 lam2 ->  
    --LZero ->
    --LSucc ->
    --LNCase lint1 lam1 lam2 lam3 ->
    --LLNil ->
    --LLCons ->
    --LLCase lint1 lam1 lam2 lint2
    --LFix lam1 -> 



unify::[TEqn] -> Type
unify list = TNat

--1. Generate type equations
--    -build up the tree
--    -Generate equations
--    -solve all equations -- easier to do these all in one step when programming, easier to do all steps when doing by hand.
--
--2. Unify Type equations

--Tutorial Nov 27 - Cole

--Solving Type Equations



--therexists 1,2.1 = 2 x 3 => ([1],[2,3],[1,2]...)

--foldType:: (TInt -> a ) -> (((a,a) -> a) . _ ._) -> Type -> a

--foldTEqn::(Type,Type) -> a -> ([TInt] -> a[] -> a)) -> TEqn -> a

--solveTEqns:: [TEqn] -> Package
--use (foldTEqn) to solve things here

--infer:: Lam -> Type
--infer2 = rename(fix(TVar 0))
--    where
--        fix ty = case ty == (substituteAll ty subs) of
--            True -> 
--            False -> fix (substituteAll, ty subs)
--        (_,_, subs) = solve TEqns (genEqns2)
        
        
substituteAll:: Type -> [Subst] -> Type
substituteAll  = foldr substitute


substitute:: Subst -> Type -> Type
substitute subts typ = typ

--combinePackage:: [Package] -> Package
--in this function you will have to call the linearize
-- each time you combine the package, you are doing the unifcation, i.e. this is the unification step

linearize::[Subst] -> [Subst]
linearize [] = []
linearize (sub:subs) = sub:linearize(coalesce sub subs)

coalesce:: Subst -> [Subst] -> [Subst]
coalesce _ [] = []
colaesce (t,ty) ((t',ty'):subs) = union subs' subs''
    where
        subs' = coalesce (t,ty) subs
        subs'' = case (t==t') of
            True ->  match (ty,ty')
            False -> [occursCheck(t',(substitute(t,ty) ty'))]

occursCheck:: Subst -> Subst
occursCheck subst = subst
--1 = 1 x 2 would be a fail

match:: (Type, Type) -> [(TInt, Type)]
match (typ1,typ2) = []
--use a zip, recursion
-- f(x,y) = f(z * y, w)
--  x = z * y 
-- y = w
-- we have 3 functions
-- 1. (_ -> _)
-- 2. (_ * _)
-- 3. [_]
--
--cole example
--[0 = 1x2, 1=3, 3=2 -> 4, 3 = 4 -> 2]subst
--[0 = 1 x 2, 1 = 2 -> 4, 1 = 4 -> 2] match
--[0 = 1 x 2, 1 = 2 -> 4, 2=4, 4=2]subst
--[0 = 1 x 2, 1 = 2 -> 2]
--[0 = (2 -> 2) x 2]
-- [0 = (1 -> 1) x 1]

term = LAbst 1 (LVar 1)

term2 = LAbst 1 (LAbst 2 (LAbst 3 (LVar 2)))

term3 = LApp ( LAbst 1 (LApp (LVar 1) (LAbst 2 (LVar 2)))) (LVar 3)

term4 = LApp ( LAbst 1 (LApp (LVar 1) (LAbst 2 (LVar 2)))) (LVar 2)

term5 = LAbst 1 (LApp (LVar 1) (LVar 2))

term6 = LAbst 1 ( LAbst 2 (LApp (LVar 1) (LVar 2)))

term7 = LFix term

term8 = LPair (LVar 1) (LVar 2)


