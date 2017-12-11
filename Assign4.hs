module Assign4 where

import Control.Monad.State
import Data.List
import Data.Maybe

type LInt = Int
type TInt = Int
type Subst = (TInt, Type)
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

--showType:: Type -> String
--showType typ = show typ

addToContext:: LInt -> Context -> TInt -> Context
addToContext l (Context c) t = ctex where
     ctex = Context ((l,t+1):c)   
      
addAbst:: State (Context,TInt) TEqn 
addAbst = state (\(c,n) -> ((Exists ([n+1,n+2],[Simp(TVar n, TFun (TVar (n+1),TVar (n+2)))])), (c,n+2)))

addVar:: LInt -> State(Context, TInt) TEqn
addVar num = state(\(c,n) -> ((Simp (TVar num, TVar (n))), (c,n+1)))

addApp:: State (Context, TInt) TEqn
addApp = state (\(c,n) -> ((Exists ([n+2,n+1],[Simp(TVar (n+1), TFun (TVar (n+2),TVar (n)))])), (c,n+1)))

addFix:: State (Context, TInt) TEqn
addFix = state (\(c,n) -> ((Exists ([n+1], [Simp(TVar (n+1), TFun (TVar n, TVar n))])), (c, n+1)))

addPair:: State (Context, TInt) TEqn
addPair  = state (\(c,n) -> ((Exists ([n+1,n+2],[Simp(TVar n, TProd (TVar (n+1),TVar (n+2)))])), (c,n+1)))

addPCase:: TInt -> State (Context, TInt) TEqn
addPCase tint = state (\(c,n) -> ((Exists ([tint+1,tint+2,n],[Simp(TVar (n), TProd (TVar (tint+1),TVar (tint+2)))])), (c,n)))


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
             
genTypeEqnsHelper:: Lam -> State (Context, TInt) [TEqn]
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
        eqs2 <- genTypeEqnsHelper lam2
        eqs1 <- genTypeEqnsHelper lam1
        return (eq:(eqs1 ++ eqs2))
        
    LVar lint -> do
        (ctex,tint) <- get
        let compVal = varHelper lint ctex       
        case compVal of 
            Just val -> do
                aVar <- addVar val
                return [aVar]
            Nothing -> do                
                return []  
    LFix lam1 -> do
        eq <- addFix
        eqs <- genTypeEqnsHelper lam1
        return (eq:eqs)
    
    LPair lam1 lam2 -> do
        eq <- addPair
        eqs2 <- genTypeEqnsHelper lam2
        eqs1 <- genTypeEqnsHelper lam1
        return (eq:(eqs1 ++ eqs2))
        
    LPCase lint1 lint2 lam1 lam2 -> do
        (c1,firstN) <- get
        let newC = addToContext lint1 c1 (firstN)       
        let newc2 = addToContext lint2 newC (firstN+1)
        put(newc2,firstN+2)
        
        eqs1 <- genTypeEqnsHelper lam2
        (c3,thirdN) <- get
        put(c1,thirdN)
        
        eq <- addPCase firstN
        --put(c1,thirdN)
        
        eqs2 <- genTypeEqnsHelper lam1                 
       
        return (eq:(eqs2 ++ eqs1))               
        
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


term = LAbst 1 (LVar 1)

term1 = LAbst 1 (LApp (LVar 1)(LVar 1))

term2 = LAbst 1 (LAbst 2 (LAbst 3 (LVar 2)))

term3 = LApp ( LAbst 1 (LApp (LVar 1) (LAbst 2 (LVar 2)))) (LVar 3)

term4 = LApp ( LAbst 1 (LApp (LVar 1) (LAbst 2 (LVar 2)))) (LVar 2)

term5 = LAbst 1 (LApp (LVar 1) (LVar 2))

term6 = LAbst 1 ( LAbst 2 (LApp (LVar 1) (LVar 2)))

term7 = LFix term

term8 = LPair (LVar 1) (LVar 2)

term9 = LAbst 1 (LPCase 2 3 (LVar 1) (LPair (LVar 2)(LVar 3)))

term10 = LApp (term3) (LPCase 1 4 (LVar 3) (LPair (LVar 2)(LVar 1)))

foldTeqn:: ((Type,Type)-> a) -> (([TInt], [a])->a) -> TEqn -> a
foldTeqn f1 f2  (Simp (t1, t2)) = f1 (t1,t2)
foldTeqn f1 f2 (Exists (list1, list2))  = f2 (list1, map (foldTeqn f1 f2) list2 )   

prettyP:: [TEqn] -> String
prettyP eqns = foldr (++) "" (map pretty1 eqns)

pretty1:: TEqn -> String
pretty1 = foldTeqn (\(a,b) -> (showType a) ++ "=" ++ (showType b)++", ")
                   (\(a,b) -> "Exists" ++ (show a) ++ ":" ++ (show b))

showType:: Type -> String
showType (TVar n) = show n
showType (TFun (t1,t2)) = "(" ++ (showType t1) ++ "->" ++ (showType t2) ++ ")"
showType (TProd (t1,t2)) = "(" ++ (showType t1) ++ "x" ++ (showType t2) ++ ")"
showType (TList t1) = "[" ++ (showType t1) ++ "] "
showType (TUnit) = "()"
showType (TNat) = "N"

--Notes from tutorial

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

