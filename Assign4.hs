module Assign4 where

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


addToContext:: LInt -> Context -> TInt -> Context
addToContext l (Context c) t = ctex where
     ctex = Context ((l,t+1):c)   
      
addAbst:: State (Context,TInt) TEqn 
addAbst = state (\(c,n) -> ((Exists ([n+1,n+2],[Simp(TVar n, TFun (TVar (n+1),TVar (n+2)))])), (c,n+2)))

addVar:: LInt -> State(Context, TInt) TEqn
addVar num = state(\(c,n) -> ((Simp (TVar num, TVar (n))), (c,n+1)))

addApp:: TInt -> TInt -> State (Context, TInt) TEqn
addApp tint1 tint2  = state (\(c,n) -> ((Exists ([tint1,tint2],[Simp(TVar (tint2), TFun (TVar (tint1),TVar (tint1-1)))])), (c,tint2)))

addFix:: State (Context, TInt) TEqn
addFix = state (\(c,n) -> ((Exists ([n+1], [Simp(TVar (n+1), TFun (TVar n, TVar n))])), (c, n+1)))

addPair:: TInt -> TInt -> State (Context, TInt) TEqn
addPair t1 t2  = state (\(c,n) -> ((Exists ([t2,t1],[Simp(TVar (t1-1), TProd (TVar (t2),TVar (t1)))])), (c,t2)))

addPCase:: TInt -> TInt -> State (Context, TInt) TEqn
addPCase t1 t2 = state (\(c,n) -> ((Exists ([t2,t1+1,t1+2,t1+3],[Simp(TVar (t2), TProd (TVar (t1+1),TVar (t1+2))),Simp(TVar t1, TVar (t1+3))])), (c,t2)))

addUnit:: State (Context, TInt) TEqn
addUnit = state(\(c,n) -> ((Simp (TVar (n), TUnit)), (c,n+1)))

addUCase:: TInt -> State (Context, TInt) TEqn
addUCase t1 = state (\(c,n) -> ((Exists ([t1], [Simp (TVar (t1), TUnit)])), (c, n)))

addLSucc:: State (Context, TInt) TEqn
addLSucc = state(\(c,n) -> ((Simp (TVar n, TFun(TNat, TNat))), (c,n+1)))

addLZero:: State (Context, TInt) TEqn
addLZero = state(\(c,n) -> ((Simp (TVar n, TNat)), (c,n+1)))

addNil:: State (Context, TInt) TEqn
addNil = state(\(c,n) -> ((Exists([n+1], [Simp (TVar n, TList (TVar (n+1)))])), (c,n+1)))
   
addCons:: State (Context, TInt) TEqn
addCons = state(\(c,n) -> ((Exists([n+1], [Simp (TVar n, TFun(TProd ((TVar (n+1)) ,TList (TVar (n+1))), TList (TVar (n+1))))])), (c,n+1)))

addLNCase:: TInt -> TInt -> TInt -> TInt -> State (Context, TInt) TEqn
addLNCase x1 y1 x2 y2 = state(\(c,n) -> ((Exists([x1,y1,x2,y2],[Simp(TVar (x1),TNat),Simp(TVar (x2),TNat),Simp(TVar (y1), TVar (y2-2)),Simp(TVar (y2),TVar (y2-2))])), (c,n)))

addLLCase:: TInt -> TInt -> TInt -> TInt -> TInt -> State (Context, TInt) TEqn
addLLCase x x1 y1 x2 y2 = state(\(c,n) -> ((Exists ([x,x1,y1,x2,y2],[Simp(TVar (x2),TProd(TVar (x),(TList (TVar (x))))),Simp(TVar x1,TList(TVar x)),Simp(TVar y1, TVar (y2-2)),Simp(TVar (y2), TVar (y2-2))])),(c,n)))

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
        (c, n1) <- get
        put(c,(n1+1))
        eqs2 <- genTypeEqnsHelper lam2        
        (c1,n2) <- get
        put(c,n2)
        eq <- addApp (n1+1) (n2)
        eqs1 <- genTypeEqnsHelper lam1         
        return (eq:(eqs2 ++ eqs1))
        
    LVar lint -> do
        (ctex,tint) <- get
        let compVal = varHelper lint ctex       
        case compVal of 
            Just val -> do
                aVar <- addVar val
                return [aVar]
            Nothing -> do 
                (c,n) <- get
                put (c,(n+1))
                return []
                  
    LFix lam1 -> do
        eq <- addFix
        eqs <- genTypeEqnsHelper lam1
        return (eq:eqs)
    
    LPair lam1 lam2 -> do      
        (c,n) <-get
        put(c,(n+1))
        eqs2 <- genTypeEqnsHelper lam2
        (c1,n1) <- get
        put(c,n1)
        eq <- addPair (n+1) n1       
        eqs1 <- genTypeEqnsHelper lam1       
        return (eq:(eqs1 ++ eqs2))
        
    LPCase lint1 lint2 lam1 lam2 -> do
        (c1,firstN) <- get
        let newC = addToContext lint1 c1 (firstN)       
        let newc2 = addToContext lint2 newC (firstN+1)
        put(newc2,firstN+3)        
        eqs2 <- genTypeEqnsHelper lam2
        (c3,thirdN) <- get
        put(c1,thirdN) 
        eq <- addPCase (firstN) (thirdN)      
        eqs1 <- genTypeEqnsHelper lam1             
        return (eq:(eqs1 ++ eqs2))
    
    LUnit -> do
        eq <- addUnit
        return [eq]
        
    LUCase lam1 lam2 -> do
        (ctext,n1) <- get        
        eqs2 <- genTypeEqnsHelper lam2
        (c2,n2) <- get
        put(ctext,n2)        
        eq <- addUCase n2               
        eqs1 <- genTypeEqnsHelper lam1       
        return (eq:(eqs1 ++ eqs2))
    
    LNCase lint1 lam1 lam2 lam3 -> do
        (c1, q) <- get
        let newC = addToContext lint1 c1 q
        put(newC, q+2)
        eqs3 <- genTypeEqnsHelper lam3
        (c2, y1) <- get
        put(c1,y1)
        eqs2 <- genTypeEqnsHelper lam2
        (c3,x1) <- get
        put(c1,x1)
        eq <- addLNCase x1 y1 (q+1) (q+2) 
        eqs1 <- genTypeEqnsHelper lam1        
        return (eq:(eqs1 ++ eqs2 ++ eqs3))
        
    LZero -> do
        eqn <- addLZero
        return [eqn]
        
    LSucc -> do
        eqn <- addLSucc
        return [eqn]
        
    LLNil -> do
        eqn <- addNil
        return [eqn]
        
    LLCons -> do
        eqn <- addCons
        return [eqn]  
 
    LLCase lint1 lam1 lam2 lam3 -> do
        (c1, q) <- get
        let newC = addToContext lint1 c1 q
        put(newC, q+2)
        eqs3 <- genTypeEqnsHelper lam3
        (c2, y1) <- get
        put(c1,y1)
        eqs2 <- genTypeEqnsHelper lam2
        (c3,x) <- get
        put(c1,(x+1))
        (c4,x1) <- get
        eq <- addLLCase x x1 y1 (q+1) (q+2) 
        eqs1 <- genTypeEqnsHelper lam1        
        return (eq:(eqs1 ++ eqs2 ++ eqs3))       


infer:: Lam -> Type
infer lam = (fix(TVar 1)) where
        fix ty = case (ty == (substituteAll ty subs)) of           
            False -> fix (substituteAll ty subs)
            True -> ty
        subs = solveTEqns (genTypeEqns lam)

    
prettyP:: [TEqn] -> String
prettyP eqns = foldr (++) "" (map pretty1 eqns)

pretty1:: TEqn -> String
pretty1 = foldTeqn (\(a,b) -> (showType a) ++ "=" ++ (showType b)++", ")
                   (\(a,b) -> "Exists" ++ (show a) ++ ":" ++ (show b))                    

solveTEqns:: [TEqn] -> [Subst]
solveTEqns [] = []
solveTEqns (t:teqns) = result where
    sub = solveTEqn t
    subs = solveTEqns teqns
    subLst =  (sub++subs)
    result = linearize subLst

solveTEqn:: TEqn -> [Subst]
solveTEqn = foldTeqn funSimp funExists where
    funSimp ((TVar n), t) = [(n, t)] :: [Subst]
    funExists (evars, []) = [] :: [Subst]
    funExists (evars, subs) = flatten $ subs :: [Subst]


foldTeqn:: ((Type,Type)-> a) -> (([TInt], [a])->a) -> TEqn -> a
foldTeqn f1 f2  (Simp (t1, t2)) = f1 (t1,t2)
foldTeqn f1 f2 (Exists (list1, list2))  = f2 (list1, map (foldTeqn f1 f2) list2 )  
        
substituteAll:: Type -> [Subst] -> Type
substituteAll typ1 [] = typ1
substituteAll typ1 (s:subs) =  substituteAll (substitute s typ1) subs --foldr (\(tint,typ2) typ3 -> substitute (tint,typ2) typ3) typ1 subs


substitute:: Subst -> Type -> Type
substitute (num, typ1) (TVar n) = case (num == n) of
    True -> typ1
    False -> TVar n
substitute (num, typ1) (TFun (t1, t2)) = TFun ((substitute (num,typ1) t1), (substitute (num,typ1) t2))
substitute (num, typ1) (TProd (t1, t2)) = TProd ((substitute (num,typ1) t1), (substitute (num,typ1) t2))
substitute (num, typ1) (TList t1) = TList (substitute (num,typ1) t1)
substitute (num, typ1) TNat = TNat
substitute (num, typ1) TUnit = TUnit

--in this function you will have to call the linearize
-- each time you combine the package, you are doing the unifcation, i.e. this is the unification step

linearize::[Subst] -> [Subst]
linearize [] = []
linearize (sub:subs) = sub:linearize(coalesce sub subs)

coalesce:: Subst -> [Subst] -> [Subst]
coalesce _ [] = []
coalesce (t,ty) ((t',ty'):subs) = union subs' subs''
    where
        subs' = coalesce (t,ty) subs
        subs'' = case (t==t') of
            True ->  match (ty,ty')
            False ->  [occursCheck(t',(substitute(t,ty) ty'))] --[occursCheck(t',(substitute(t,ty) (t',ty')))]

occursCheck:: Subst -> Subst
occursCheck subst =  case (occursHelper (fst subst)(snd subst)) of
    True -> subst
    False -> error ("occurs check fails")


occursHelper:: TInt -> Type -> Bool
occursHelper int typ = case typ of
    TUnit -> True
    TNat -> True
    TVar n -> (int /= n)
    TList typ1 -> (occursHelper int typ1)
    TFun (typ1, typ2) -> ((occursHelper int typ1) && (occursHelper int typ2))
    TProd (typ1, typ2) -> ((occursHelper int typ1) && (occursHelper int typ2))
    
match:: (Type, Type) -> [(TInt, Type)]
match (TVar t1, t2) = [occursCheck (t1,t2)]
match (t1, TVar t2) = [occursCheck (t2,t1)]
match ((TFun (t1,t2)), (TFun (t3,t4))) = ((match (t1,t3)) ++ (match (t2,t4)))
match ((TProd (t1,t2)), (TProd (t3,t4))) = ((match (t1,t3)) ++ (match (t2,t4)))
match ((TList t1), (TList t2)) = match (t1,t2) 
match (TNat, TNat) = []
match (TUnit, TUnit) = []
match _ = error("testing")

flatten:: [[a]] -> [a]
flatten []  = []
flatten xs = foldr (\acc x -> acc ++ x)[] xs
         
term = LApp (LVar 1) (LVar 1)

term1 = LAbst 1 (LApp (LVar 1)(LVar 2))

term2 = LAbst 1 (LAbst 1 (LAbst 3 (LVar 2)))

term3 = LApp ( LAbst 1 (LApp (LVar 1) (LAbst 2 (LVar 2)))) (LVar 3)

term4 = LApp ( LAbst 1 (LApp (LVar 1) (LAbst 2 (LVar 2)))) (LVar 2)

term5 = LAbst 1 (LApp (LVar 1) (LVar 2))

term6 = LAbst 1 ( LAbst 2 (LApp (LVar 1) (LVar 2)))

term7 = LFix term

term8 = LPair (LVar 1) (LVar 2)

term9 = LAbst 1 (LPCase 2 3 (LVar 1) (LPair (LVar 3)(LVar 2)))

term10 = LApp (term3) (LPCase 1 4 (LVar 3) (LPair (LVar 2)(LVar 1)))

term11 = LAbst 1 (LUCase (LVar 1) (LPair (LVar 2)(LVar 3)))

term12 = LAbst 1 (LUCase (LVar 1) (LAbst 2 (LApp (LVar 2) (LVar 3))))

term13 = LApp (LSucc) (LZero)

term14 = LApp (LAbst 1 (LApp (LVar 1)(LVar 1))) (LAbst 2 (LApp(LVar 1)(LVar 2)))

term15 = LApp (LAbst 1 (LApp(LVar 1)(LVar 1))) (LAbst 2(LApp (LVar 1)(LVar 2)))

term16 = LApp (LPair(LVar 1)(LVar 2))(LPair(LVar 2)(LVar 3))

term17 = LApp (LPair(LPair(LVar 1)(LVar 2))(LPair(LVar 3)(LVar 1))) (LAbst 1 (LApp (LVar 1)(LVar 1)))

term18 = LApp(LApp (LVar 1)(LVar 1))(LApp(LVar 1)(LVar 1))

term19 = LApp(LApp(LApp(LVar 1)(LVar 1))(LVar 1))(LVar 1)

term20 = LAbst 4 (LLCons)

term21 = LAbst 1 (LLNil)

term22 = LAbst 1 (LApp (LVar 1)(LVar 1))

--pkg = [(([],[]),[],[(5,TFun ((TVar 4),(TVar 3)))]),(([5],[]),[],[(6,TVar 2)]),(([],[]),[4,5],[])]::[Package]

--pkg2 = [(([],[]),[],[(5,TFun ((TVar 4),(TVar 3)))]),(([5],[]),[],[(6,TVar 2)]),(([],[]),[4,5],[]), (([],[]),[],[(5,TFun ((TVar 4),(TVar 3)))]),(([5],[]),[],[(6,TVar 2)]),(([],[]),[4,5],[])]::[Package]

subs = [(5,TFun ((TVar 4),(TVar 3))),(6,TVar 2), (5,TFun ((TVar 4),(TVar 3))),(6,TVar 2)]::[Subst]

term23 = LLCase 88 (LVar 1)(LVar 2)(LVar 3)

test = ((TFun ((TVar 6),(TVar 5))),(TProd((TFun((TVar 4),(TVar 3))),(TFun((TVar 2),(TVar 1))))))

term24 = LAbst 1 (LApp (LSucc)(LZero))


showType:: Type -> String
showType (TVar n) = show n
showType (TFun (t1,t2)) = "(" ++ (showType t1) ++ "->" ++ (showType t2) ++ ")"
showType (TProd (t1,t2)) = "(" ++ (showType t1) ++ "x" ++ (showType t2) ++ ")"
showType (TList t1) = "[" ++ (showType t1) ++ "] "
showType (TUnit) = "()"
showType (TNat) = "N"



