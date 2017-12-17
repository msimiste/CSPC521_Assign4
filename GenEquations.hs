module GenEquations where

import A4
import Control.Monad.State
import Data.List
import Data.Maybe

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
