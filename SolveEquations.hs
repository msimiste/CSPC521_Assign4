module SolveEquations where

import GenEquations
import A4
import Data.List
import Data.Maybe



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
