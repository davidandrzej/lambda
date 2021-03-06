module Lambda
    ( occursIn,
        freeVars,
        alphaConvert,
        substitute,
        betaReduce,
        alphaConvertible,
        varRenamings,
        Variable, Atomic, 
        Term (..)
    ) where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.List 

type Variable = Char
type Atomic = Int
data Term = 
    VarTerm { unVarTerm :: Variable }  | 
    AtomTerm Atomic | 
    AppTerm Term Term |
    AbsTerm { binding :: Variable, body :: Term} deriving (Show, Eq)
    
-- (very) hacky way to generate "new" variable names, chosen
-- from an artificially constrained set of possibilities 
allVars = Set.fromList ['a', 'b', 'c', 'd', 'x', 'y', 'z']
newVar :: Variable -> Variable -> Variable
newVar v1 v2 = head $ Set.toList (Set.delete v2 (Set.delete v1 allVars))
    
--substitution 
substitute :: Term -> Variable -> Term -> Term
substitute termVal tgtVar (AtomTerm a) = AtomTerm a
substitute termVal tgtVar (VarTerm v) = 
    if(v == tgtVar) then termVal else (VarTerm v)
substitute termVal tgtVar (AppTerm lt rt) = 
    AppTerm (substitute termVal tgtVar lt) (substitute termVal tgtVar rt)
substitute termVal tgtVar (AbsTerm bindVar bodyTerm) = 
    if(bindVar == tgtVar)
    then AbsTerm tgtVar bodyTerm -- Sub "overridden" by binding, so no-op
    else
        let fvBody = freeVars bodyTerm Set.empty
            fvVal = freeVars termVal Set.empty
        in
            if(not $ Set.member tgtVar fvBody)
            then AbsTerm bindVar bodyTerm -- No free occurrence, so no-op
            else
                if(not $ Set.member bindVar fvVal) 
                -- Inner binding _not_ a FV in new term (no rename necessary)
                then AbsTerm bindVar (substitute termVal tgtVar bodyTerm) 
                -- Inner binding is FV in new term, need to do rename
                else 
                    let uniqVar = newVar tgtVar bindVar
                    in AbsTerm uniqVar (substitute termVal tgtVar ( 
                        substitute (VarTerm uniqVar) bindVar bodyTerm
                    ))                    

-- beta reduction: find any instance of an application
-- where left term is abstraction, then do substitution
--
-- Put another way, this function is going to give you the 
-- 1-neighborhood of the \triangleright_{1\beta} relation 
-- 
-- TODO is this associativity logic correct?
--
betaReduce :: Term -> [Term]
betaReduce a@(AtomTerm _) = [a]
betaReduce v@(VarTerm _) = [v]
betaReduce (AbsTerm bindVar bodyTerm) = 
    (\x -> (AbsTerm bindVar x)) <$> (betaReduce bodyTerm)
betaReduce (AppTerm (AbsTerm bindVar bodyTerm) rt) = 
    [substitute rt bindVar bodyTerm]
betaReduce (AppTerm lt rt) = 
    ((\x -> (AppTerm x rt)) <$> (betaReduce lt)) ++
    ((\x -> (AppTerm lt x)) <$> (betaReduce rt))

-- Can we convert A into B by some finite sequence
-- of alpha-conversions? For now, let's brute-force
-- over the space of possible variable re-namings
alphaConvertible :: Term -> Term -> Int -> Bool
alphaConvertible src tgt 0 = (src == tgt)
alphaConvertible src tgt n = 
    if (src == tgt) 
        then True 
        else -- generate all 1-adjacent alpha conversions
            let alphaAdjacent = ((uncurry (alphaConvert src)) <$>  (varRenamings allVars))
            in 
                (any (== tgt) alphaAdjacent) || -- any 1-adjacent match?
                (any (\x -> alphaConvertible x tgt (n - 1)) alphaAdjacent) -- otherwise continue BFS

-- Helper function to generate all possible renamings
varRenamings :: Set.Set Variable -> [(Variable, Variable)]
varRenamings varSet = _varRenamings $ Set.toList varSet

_varRenamings :: [Variable] -> [(Variable, Variable)]
_varRenamings (x : xs) = 
    (concat $ (\y -> [(x,y), (y,x)]) <$> xs) ++ (_varRenamings xs) 
_varRenamings _ = []

alphaConvert :: Term -> Variable -> Variable -> Term
alphaConvert (AtomTerm a) _ _ = (AtomTerm a)
alphaConvert (VarTerm v) src tgt = 
    if(v == src) then VarTerm tgt else VarTerm v
alphaConvert (AppTerm lt rt) src tgt = 
    AppTerm (alphaConvert lt src tgt) (alphaConvert rt src tgt)
alphaConvert (AbsTerm boundVar bodyTerm) src tgt = 
    let convertedBody = (alphaConvert bodyTerm src tgt) 
    in if(boundVar == src)
        then (AbsTerm tgt convertedBody)
        else (AbsTerm boundVar convertedBody)

freeVars :: Term -> Set Variable -> Set Variable
freeVars (VarTerm v) bound = 
    if Set.member v bound 
        then Set.empty
        else Set.singleton v
freeVars (AtomTerm _) _ = Set.empty
freeVars (AppTerm lt rt) bound = 
    Set.union (freeVars lt bound) (freeVars rt bound)
freeVars (AbsTerm bindVar bodyTerm) bound = 
    freeVars bodyTerm (Set.insert bindVar bound)

occursIn :: Term -> Term -> Bool
occursIn (VarTerm v1) (VarTerm v2) = v1 == v2
occursIn (AtomTerm a1) (AtomTerm a2) = a1 == a2
occursIn t1 t2@(AbsTerm _ bd) = t1 == t2 || occursIn t1 bd
occursIn t1 t2@(AppTerm at1 at2) = t1 == t2 || occursIn t1 at1 || occursIn t1 at2
occursIn _ _ = False
