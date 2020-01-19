module Lib
    ( someFunc
    ) where

import Data.Set (Set)
import qualified Data.Set as Set

-- Data structure
-- term: variable, const, application (MN), abstraction (\x.M)
--
-- Functions
-- substitution [N/x]M
-- alpha-conversion (and congruence)
-- beta-reduction (and convertible)
-- 
--

type Variable = Char
type Atomic = Int
data Term = 
    VarTerm { unVarTerm :: Variable }  | 
    AtomTerm Atomic | 
    AppTerm Term Term |
    AbsTerm { binding :: Variable, body :: Term} deriving (Show, Eq)
    
    
atom0 = AtomTerm 0
lambdaIdentityX = AbsTerm (unVarTerm variableX) variableX
variableX = VarTerm 'x'
variableY = VarTerm 'y'
appAtomX = AppTerm atom0 variableX
lambdaX = AbsTerm (unVarTerm variableX) appAtomX

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

someFunc :: IO ()
someFunc = do
    putStrLn $ show (alphaConvert lambdaX 'x' 'y')
    putStrLn $ show (freeVars appAtomX Set.empty)
    putStrLn $ show (freeVars appAtomX (Set.singleton (unVarTerm variableX)))
    putStrLn $ show (freeVars variableX (Set.singleton (unVarTerm variableX)))
    putStrLn $ show (freeVars variableX Set.empty)
    putStrLn $ show (occursIn variableX lambdaIdentityX)    
    putStrLn $ show (occursIn variableY lambdaIdentityX)    