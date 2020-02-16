import Data.Set (Set)
import qualified Data.Set as Set

import Lambda

atom1 = AtomTerm 1
atom0 = AtomTerm 0
lambdaIdentityX = AbsTerm (unVarTerm variableX) variableX
variableX = VarTerm 'x'
variableY = VarTerm 'y'
variableZ = VarTerm 'z'
variableB = VarTerm 'b'
variableA = VarTerm 'a'
appAtomX = AppTerm atom0 variableX
lambdaX = AbsTerm (unVarTerm variableX) appAtomX
appLambda0 = AppTerm lambdaIdentityX atom0

doubleApp = AppTerm appLambda0 (AppTerm lambdaX atom1) 
-- (\x.x 0)(\x.(0 x) 1)
-- 1-nbd should be 
-- (0 (\x.(0 x) 1)
-- (\x.x 0)(0 1) 

-- Test case for 2-distance alpha convertibility
appAtomY = AppTerm atom0 variableY
appAtomB = AppTerm atom0 variableB
absXY = AbsTerm 'x' (AbsTerm 'y' appAtomY)
absAB = AbsTerm 'a' (AbsTerm 'b' appAtomB)


main :: IO ()
main = do
    putStrLn $ show (alphaConvertible absAB absXY 3)
    putStrLn $ show (alphaConvertible absAB absXY 2)
    putStrLn $ show (alphaConvertible absAB absXY 1)
    putStrLn $ show (alphaConvertible absAB absXY 0)
    putStrLn $ show (alphaConvertible variableX variableX 1)
    putStrLn $ show (alphaConvertible variableX variableY 1)        
    putStrLn $ show (varRenamings (Set.fromList ['x', 'y', 'z']))
    putStrLn $ show (alphaConvertible variableX variableX 0)
    putStrLn $ show (alphaConvertible variableX variableY 0)    
    putStrLn $ show (betaReduce doubleApp)    
    putStrLn $ show (betaReduce appLambda0)    
    putStrLn $ show (betaReduce variableX)    
    putStrLn $ show (betaReduce atom0)
    putStrLn $ show (substitute atom0 'x' variableX)
    putStrLn $ show (substitute atom0 'x' variableY)
    putStrLn $ show (alphaConvert lambdaX 'x' 'y')
    putStrLn $ show (freeVars appAtomX Set.empty)
    putStrLn $ show (freeVars appAtomX (Set.singleton (unVarTerm variableX)))
    putStrLn $ show (freeVars variableX (Set.singleton (unVarTerm variableX)))
    putStrLn $ show (freeVars variableX Set.empty)
    putStrLn $ show (occursIn variableX lambdaIdentityX)    
    putStrLn $ show (occursIn variableY lambdaIdentityX)    