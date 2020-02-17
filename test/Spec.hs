import Data.Set (Set)
import qualified Data.Set as Set

import Test.HUnit

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
lambdaX = AbsTerm 'x' appAtomX
lambdaY = AbsTerm 'y' appAtomY

appLambda0 = AppTerm lambdaIdentityX atom0
absFreeVar = AbsTerm 'x' appAtomY

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


testBasicOccursIn :: Test
testBasicOccursIn = TestCase $ do
    assertEqual "Basic occursIn false" 
        False 
        (occursIn variableY lambdaIdentityX) 
    assertEqual "Basic occursIn true" 
        True 
        (occursIn variableX lambdaIdentityX)    

testFreeVars :: Test
testFreeVars = TestCase $ do
    assertEqual "Variable free vars, no previous binding" 
        (freeVars variableX Set.empty)
        (Set.singleton 'x')
    assertEqual "Application free vars, no previous binding" 
        (freeVars appAtomX Set.empty)
        (Set.singleton 'x')
    assertEqual "Application free vars, with previous binding" 
        (freeVars appAtomX (Set.singleton 'x'))
        Set.empty
    assertEqual "Abstraction free vars, no free" 
        (freeVars lambdaX Set.empty)
        Set.empty
    assertEqual "Abstraction free vars, with free" 
        (freeVars absFreeVar Set.empty)
        (Set.singleton 'y')
    assertEqual "Application edge case, no free"
        (freeVars (AppTerm lambdaX lambdaY) Set.empty)
        Set.empty

testAlphaConvert :: Test
testAlphaConvert = TestCase $ 
    assertEqual "Basic alpha conversion" 
        (alphaConvert lambdaX 'x' 'y')
        lambdaY        

main :: IO Counts
main = runTestTT $ TestList 
    [testBasicOccursIn, 
    testAlphaConvert,
    testFreeVars]

--main = putStrLn "Spec!"
-- main = do
--     putStrLn $ show (alphaConvertible absAB absXY 3)
--     putStrLn $ show (alphaConvertible absAB absXY 2)
--     putStrLn $ show (alphaConvertible absAB absXY 1)
--     putStrLn $ show (alphaConvertible absAB absXY 0)
--     putStrLn $ show (alphaConvertible variableX variableX 1)
--     putStrLn $ show (alphaConvertible variableX variableY 1)        
--     putStrLn $ show (varRenamings (Set.fromList ['x', 'y', 'z']))
--     putStrLn $ show (alphaConvertible variableX variableX 0)
--     putStrLn $ show (alphaConvertible variableX variableY 0)    
--     putStrLn $ show (betaReduce doubleApp)    
--     putStrLn $ show (betaReduce appLambda0)    
--     putStrLn $ show (betaReduce variableX)    
--     putStrLn $ show (betaReduce atom0)
--     putStrLn $ show (substitute atom0 'x' variableX)
--     putStrLn $ show (substitute atom0 'x' variableY)