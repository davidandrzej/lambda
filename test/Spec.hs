import Data.Set (Set)
import qualified Data.Set as Set

import Test.HUnit

import Lambda
import CL

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
doubleAppChild1 = AppTerm atom0 (AppTerm lambdaX atom1) 
doubleAppChild2 = AppTerm appLambda0 (AppTerm atom0 atom1)
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
    
testAlphaConvert :: Test
testAlphaConvert = TestCase $ 
    assertEqual "Basic alpha conversion" 
        (alphaConvert lambdaX 'x' 'y')
        lambdaY        

testSubstitution :: Test
testSubstitution = TestCase $ do
    assertEqual "Basic substitution" 
        (substitute atom0 'x' variableX) atom0
    assertEqual "Basic no-op substitution" 
        (substitute atom0 'x' variableY) variableY

testBetaReduction :: Test
testBetaReduction = TestCase $ do
    assertEqual "Branching beta-reduction neighborhood" 
        (betaReduce doubleApp) [doubleAppChild1, doubleAppChild2]
    assertEqual "Basic beta-reduction" 
         (betaReduce appLambda0) [atom0]
    assertEqual "No-op beta-reduction on variable" 
        (betaReduce variableX) [variableX]      
    assertEqual "No-op beta-reduction on atom"
        (betaReduce atom0) [atom0]

testVarRenamings :: Test
testVarRenamings = TestCase $
    assertEqual "Generate candidate variable renamings"
    (Set.fromList $ varRenamings (Set.fromList ['x', 'y', 'z'])) 
    (Set.fromList [('x','y'), ('x', 'z'), ('y', 'x'), ('y', 'z'), ('z', 'x'), ('z', 'y')])

testAlphaConvertible :: Test
testAlphaConvertible = TestCase $ do
    assertEqual "Alpha convertibility check on 2-step, given 3"
        (alphaConvertible absAB absXY 3) True
    assertEqual "Alpha convertibility check on 2-step, given 2"
        (alphaConvertible absAB absXY 2) True
    assertEqual "Alpha convertibility check on 2-step, given 1"
        (alphaConvertible absAB absXY 1) False
    assertEqual "Alpha convertibility check on 2-step, given 0"
        (alphaConvertible absAB absXY 0) False
    assertEqual "Alpha convertibility check on no-op, given 1 "
        (alphaConvertible variableX variableX 1) True        
    assertEqual "Alpha convertibility check on no-op, given 0"
        (alphaConvertible variableX variableX 0) True    
    assertEqual "Alpha convertibility check on 1-step, given 1"
        (alphaConvertible variableX variableY 1) True       
    assertEqual "Alpha convertibility check on 1-step, given 0"
        (alphaConvertible variableX variableY 0) False     

lambdaTests = [testBasicOccursIn, 
    testAlphaConvert,
    testFreeVars,
    testSubstitution, 
    testBetaReduction,
    testVarRenamings,
    testAlphaConvertible]

testClNoop :: Test
testClNoop = TestCase $ 
    assertEqual "Basic CL test" ClS ClS                
clTests = [testClNoop]

main :: IO Counts
main = runTestTT $ TestList (lambdaTests ++ clTests)    