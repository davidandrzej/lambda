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

-- Container for all Lambda tests        
lambdaTests = [testBasicOccursIn, 
    testAlphaConvert,
    testFreeVars,
    testSubstitution, 
    testBetaReduction,
    testVarRenamings,
    testAlphaConvertible]

clVarA = ClVarTerm 'a'
clVarB = ClVarTerm 'b'
clVarC = ClVarTerm 'c'
clTermS = ClPrimitiveTerm ClS
clTermK = ClPrimitiveTerm ClK
clTermI = ClPrimitiveTerm ClI

testClOccursIn :: Test
testClOccursIn = TestCase $ do 
    assertEqual "clOccursIn on basic combinator - yes" 
        (clOccursIn clTermS clTermS) True 
    assertEqual "clOccursIn on variable - yes" 
        (clOccursIn clVarA clVarA) True         
    assertEqual "clOccursIn in application - yes" 
        (clOccursIn clTermS (ClAppTerm clTermS clTermI)) True 
    assertEqual "clOccursIn on application - yes" 
        (clOccursIn (ClAppTerm clTermS clTermI)
                    (ClAppTerm clTermS clTermI)) True 
    assertEqual "clOccursIn on basic combinator - no"
        (clOccursIn clTermS clTermK) False
    assertEqual "clOccursIn on variable - no"
        (clOccursIn clVarA clTermK) False
    assertEqual "clOccursIn in application - no"
        (clOccursIn clTermS (ClAppTerm clTermK clTermI)) False
    assertEqual "clOccursIn on application - no"
        (clOccursIn (ClAppTerm clTermS clTermI) 
                    (ClAppTerm clTermK clTermI)) False

clAppAI = ClAppTerm clVarA clTermI
clAppIA = ClAppTerm clTermI clVarA
clAppKA = ClAppTerm clTermK clVarA
clAppKAB = ClAppTerm (ClAppTerm clTermK clVarA) clVarB
clAppSABC = ClAppTerm (ClAppTerm (ClAppTerm clTermS clVarA) clVarB) clVarC

testClWeaklyReduces :: Test
testClWeaklyReduces = TestCase $ do
    assertEqual "clWeaklyReduces on basic variable"
        (weaklyReduces clVarA) clVarA
    assertEqual "clWeaklyReduces on primitive"
        (weaklyReduces clTermS) clTermS
    assertEqual "clWeaklyReduces on aI"
        (weaklyReduces clAppAI) clAppAI
    assertEqual "clWeaklyReduces on Ia"
        (weaklyReduces clAppIA) clVarA
    assertEqual "clWeaklyReduces on Kab"
        (weaklyReduces (weaklyReduces clAppKAB)) clVarA
    assertEqual "clWeaklyReduces on aKab"
        (weaklyReduces (weaklyReduces (ClAppTerm clVarA clAppKAB))) 
        (ClAppTerm clVarA clVarA)
    assertEqual "clWeaklyReduces on Sabc"
        (weaklyReduces (weaklyReduces (weaklyReduces clAppSABC)))
        (ClAppTerm (ClAppTerm clVarA clVarC) (ClAppTerm clVarB clVarC))

-- Container for all CL tests
clTests = [testClOccursIn, testClWeaklyReduces]

main :: IO Counts
main = runTestTT $ TestList (lambdaTests ++ clTests)    