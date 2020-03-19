module CL
    (
        ClVar,
        ClPrimitive (..), 
        ClTerm (..),
        clOccursIn,
        weaklyReduces
    ) where

-- Note: products are left-associative: ABCD = ((AB)C)D
type ClVar = Char
data ClPrimitive = ClS | ClK | ClI deriving (Show, Eq)
data ClCurried = 
    ClKX {unClKX :: ClTerm} |
    ClSX {unClSX :: ClTerm} |
    ClSXY {unClSXY_X :: ClTerm, unClSXY_Y :: ClTerm} 
    deriving (Show, Eq)

data ClTerm = 
    ClVarTerm { unClVarTerm :: ClVar } | 
    ClPrimitiveTerm { unClPrimitiveTerm :: ClPrimitive } | 
    ClAppTerm ClTerm ClTerm |
    ClCurriedTerm { unClCurriedTerm :: ClCurried }
    deriving (Show, Eq)
    -- Need to add "curried" variants of ClK and ClS

-- Apply a single weak reduction step
weaklyReduces :: ClTerm -> ClTerm
weaklyReduces vt@(ClVarTerm _) = vt
weaklyReduces ct@(ClPrimitiveTerm _) = ct
weaklyReduces (ClAppTerm (ClPrimitiveTerm p) x) = 
    case p of 
        ClI -> x
        ClS -> ClCurriedTerm (ClSX x)
        ClK -> ClCurriedTerm (ClKX x)
weaklyReduces (ClAppTerm (ClCurriedTerm c) a) = 
    case c of 
        ClKX x -> x
        ClSX x -> ClCurriedTerm (ClSXY x a)
        ClSXY x y -> 
            ClAppTerm 
            (ClAppTerm x a)
            (ClAppTerm y a) 
weaklyReduces (ClAppTerm (ClVarTerm v) y) = 
    ClAppTerm (ClVarTerm v) (weaklyReduces y)
weaklyReduces (ClAppTerm x y) = ClAppTerm (weaklyReduces x) y

clOccursIn :: ClTerm -> ClTerm -> Bool
clOccursIn x (ClAppTerm u v) = 
    (x == (ClAppTerm u v)) || (clOccursIn x u) || (clOccursIn x v)
clOccursIn x y = x == y

