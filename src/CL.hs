module CL
    (
        ClVar,
        ClPrimitive (..), 
        ClTerm (..),
        clOccursIn
    ) where

-- Note: products are left-associative: ABCD = ((AB)C)D
type ClVar = Char
data ClPrimitive = ClS | ClK | ClI deriving (Show, Eq)
data ClTerm = 
    ClVarTerm { unClVarTerm :: ClVar } | 
    ClPrimitiveTerm {unClPrimitiveTerm :: ClPrimitive} | 
    ClAppTerm ClTerm ClTerm deriving (Show, Eq)

clOccursIn :: ClTerm -> ClTerm -> Bool
clOccursIn x (ClAppTerm u v) = 
    (x == (ClAppTerm u v)) || (clOccursIn x u) || (clOccursIn x v)
clOccursIn x y = x == y

