module CL
    (
        ClVariable,
        ClPrimitive (..), 
        ClTerm (..)
    ) where

type ClVariable = Char
data ClPrimitive = ClS | ClK | ClI deriving (Show, Eq)
data ClTerm = ClVar | ClPrimitive | ClApp ClTerm ClTerm deriving (Show, Eq)

