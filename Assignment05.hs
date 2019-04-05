{-# LANGUAGE FlexibleInstances #-}

module Assignment05 where

import Prelude hiding (init)

import SemiringFSA

data Numb = Z | S Numb deriving Show

distrib_lhs :: (Semiring a) => a -> a -> a -> a
distrib_lhs x y z = gconj x (gdisj y z)

------------------------------------------------------------------
------------------------------------------------------------------
-- IMPORTANT: Please do not change anything above here.
--            Write all your code below this line.

distrib_rhs :: (Semiring a) => a -> a -> a -> a
distrib_rhs x y z = gdisj (gconj x y) (gconj x z)

dotprod :: (Semiring v) => [v] -> [v] -> v
dotprod l1 l2 =
    case l1 of
        [] -> gfalse
        l1head:l1tail -> 
            case l2 of 
                [] -> gfalse
                l2head:l2tail ->
                    gdisj (gconj l1head l2head) (dotprod l1tail l2tail)

expn :: (Semiring a) => a -> Numb -> a
expn element numb =
    case numb of
        Z -> gtrue
        S x -> gconj element (expn element x)


backward :: (Semiring a, Ord st, Ord sy) => GenericAutomaton st sy a -> [sy] -> st -> a
backward fsa string start_state =
    let (init, accepts, transitions) = fsa in
    case string of
        [] -> fin fsa start_state
        first:rest -> 
            big_gdisj 
                [gconj 
                    (tr fsa start_state first next_state) 
                    (backward fsa rest next_state) 
                    | next_state <- allStates fsa]

val :: (Semiring a, Ord st, Ord sy) => GenericAutomaton st sy a -> [sy] -> a
val fsa string = 
    case string of
        [] -> gfalse
        first:rest -> big_gdisj [gconj 
                        (init fsa state)
                        (backward fsa string state)
                        | state <- allStates fsa]

addCost :: Cost -> Cost -> Cost
addCost c1 c2 =
    case c1 of
        TheInt x ->
            case c2 of
                TheInt y ->
                    TheInt (x + y)
                Inf -> Inf
        Inf -> Inf

minCost :: Cost -> Cost -> Cost
minCost c1 c2 =
    case c1 of
        TheInt x ->
            case c2 of
                TheInt y ->
                    if x < y 
                        then c1
                    else c2
                Inf -> c1
        Inf -> 
            case c2 of
                TheInt y ->
                    c2
                Inf -> Inf

instance Semiring Cost where
    gconj x y = addCost x y
    gdisj x y = minCost x y
    gtrue = TheInt 0
    gfalse = Inf

map_value :: String -> [String] -> [String]
map_value tomap maplist =
    case maplist of
        [] -> []
        first:rest -> (tomap ++ first) : (map_value tomap rest)

map_string :: [String] -> [String] -> [String]
map_string s1 s2 =
    case s1 of
        [] -> []
        first:rest -> (map_value first s2) ++ (map_string rest s2)



instance Semiring [String] where
    gconj x y = map_string x y
    gdisj x y = x ++ y
    gtrue = [""]
    gfalse = []

gfsa4 :: GenericAutomaton Int Char [String]
gfsa4 = ([(0, [""]), (1, []), (2, [])], 
         [(2,["t"]), (1, [""]), (0, [""])], 
         [(0, 'n', ["n"], 0), 
          (0, 't', ["t"], 0),
          (0, 'a', ["a"], 1), 
          (1, 'a', ["a"], 1), 
          (1, 'n', ["n"], 0), 
          (1, 't', [""], 2), 
          (2, 'a', ["ta", "Ta"], 1),
          (2, 'n', ["tn"], 0),
          (2, 't', ["tt"], 0)]
        )