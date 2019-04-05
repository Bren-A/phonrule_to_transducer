module SemiringFSA where

import Prelude hiding (init)

import Data.Set (fromList, toList)

-- A little trick for eliminating duplicates from a list
set :: (Ord a) => [a] -> [a]
set xs = toList (fromList xs)

-----------------------------------------------------------
-- Our type for automata with the possibility of computing 
-- something other than booleans.

type GenericAutomaton st sy v = ([(st,v)], [(st,v)], [(st,sy,v,st)])

-- Just pulls out all the states mentioned anywhere in a GenericAutomaton
allStates :: (Ord st, Ord sy) => GenericAutomaton st sy a -> [st]
allStates (starts, ends, trs) = set ([q | (q,p) <- starts] ++ 
                                     [q | (q,p) <- ends] ++ 
                                     [q1 | (q1,x,p,q2) <- trs] ++ 
                                     [q2 | (q1,x,p,q2) <- trs])

-----------------------------------------------------------
-- Now we'll define three examples, with different value 
-- types: gfsa1 has probabilities, gfsa2 has booleans, 
-- and gfsa3 has ``costs''.

data WordSegState = Edge | Internal deriving (Show, Eq, Ord)

-- Corresponds to the PFSA used in examples in class. 
gfsa1 :: GenericAutomaton WordSegState Char Double
gfsa1 = 
    ([(Edge, 1.0)],
     [(Edge, 0.5)],
     [(Edge, 'a', 0.015, Edge),     (Internal, 'a', 0.042, Edge),
      (Edge, 'i', 0.015, Edge),     (Internal, 'e', 0.056, Edge),
                                    (Internal, 'i', 0.014, Edge),
                                    (Internal, 'n', 0.098, Edge),
                                    (Internal, 't', 0.084, Edge),
                                    (Internal, 's', 0.154, Edge), 
      (Edge, 'a', 0.103, Internal), (Internal, 'a', 0.085, Internal),
      (Edge, 'e', 0.029, Internal), (Internal, 'e', 0.149, Internal),
      (Edge, 'i', 0.088, Internal), (Internal, 'i', 0.149, Internal),
      (Edge, 'n', 0.029, Internal), (Internal, 'n', 0.085, Internal),
      (Edge, 't', 0.103, Internal), (Internal, 't', 0.021, Internal),
      (Edge, 's', 0.118, Internal), (Internal, 's', 0.064, Internal)
     ])

-- Here's our old friend, the FSA over the alphabet {C,V} that 
-- requires either two Cs or two Vs (or both), now expressed as a 
-- generic automaton that has booleans as its values. 
-- See section 2.1 of the semirings handout.
gfsa2 :: GenericAutomaton Int Char Bool
gfsa2 = ([(40, True)], 
         [(43, True)], 
         [(40, 'C', True, 40),      (41, 'C', True, 43),
          (40, 'V', True, 40),      (42, 'V', True, 43),
          (40, 'C', True, 41),      (43, 'C', True, 43),
          (40, 'V', True, 42),      (43, 'V', True, 43)]
        )

-- Now we define a cost type, which is either ``infinite'' 
-- or an integer. See section 2.3 of the handout.
data Cost = Inf | TheInt Int deriving Show

-- ... and then use it to define an FSA where each possible 
-- start, end and transition has a cost.
gfsa3 :: GenericAutomaton Int Char Cost
gfsa3 = ([(10, TheInt 0)], 
         [(12, TheInt 0)], 
         [(10, 'C', TheInt 5, 10), 
          (10, 'V', TheInt 4, 10), 
          (10, 'C', TheInt 0, 11), 
          (11, 'C', TheInt 0, 12), 
          (12, 'C', TheInt 7, 12), 
          (12, 'V', TheInt 8, 12)]
        )

-- You can see, in ProbFSA.hs, how to write functions for working with 
-- probabilistic FSAs such as gfsa1 above, i.e. backwardProb and 
-- valProb, corresponding to (3) on the handout. 
-- That's a good start, but it's no use for gfsa2 ... to work with gfsa2 
-- we might write a separate function
--     valBool :: GenericAutomaton st sy Bool -> [sy] -> Bool
-- that does conjunctions and disjunctions, corresponding to (16) 
-- on the handout (actually you did some of this last week in HW4). 
-- And if we want to do things with gfsa3, we might write a separate function 
--     valCost :: GenericAutomaton st sy Cost -> [sy] -> Cost
-- which adds up costs in some places and then picks the smallest 
-- cost in some other places, corresponding to (20) on the handout. 
-- But no! That would be painfully repetitive. There's a better way ...

-----------------------------------------------------------
-- Now, introduce the idea of a semiring.

-- This says, ``Some types are semiring types. To be a semiring 
-- type you need to have two two-place functions called `gconj' and 
-- `gdisj', and two elements called `gtrue' and `gfalse'.'' 
-- These four things are named for ``generalized conjunction'', 
-- ``generalized disjunction'', ``generalized true'' and 
-- ``generalized false''; see section 3 on the handout.
class Semiring a where
    gconj :: a -> a -> a
    gdisj :: a -> a -> a
    gtrue :: a
    gfalse :: a

-- Now we can write functions that will be well-defined for 
-- any semiring type: as long as `a' is a semiring type, we 
-- know it has a two-place function called `gconj' and an 
-- element called `gtrue', so we can use them to write big_gconj. 
-- Similarly for big_gdisj.
-- (If the base cases of these look odd, try evaluating `sum []' 
-- and `product []' in ghci and think about why those results make sense.)
big_gconj :: Semiring a => [a] -> a
big_gconj list = case list of {[] -> gtrue; (x:xs) -> gconj x (big_gconj xs)}
big_gdisj :: Semiring a => [a] -> a
big_gdisj list = case list of {[] -> gfalse; (x:xs) -> gdisj x (big_gdisj xs)}

init :: (Semiring v, Ord st) => GenericAutomaton st sy v -> st -> v
init (starts, ends, trs) q = big_gdisj [v | (q',v) <- starts, q == q']

fin :: (Semiring v, Ord st) => GenericAutomaton st sy v -> st -> v
fin (starts, ends, trs) q = big_gdisj [v | (q',v) <- ends, q == q']

tr :: (Semiring v, Ord st, Ord sy) => GenericAutomaton st sy v -> st -> sy -> st -> v
tr (starts, ends, trs) q1 x q2 = big_gdisj [p | (q,y,p,q') <- trs, (q,y,q') == (q1,x,q2)]

-----------------------------------------------------------
-- Now we introduce some specific semirings.

-- This says, ``Bool is a semiring type. When some code 
-- based on semirings uses `gconj x y', what that means for 
-- the type Bool is `x && y'; when some semiring code uses 
-- `gdisj x y', what that means for Bool is `x || y'; etc.''
instance Semiring Bool where
    gconj x y = x && y
    gdisj x y = x || y
    gtrue = True
    gfalse = False

-- Similarly for the Double type. 
-- When some code based on semirings uses `gconj x y', what 
-- that means for the type Double is `x * y'; etc.
instance Semiring Double where
    gconj x y = x * y
    gdisj x y = x + y
    gtrue = 1.0
    gfalse = 0.0

