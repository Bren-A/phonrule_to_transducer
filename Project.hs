{-# LANGUAGE FlexibleInstances #-}

module Project where

import Prelude hiding (Nothing)

import Assignment05

import Data.Set (fromList, toList)

data PhonRight = Nothing | WordBound | Maybe String deriving Show

type PhonologicalRule sl sr = (sl, sl, sr, sr)

type GenericAutomaton st sy v = ([(st,v)], [(st,v)], [(st,sy,v,st)])

set :: (Ord a) => [a] -> [a]
set xs = toList (fromList xs)

test1 :: PhonologicalRule Char PhonRight
test1 = ('t', 'T', Maybe "u", Maybe "e")

test2 :: PhonologicalRule Char PhonRight
test2 = ('t', 'T', Maybe "up", Maybe "e")

test3 :: PhonologicalRule Char PhonRight
test3 = ('t', 'T', Maybe "u", Maybe "u")

test4 :: PhonologicalRule Char PhonRight
test4 = ('t', 'T', Nothing, Maybe "u")

test5 :: PhonologicalRule Char PhonRight
test5 = ('t', 'T', Maybe "u", Nothing)

test6 :: PhonologicalRule Char PhonRight
test6 = ('t', 'T', Maybe "upper", Nothing)

test7 :: PhonologicalRule Char PhonRight
test7 = ('t', 'T', Nothing, Nothing)

test8 = ('t', 'T', WordBound, Maybe "u")


-- Array that has default for everything
base :: [(Int, Char, [String], Int)]
base = [(0, c, [[c]], 0) | c <- "abcdefghijklmnopqrstuvwxyz"]

-- Makes transitions based on the string
-- This version has each transition return a string version
-- of what it consumed.
-- i is the state counter
create_transitions_consume :: Int -> String -> [(Int, Char, [String], Int)]
create_transitions_consume i string =
    case string of
        [] -> []
        first:rest -> (i, first, [[first]], i+1)
            : create_transitions_consume (i+1) rest

-- Same as create_transitions_consume but 
-- does not add the last value and returns empty instead
create_transitions_only :: Int -> String -> [(Int, Char, [String], Int)]
create_transitions_only i string =
    case string of
        -- Do not account for last string!!
        [x] -> []
        first:rest -> (i, first, [""], i+1)
            : create_transitions_only (i+1) rest

-- Makes all but initial state empty
create_init :: Int -> [(Int, [String])]
create_init i =
    case i of
        1 -> [(i, [])]
        _ -> (i, []) : create_final_empty (i-1)

-- Creates accept states for the final transitions
create_final_empty :: Int -> [(Int, [String])]
create_final_empty i =
    case i of
        1 -> [(i, [""])]
        _ -> (i, [""]) : create_final_empty (i-1)

-- Creates accept states for gamma transitions
create_final_values :: Char -> String -> String -> Int -> [(Int, [String])]
create_final_values append current string i =
    case string of
        [x] -> [] -- [(i, [[append] ++ current])]
        first:rest -> (i, [[append] ++ current]) 
            : create_final_values append (current ++ [first]) rest (i+1)


-- Case where there's a requirement on both sides of the rule
both_sides :: PhonologicalRule Char PhonRight 
                -> GenericAutomaton Int Char [String]
both_sides (alpha, beta, Maybe lambda, Maybe gamma) = 
    let state_2 = length lambda in
    let state_3 = length gamma in

    let init = create_init (state_2 + state_3) in

    let lambda_final = create_final_empty state_2 in
    let gamma_final = create_final_values beta [head gamma] gamma (state_2+1) in

    let lambda_transition = create_transitions_consume 0 lambda in
    let gamma_transition = create_transitions_only (state_2+1) gamma in
    
        (
            init ++
                [(0, [""])], 

            lambda_final ++
                gamma_final ++
                [(state_2 + 1,[[alpha]]), (1, [""]), (0, [""])], 

            base ++ 
                lambda_transition ++
                gamma_transition ++
                [(state_2, alpha, [""], state_2 + 1), 
                -- end of gamma leads back to initial state
                (state_2 + state_3, last gamma, [[beta] ++ gamma], 0)]
        )

-- Creates transition values for all alphabet
char_transitions :: String -> Int -> Int
                        -> [(Int, Char, [String], Int)]
char_transitions string i j =
    [(i, c, [string ++[c]], j) | c <- "abcdefghijklmnopqrstuvwxyz"]

-- Removes a transition rule containing the given character
-- In the transition character position
filter_transitions :: Char -> [(Int, Char, [String], Int)] 
                         -> [(Int, Char, [String], Int)]
filter_transitions char transitions =
    case transitions of
        [] -> []
        first:rest ->
            let (start, alpha, string, end) = first in
            if alpha == char then
                filter_transitions char rest
            else first : filter_transitions char rest

-- Case that both sides of a rule are the same value
both_sides_equal :: PhonologicalRule Char PhonRight 
                -> GenericAutomaton Int Char [String]
both_sides_equal (alpha, beta, Maybe lambda, Maybe gamma) = 
    -- Initialize length of each argument
    let state_2 = length lambda in
    
    let init = create_init (state_2 * 2) in

    let lambda_final = create_final_empty state_2 in
    let gamma_final = create_final_values beta [head lambda] lambda (state_2+1) in
    
    -- Transitions from one main state to the next 
    let lambda_transition = create_transitions_consume 0 lambda in
    let gamma_transition = create_transitions_only (state_2+1) lambda in
     
    -- State 2 to init transitions
    let to_init = filter_transitions 
                        (head lambda)
                        (char_transitions [alpha] (state_2+1) 0) in
    -- Complete gamma to initial
    let to_init_2 = -- filter_transitions
                    --    (last lambda)
                        (char_transitions [alpha] (state_2 * 2) 0) in

       (
        init ++
            [(0, [""])], 

        lambda_final ++
            gamma_final ++
            [(state_2 + 1,[[alpha]]), (1, [""]), (0, [""])], 

        base ++ 
            lambda_transition ++
            gamma_transition ++
            to_init ++
            to_init_2 ++
            --to_init_from_2 ++
            [(state_2, alpha, [""], state_2 + 1), 
            -- end of gamma leads back to beginning of gamma state
            (state_2 * 2, last lambda, [[beta] ++ lambda], state_2),
            --(state_2 * 2, last lambda, [[beta] ++ lambda], 0),
            -- Loop back to self (second state transitions)
            (state_2, head lambda, [[head lambda]], 1)]
        )

no_lambda :: PhonologicalRule Char PhonRight 
                -> GenericAutomaton Int Char [String]
no_lambda (alpha, beta, Nothing, Maybe gamma) = 
     let state_3 = length gamma in
     let gamma_transition = create_transitions_only (1) gamma in
     let gamma_final = create_final_values beta [head gamma] gamma (1) in
     let init = create_init (1 + state_3) in
      (
        init ++
        [(0, [""])], 

         gamma_final ++
         [(1,[[alpha]]), (0, [""])], 

         base ++ 
         gamma_transition ++
         [(0, alpha, [""], 1), 
         -- end of gamma leads back to beginning of gamma state
        (state_3, last gamma, [[beta] ++ gamma], 0)]
        )

no_gamma :: PhonologicalRule Char PhonRight 
                -> GenericAutomaton Int Char [String]
no_gamma (alpha, beta, Maybe lambda, Nothing) = 
    let state_2 = length lambda in
    let lambda_transition = create_transitions_consume 0 lambda in
    let lambda_final = create_final_empty state_2 in
    let init = create_init (state_2) in
      (
        init ++
        [(0, [""])], 

        lambda_final ++
        [(state_2 + 1,[[alpha]]), (1, [""]), (0, [""])], 

        base ++ 
        lambda_transition ++
        -- end after alpha instead since no gamma
        [(state_2, alpha, [[beta]], 0)]
        )

no_neither :: PhonologicalRule Char PhonRight 
                -> GenericAutomaton Int Char [String]
no_neither (alpha, beta, Nothing, Nothing) = 
    (
        [(0, [""])], 

        [(0, [""])], 

        base ++ 
        -- end after alpha instead since no gamma
        [(0, alpha, [[beta]], 0)]
        )

-- Cases where there is a word boundary instead for the rules


bound_left :: PhonologicalRule Char PhonRight 
                -> GenericAutomaton Int Char [String]
bound_left (alpha, beta, WordBound, Maybe gamma) = 
    let length_gamma = length gamma in
    let gamma_transition = create_transitions_only 1 gamma in
    let gamma_final = create_final_values beta [head gamma] gamma (1) in

    let self_loop_end = char_transitions "" (length_gamma + 1) (length_gamma + 1) in
    let new_base = filter_transitions alpha base in
        (
            [(0, [""])],
            
            gamma_final ++
            [(0, [])],
            
            -- Do not add if first character is alpha until
            -- gamma is followed after.
            new_base ++
            gamma_transition ++
            self_loop_end ++
            [(0, alpha, [""], 1),
             (length_gamma, last gamma, [[beta] ++ gamma], length_gamma + 1)]
        )



bound_right :: PhonologicalRule Char PhonRight 
                -> GenericAutomaton Int Char [String]
bound_right (alpha, beta, Maybe lambda, WordBound) = 
    (
        [],
        [],
        []
    )


phonRule_to_Transducer:: PhonologicalRule Char PhonRight 
                -> GenericAutomaton Int Char [String]
phonRule_to_Transducer phonRule =
    let (alpha, beta, lambda, gamma) = phonRule in 
    case lambda of
        Maybe x ->
            case gamma of
                Maybe y ->
                    if x == y then
                        both_sides_equal phonRule
                    else
                        both_sides phonRule
                Nothing ->
                    no_gamma phonRule
        Nothing ->
            case gamma of
                Maybe x ->
                    no_lambda phonRule
                Nothing ->
                    no_neither phonRule
        WordBound ->
            case gamma of
                Maybe x ->
                    no_lambda phonRule
                Nothing ->
                    no_neither phonRule
                WordBound ->











