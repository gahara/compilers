{-# LANGUAGE LambdaCase, OverloadedStrings, ViewPatterns #-}

import Control.Monad
import Data.Maybe
import Control.Applicative
import Control.Arrow
import Data.List
import Data.Function
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Attoparsec.Text as A
import Data.Ord

type Terminal = Char
data NonTerminal = S
                 | NT Char
                 deriving (Eq, Show, Ord)
data Symbol = STerminal Terminal | SNonTerminal NonTerminal deriving (Eq, Show)
type Rule = [Symbol]

newtype LeftLinear = LeftLinear { unLeftLinear :: Rule } deriving (Eq, Show) --{....} - из ll вытаскивает Rule
type LeftGrammar = [(NonTerminal, LeftLinear)]
newtype RightLinear = RightLinear { unRightLinear :: Rule } deriving (Eq, Show)
type RightGrammar = [(NonTerminal, RightLinear)]

rule :: A.Parser (NonTerminal, Rule)
rule = (,) <$> nonterm <* A.skipWhile (== ' ') <* A.string "->" <* A.skipWhile (== ' ') <*> rightr 
  where nonterm = S <$ A.char 'S'
                  <|> NT <$> A.satisfy (A.inClass "A-Z")
        rightr = many (STerminal <$> term
                       <|> SNonTerminal <$> nonterm)
        term = A.satisfy (A.inClass "a-z")

run :: A.Parser a -> String -> Either String a
run p = A.parseOnly (p <* A.endOfInput) . T.pack

isTerm :: Symbol -> Bool
isTerm (STerminal _) = True
isTerm (SNonTerminal _) = False

isNonterm :: Symbol -> Bool
isNonterm (STerminal _) = False
isNonterm (SNonTerminal _) = True

extract :: (Rule -> Maybe a) -> [(NonTerminal, Rule)] -> [(NonTerminal, a)]
extract f = map $ second $ fromJust . f

--guard - Nothing если false и Just(), а <$ подменяет то, что внутри функутора на другое
leftLinear :: Rule -> Maybe LeftLinear
leftLinear ss = LeftLinear ss <$ guard (check ss)
  where check :: Rule -> Bool	
        check ((SNonTerminal _):t) = all isTerm t
        check r = all isTerm r

rightLinear :: Rule -> Maybe RightLinear
rightLinear ss = RightLinear ss <$ guard (check ss)
  where check :: Rule -> Bool
        check [] = True
        check [SNonTerminal _] = True
        check ((STerminal _):t) = check t
        check _ = False

leftToRight :: LeftGrammar -> RightGrammar
leftToRight = extract rightLinear . map (convert . second unLeftLinear)
  where convert :: (NonTerminal, Rule) -> (NonTerminal, Rule)
        convert (S, r) | all isTerm r = (S, r)
        convert (a@(NT _), r) | all isTerm r = (S, r ++ [SNonTerminal a])
        convert (b@(NT _), (SNonTerminal a):r)| all isTerm r = ( a, r ++ [SNonTerminal b])
        convert (S, (SNonTerminal a):r) | all isTerm r = (a, r)
        convert _ = error "impossible"

data RegularExpression = EmptySet
                       | EmptyString
                       | Letter Char
                       | Concat RegularExpression RegularExpression
                       | Alteration RegularExpression RegularExpression
                       | Star RegularExpression
                       deriving (Eq)

instance Show RegularExpression where
  show EmptySet = "@"
  show EmptyString = ""
  show (Letter a) = pure a
  show (Concat a b) = show a ++ show b
  show (Alteration a b) = show a ++ " + " ++ show b
  show (Star a) = "(" ++ show a ++ ")*"

type RightExpr = Map (Maybe NonTerminal) RegularExpression

toEq :: RightGrammar -> Map NonTerminal RightExpr
toEq = groupAll convert . map (second unRightLinear)
  where convert :: [(NonTerminal, Rule)] -> (NonTerminal, RightExpr)
        convert list@((nt, _):_) = (nt, groupAll sumexpr $ map (toexpr . snd) list)
        convert _ = error "impossible"
        toexpr :: Rule -> (Maybe NonTerminal, RegularExpression) 
        toexpr list = let (t, nt) = span isTerm list
                      in ( listToMaybe $ map (\(SNonTerminal a) -> a) nt
                         , toReg $ map (\(STerminal a) -> a) t
                         )
        toReg :: [Terminal] -> RegularExpression
        toReg [] = EmptyString
        toReg (h:t) = Letter h `Concat` toReg t
        groupAll f = M.fromList . map f . groupBy ((==) `on` fst) . sortBy (comparing fst)
        sumexpr :: [(Maybe NonTerminal, RegularExpression)] -> (Maybe NonTerminal, RegularExpression)
        sumexpr list@((nt, _):_) = (nt, foldr1 Alteration $ map snd list)
        sumexpr _ = error "impossible"
        -- toReg = foldl (\a h -> Concat a (Letter h)) EmptyString


solve :: Map NonTerminal RightExpr -> RegularExpression
solve = (M.! Nothing) . snd . last . walk . M.toDescList
  where walk ::[(NonTerminal, RightExpr)] -> [(NonTerminal, RightExpr)]
        walk [] = []
        walk ((nt, vars):t) = let vars' = replaceSelf nt vars
                              in (nt, vars') : walk (map (second $ replace nt vars') t)
        replaceSelf :: NonTerminal -> RightExpr -> RightExpr
        replaceSelf nt re = case M.lookup (Just nt) re of
          Just r -> M.map (\r' -> Star r `Concat` r') $ M.delete (Just nt) re
          Nothing -> re
        replace :: NonTerminal -> RightExpr -> RightExpr -> RightExpr
        replace nt from to = case M.lookup (Just nt) to of
          Just r -> let from' = M.map (\r' -> r `Concat` r') from 
                    in M.unionWith Alteration from' to
          Nothing -> to

-- ------

type Error = String

newtype Parser a = Parser { runParser :: String -> Either Error (a, String) }

instance Monad Parser where
  -- return :: a -> Parser a
  return a = Parser $ \s -> Right (a, s) 
  -- (>>=) :: Parser a -> (a -> Parser b) -> Parser b
  a >>= b = Parser $ \s -> case runParser a s of
    Left e  -> Left e
    Right (res, s') -> runParser (b res) s'   
  -- fail :: Error -> Parser a
  fail s = Parser $ \_ -> Left s

instance Alternative Parser where
  -- empty :: Parser a
  empty = fail "can't parse"
  -- (<|>) :: Parser a -> Parser a -> Parser a
  a <|> b = Parser $ \s -> case runParser a s of
    Left _ -> runParser b s
    Right r -> Right r

anyChar :: Parser Char
anyChar = Parser $ \case
  "" -> Left "empty string"
  h:t -> Right (h, t)

-- --------

instance Functor Parser where
  fmap = liftM

instance Applicative Parser where
  pure = return
  (<*>) = ap

instance MonadPlus Parser where
  mzero = empty
  mplus = (<|>)

endOfInput :: Parser ()
endOfInput = do
  r <- optional anyChar
  case r of
    Nothing -> return ()
    Just _ -> fail "not end of string"

removeEmpty :: (RegularExpression -> RegularExpression -> RegularExpression)
            ->  RegularExpression -> RegularExpression -> RegularExpression
removeEmpty _ EmptyString b = b
removeEmpty _ a EmptyString = a
removeEmpty f a b = f a b

simplify :: RegularExpression -> RegularExpression
simplify (Concat a b) = removeEmpty Concat (simplify a) (simplify b)
simplify (Alteration a b) = Alteration (simplify a) (simplify b)
simplify (Star (simplify -> a)) = case a of
  EmptyString -> a
  Star _ -> a
  Alteration e1 e2 -> Star $ removeEmpty Alteration e1 e2
  _ -> Star a
simplify a = a

parseRegex :: RegularExpression -> Parser String
parseRegex re = conv (simplify re) <* endOfInput
  where conv :: RegularExpression -> Parser String
        conv EmptySet = fail "empty set"
        conv EmptyString = return ""
        conv (Letter c) = do
          r <- anyChar
          unless (r == c) $ fail "not proper symbol"
          return $ pure r
        -- (++) :: [a] -> [a] -> [a]
        conv (Concat re1 re2) = (++) <$> conv re1 <*> conv re2
        conv (Alteration re1 re2) = conv re1 <|> conv re2
        conv (Star re') = concat <$> many (conv re')


--------------
--here begins lab 2.
--------------
type CFGrammar = [(NonTerminal, Rule)]
deleteUnreachable :: CFGrammar  -> CFGrammar 
deleteUnreachable old = loop S
  where loop :: NonTerminal -> CFGrammar 
        --loop nt = filter ((== nt) . fst) old ++ concatMap (loop . (\(SNonTerminal x) -> x)) (filter isNonterm old)
        loop nt = let r = filter ((== nt) . fst) old
          in r ++ concatMap (loop . (\(SNonTerminal x) -> x)) (filter isNonterm $ concatMap snd r)

-- deleteUnreachable :: CFGrammar  -> CFGrammar 
-- deleteUnreachable old = loop S
--   where loop :: NonTerminal -> CFGrammar 
--         --loop nt = filter ((== nt) . fst) old ++ (map loop (map (\(SNonTerminal x) -> x) . filter isNonterm)) --x - Nonterminal
--         loop nt = filter ((== nt) . fst) old ++ concatMap (loop . (\(SNonTerminal x) -> x)) (filter isNonterm old)

--summ :: Int -> Int -> Int
--summ a b = a+b

-- *Main> runParser
-- *Main> let rules = [(S,[SNonTerminal (NT 'A'),STerminal 'a']), (NT 'A',[STerminal 'a',STerminal 'b'])]
-- *Main> solve $ toEq $ leftToRight $ extract leftLinear rules
-- aba
-- *Main> let reg = solve $ toEq $ leftToRight $ extract leftLinear rules
-- *Main> reg
-- aba
-- *Main> runParser (parseRegex reg) "ab"
-- Left "empty string"
-- *Main> runParser (parseRegex reg) "a"
-- Left "empty string"
-- *Main> runParser (parseRegex reg) "aba"
-- Right ("aba","")
-- *Main> runParser (parseRegex reg) "abaa"
-- Left "not end of string"
-- *Main> run rule "a -> a"
-- Left "Failed reading: satisfy"
-- *Main> run rule "A -> a"
-- Right (NT 'A',[STerminal 'a'])
-- *Main> map (run rule) ["A -> a", "S -> c"]
-- [Right (NT 'A',[STerminal 'a']),Right (S,[STerminal 'c'])]
-- *Main>
