-- | Definition of the S-Expression tokens used to encode the
-- formula for an opcode's semantics.  These S-Expressions are written
-- by DSL specifications of the opcode semantics and other methods;
-- the S-Expressions are read during Template Haskell expansion of the
-- SemMC.TH.attachSemantics to compile into the Haskell Formula
-- representation for passing semantics details to Crucible for
-- evaluation.

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module SemMC.Formula.SETokens
    ( FAtom(..)
    , string, ident, quoted, int, bitvec
    , string', ident', quoted', int', bitvec'
    , fromFoldable, fromFoldable'
    , printAtom, printTokens, printTokens'
    , parseLL
    )
    where

import qualified Data.Foldable as F
import qualified Data.SCargot as SC
import qualified Data.SCargot.Comments as SC
import           Data.SCargot.LetBind
import qualified Data.SCargot.Repr as SC
import qualified Data.SCargot.Repr.Rich as SE
import           Data.Semigroup
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import           Numeric.Natural ( Natural )
import qualified Text.Parsec as P
import           Text.Parsec.Text ( Parser )
import           Text.Printf ( printf )

import           Prelude

data FAtom = AIdent String
           | AQuoted String
           | AString String
           | AInt Integer
           | ABV Int Integer
           | ANamed String Int FAtom
           deriving (Show, Eq)


string :: String -> SC.SExpr FAtom
string = SE.fromRich . string'
string' :: String -> SC.RichSExpr FAtom
string' = SE.A . AString

-- | Lift an unquoted identifier.
ident :: String -> SC.SExpr FAtom
ident = SE.fromRich . ident'
ident' :: String -> SC.RichSExpr FAtom
ident' = SE.A . AIdent

-- | Lift a quoted identifier.
quoted :: String -> SC.SExpr FAtom
quoted = SE.fromRich . quoted'
quoted' :: String -> SE.RichSExpr FAtom
quoted' = SE.A . AQuoted

-- | Lift an integer.
int :: Integer -> SC.SExpr FAtom
int = SE.fromRich . int'
int' :: Integer -> SE.RichSExpr FAtom
int' = SE.A . AInt

-- | Lift a bitvector.
bitvec :: Natural -> Integer -> SC.SExpr FAtom
bitvec w v = SE.fromRich $ bitvec' w v
bitvec' :: Natural -> Integer -> SE.RichSExpr FAtom
bitvec' w v = SE.A $ ABV (fromEnum w) v


-- * Miscellaneous operations on the S-Expressions

-- | Turn any 'Foldable' into an s-expression by transforming each element with
-- the given function, then assembling as you would expect.
fromFoldable :: (F.Foldable f) => (a -> SC.SExpr atom) -> f a -> SC.SExpr atom
fromFoldable f = F.foldr (SC.SCons . f) SC.SNil

-- | @fromFoldable id@
fromFoldable' :: (F.Foldable f) => f (SC.SExpr atom) -> SC.SExpr atom
fromFoldable' = fromFoldable id

-- * Output of the S-Expression Formula language


-- | Generates the the S-expression tokens represented by the sexpr
-- argument, preceeded by a list of strings output as comments.
printTokens' :: Seq.Seq String -> SC.RichSExpr FAtom -> T.Text
printTokens' comments = printTokens comments . SE.fromRich

printTokens :: Seq.Seq String -> SC.SExpr FAtom -> T.Text
printTokens comments sexpr =
  let oguide = nativeGuide AIdent nameFor
      guide = oguide { weighting = weighter (weighting oguide)
                     , allowRecursion = True
                     , minExprSize = 10
                     -- , maxLetBinds = min 8 . (`div` 2)
                     , maxLetBinds = id
                     }
      nameFor n e = case nameOf 0 e of
                      Nothing -> AIdent n
                      Just n' -> AIdent n'
      nameOf d (SC.SAtom (ANamed n' d' _)) = if d == d' then Just n' else Nothing
      nameOf d (SC.SCons l _) = nameOf (d+1) l
      nameOf _ _ = Nothing
      weighter _ expr cnt = case nameOf 0 expr of
                              Just _ -> 1000000 -- always bind this!
                              Nothing -> let bl = case expr of
                                                    (SC.SCons (SC.SAtom _) _) -> 500 -- higher baseline
                                                    _ -> 0
                                             h = F.length expr
                                             w = bl + h + (2 * cnt)
                                         in if w > 600 then w else 0
      outputFmt = SC.setIndentAmount 1 $ SC.unconstrainedPrint printAtom
  in formatComment comments <> (SC.encodeOne outputFmt $
                                discoverLetBindings guide sexpr)


formatComment :: Seq.Seq String -> T.Text
formatComment c
  | Seq.null c = T.empty
  | otherwise = T.pack $ unlines $ fmap formatLine (F.toList c)
  where
    formatLine l = printf ";; %s" l


printAtom :: FAtom -> T.Text
printAtom a =
  case a of
    AIdent s -> T.pack s
    AQuoted s -> T.pack ('\'' : s)
    AString s -> T.pack (show s)
    AInt i -> T.pack (show i)
    ABV w val -> formatBV w val
    ANamed _ _ e -> printAtom e


formatBV :: Int -> Integer -> T.Text
formatBV w val = T.pack (prefix ++ printf fmt val)
  where
    (prefix, fmt)
      | w `rem` 4 == 0 = ("#x", "%0" ++ show (w `div` 4) ++ "x")
      | otherwise = ("#b", "%0" ++ show w ++ "b")


-- * Input and parse of the S-Expression Formula language

-- | This is only the base-level parsing of atoms.  The full language
-- parsing is handled by the base here and the Parser definitions.

parseIdent :: Parser String
parseIdent = (:) <$> first <*> P.many rest
  where first = P.letter P.<|> P.oneOf "+-=<>_"
        rest = P.letter P.<|> P.digit P.<|> P.oneOf "+-=<>_"

parseString :: Parser String
parseString = do
  _ <- P.char '"'
  s <- P.many (P.noneOf ['"'])
  _ <- P.char '"'
  return s

parseBV :: Parser (Int, Integer)
parseBV = P.char '#' >> ((P.char 'b' >> parseBin) P.<|> (P.char 'x' >> parseHex))
  where parseBin = P.oneOf "10" >>= \d -> parseBin' (1, if d == '1' then 1 else 0)

        parseBin' :: (Int, Integer) -> Parser (Int, Integer)
        parseBin' (bits, x) = do
          P.optionMaybe (P.oneOf "10") >>= \case
            Just d -> parseBin' (bits + 1, x * 2 + (if d == '1' then 1 else 0))
            Nothing -> return (bits, x)

        parseHex = (\s -> (length s * 4, read ("0x" ++ s))) <$> P.many1 P.hexDigit

parseAtom :: Parser FAtom
parseAtom
  =   AIdent      <$> parseIdent
  P.<|> AQuoted     <$> (P.char '\'' >> parseIdent)
  P.<|> AString     <$> parseString
  P.<|> AInt . read <$> P.many1 P.digit
  P.<|> uncurry ABV <$> parseBV
   -- n.b. an ANamed is an internal marker and not expressed or
   -- recoverable in the streamed text version

parserLL :: SC.SExprParser FAtom (SC.SExpr FAtom)
parserLL = SC.withLispComments (SC.mkParser parseAtom)

parseLL :: T.Text -> Either String (SC.SExpr FAtom)
parseLL t = letExpand getIdent <$> SC.decodeOne parserLL t
    where getIdent (AIdent s) = Just s
          getIdent _ = Nothing
