{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
module SemMC.Architecture.Location (
  Location,
  IsLocation(..),
  MemLoc(..),
  fromMemLoc,
  toMemLoc,
  ArchState
  ) where

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.Context as Ctx
import           What4.BaseTypes
import qualified What4.Interface as S


type ArchState arch ex = MapF.MapF (Location arch) ex

-- | Methods we want on state variables.
class (OrdF a, TestEquality a, ShowF a) => IsLocation a where
  -- | Try parsing a human representation of a state variable like "r8" into its
  -- representation (and its type).
  readLocation :: String -> Maybe (Some a)
  -- | Given a state variable, return a representation of its type matching its
  -- parameter.
  locationType :: a tp -> BaseTypeRepr tp
  -- | Default value for this location. Typically something like 0.
  defaultLocationExpr :: (S.IsExprBuilder sym) => sym -> a tp -> IO (S.SymExpr sym tp)
  -- | Non-memory locations
  nonMemLocations :: [Some a]
  -- | The location(s) representing memory
  memLocation :: MemLoc a
  -- | All the locations!
  allLocations :: [Some a]
  allLocations = nonMemLocations ++ [fromMemLoc memLocation]
  -- | Locations that are acceptable to use for registerization.
  --
  -- This isn't just allLocations because vector registers and control registers
  -- are not valid.  Also, on some architectures r0 is special and not allowable
  -- for holding data.
  registerizationLocations :: [Some a]
  -- | A predicate describing if a particular location is a memory location
  isMemLoc :: a tp -> Bool


-- | Represents the different registers, flags, and (eventually) memory a given
-- architecture has.
type family Location (arch :: *) :: BaseType -> *


-- A MemLoc is a way to represent a memory location by abstracting away the size
-- of bit-vector indices. We make the assumption here that memory is an array
-- with bit-vector indices of a fixed width
data MemLoc loc where
  MemLoc :: 1 S.<= w
         => S.NatRepr w
         -> loc (S.BaseArrayType (Ctx.SingleCtx (S.BaseBVType w)) xs)
         -> MemLoc loc -- (S.BaseArrayType (Ctx.SingleCtx (S.BaseBVType w)) xs)
instance ShowF loc => Show (MemLoc loc) where 
  show (MemLoc _ l) = showF l
  

fromMemLoc :: MemLoc loc -> Some loc
fromMemLoc (MemLoc _ l) = Some l

toMemLoc :: IsLocation loc => loc tp -> MemLoc loc
toMemLoc loc 
      | S.BaseArrayRepr (Ctx.Empty Ctx.:> S.BaseBVRepr w) _ <- locationType loc
        = MemLoc w loc
      | otherwise = error "The type of the memory Location in this architecture is unsupported"

