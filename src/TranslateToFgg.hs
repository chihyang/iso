module TranslateToFgg (transToFggPg) where

import Data.Foldable
import Data.String
import qualified Perpl.Struct.Lib as Perpl
import PatternMatch
import Syntax
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Debug.Trace (trace)
import Perpl.Util.JSON

transToFggPg :: (Definitions, Program) -> Result JSON
transToFggPg = undefined
