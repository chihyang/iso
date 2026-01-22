module TranslateToFgg (transToFggPg) where

import Data.Foldable
import Data.String
import qualified Perpl.Struct.Lib as Perpl
import PatternMatch
import Syntax
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Perpl.Util.FGG
import Perpl.Util.JSON
import Perpl.Util.Tensor (TensorLike)
import Debug.Trace (trace)

transToFggPg :: Bool -> (Definitions, Program) -> Result JSON
transToFggPg = undefined
