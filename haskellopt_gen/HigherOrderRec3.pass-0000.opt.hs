-- Generated Haskell code from Graph optimizer
-- Core obtained from: The Glorious Glasgow Haskell Compilation System, version 8.6.3
-- Optimized after GHC phase:
--   desugar
-- Total nodes: 59; Boxes: 19; Branches: 11
-- Apps: 6; Lams: 6; Unreduced Redexes: 2

{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE MagicHash #-}

module HigherOrderRec (rec7,rec7Test1,rec0_0,rec7Test0,rec0) where

import GHC.Base
import GHC.Num

rec0 = (\f -> (_0(# f #)))

_0(# f' #) = (f' (\x -> ((_0(# f' #)) x)))

rec0_0 = GHC.Base.id

rec7 = (\g -> (_2(# (_1(# g #)) #)))

_2(# g' #) = (\ds -> (case ds of {() -> g'}))

_1(# g'2 #) = (g'2 (_1(# (_3(# g'2 #)) #)))

rec7Test0 = (_2(# (_1(# ((GHC.Num.+) 1) #)) #))

rec7Test1 = (_2(# (_4(# (_1(# (_3(# (\ds' -> (_4(# ds' #))) #)) #)) #)) #))

_4(# ds'2 #) = (((GHC.Num.*) ds'2) 2)

_3(# g'3 #) = g'3
