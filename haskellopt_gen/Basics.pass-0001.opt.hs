-- Generated Haskell code from Graph optimizer
-- Core obtained from: The Glorious Glasgow Haskell Compilation System, version 8.6.3
-- Optimized after GHC phase:
--   Simplifier: Max iterations = 4
--               SimplMode {Phase = 0 [Non-opt simplification],
--                          inline,
--                          no rules,
--                          eta-expand,
--                          case-of-case}
-- Total nodes: 270; Boxes: 38; Branches: 2
-- Apps: 112; Lams: 6; Unreduced Redexes: 0

{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE MagicHash #-}

module Basics (fTest4,x,gTest1,gTest6,gTest2,f,fTest3,gTest5,fTest0,fTest2,g,gTest4,fTest1,gTest0,k,foo,gTest3) where

import GHC.Num
import GHC.Types

f = (\x' -> (((GHC.Num.*) x') x'))

fTest0 = (((GHC.Num.*) (((GHC.Num.*) x'2) x'2)) (((GHC.Num.*) x'3) x'3))

x'2 = (GHC.Types.I# 11#)

x'3 = (GHC.Types.I# 22#)

fTest1 = (((GHC.Num.*) x) x)

x = (((GHC.Num.*) x'11) x'11)

fTest2 = (((GHC.Num.+) (((GHC.Num.*) x'4) x'4)) (((GHC.Num.*) x'5) x'5))

x'4 = (GHC.Types.I# 44#)

x'5 = (((GHC.Num.*) x'16) x'16)

fTest3 = (((GHC.Num.*) (((GHC.Num.*) x'6) x'6)) (((GHC.Num.*) x'7) x'7))

x'6 = (((GHC.Num.*) x'17) x'17)

x'7 = (((GHC.Num.*) x'13) x'13)

fTest4 = (((GHC.Num.+) (((GHC.Num.*) x'8) x'8)) (((GHC.Num.*) x'9) x'9))

x'8 = (((GHC.Num.*) x'14) x'14)

x'9 = (((GHC.Num.*) x'15) x'15)

foo = (\x'12 -> let { tmp = (((GHC.Num.*) x'12) (GHC.Types.I# 2#)) } in (((GHC.Num.+) tmp) tmp))

g = (\x'10 -> (\y -> (((GHC.Num.*) x'10) y)))

gTest0 = (((GHC.Num.*) (((GHC.Num.*) (GHC.Types.I# 2#)) (GHC.Types.I# 3#))) (GHC.Types.I# 4#))

gTest1 = (((GHC.Num.*) (GHC.Types.I# 4#)) (((GHC.Num.*) (GHC.Types.I# 2#)) (GHC.Types.I# 3#)))

gTest2 = (\y' -> (((GHC.Num.*) (((GHC.Num.*) (GHC.Types.I# 2#)) (GHC.Types.I# 3#))) y'))

gTest3 = (((GHC.Num.*) (((GHC.Num.*) (GHC.Types.I# 2#)) (GHC.Types.I# 3#))) (GHC.Types.I# 4#))

gTest4 = (((GHC.Num.*) (((GHC.Num.*) (GHC.Types.I# 2#)) (GHC.Types.I# 3#))) (((GHC.Num.*) (GHC.Types.I# 4#)) (GHC.Types.I# 5#)))

gTest5 = (((GHC.Num.+) (_0(# (GHC.Types.I# 30#) #))) (_0(# (GHC.Types.I# 40#) #)))

_0(# z' #) = (((GHC.Num.*) (((GHC.Num.*) (GHC.Types.I# 11#)) z')) (((GHC.Num.*) z') (GHC.Types.I# 22#)))

gTest6 = (((GHC.Num.*) (((GHC.Num.*) (GHC.Types.I# 44#)) (GHC.Types.I# 33#))) (GHC.Types.I# 11#))

k = (\z -> (_0(# z #)))

x'11 = (GHC.Types.I# 33#)

x'13 = (GHC.Types.I# 77#)

x'14 = (GHC.Types.I# 66#)

x'15 = (GHC.Types.I# 77#)

x'16 = (GHC.Types.I# 55#)

x'17 = (GHC.Types.I# 66#)
