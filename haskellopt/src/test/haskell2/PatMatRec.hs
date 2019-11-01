module PatMatRec where

t0_ [a] = t0 [a]
t0_ _ = 666
t0 [a] = t0 [a]
t0 _ = 666
t0'0 = t0 [1]
t0'1 = t0 []

t1_ [a] = a : t1 [a+1]
t1_ _ = [666]
t1 [a] = a : t1 [a+1]
t1 _ = [666]
t1'0 xs = t1 xs
t1'1 x = t1'0 [x]
t1'2 = t1'0 [0]

t2_ [a,b] = (a - b) : t2 [b,a]
t2_ _ = [666]
t2 [a,b] = (a - b) : t2 [b,a]
t2 _ = [666]
t2'0 = t2 [0,1]
-- FIXME conflicting defs:
-- t2'1 = case t2'0 of { a : b : _ -> (a,b); _ -> (666,666) }
