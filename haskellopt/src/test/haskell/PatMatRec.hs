module PatMatRec where


t0_ [a] = t0 [a]
t0 [a] = t0 [a]
t0'0 = t0 [1]
t0'1 = t0 []

t1_ [a] = a : t1 [a+1]
t1 [a] = a : t1 [a+1]
t1'0 xs = t1 xs
t1'1 x = t1'0 [x]
t1'2 = t1'0 [0]

t2_ [a,b] = (a - b) : t2 [b,a]
t2 [a,b] = (a - b) : t2 [b,a]
t2'0 = t2 [0,1]
t2'1 = case t2'0 of { a:b:_ -> (a,b) }


-- usum [] = 0
-- usum (x : xs) = x + usum xs
-- usum'0 = usum []
-- -- usum'1 = usum [1] -- FIXME scheduled pgrm missing a def; also, when active alone, seems to cause divergence
-- -- usum'2 = usum [1,2] -- FIXME scheduled pgrm missing a def

