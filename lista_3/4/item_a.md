
# Finding C and P

## C
p1 = store(p0, 0, &a[0]);
p2 = store(p1, 1, 0)
g2 = x == 0;
a1 = store(a0, i0, 0);
a2 = a0;
a3 = store(a2, i0+1,1);
a4 = ite(g1, a1, a3);
p4 = store(p2, 1, select(p2, 1)+2);

## P
i0>=0
i0<2
i0+1<2
i0+1>=0
select(select(p3,0), select(p3,1)) == 1
select(p3,0) == &a[0]