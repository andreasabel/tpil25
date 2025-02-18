Proving the correctness of alpha-beta pruning
=============================================

Alpha-beta algorithm.
```
    v(t) : "value of node t"
    ch(t): "children of node t"

    I = (a, b): "alpha-beta interval"
    (a,b) ⊂ (a1,b1) = a1 ≤ a ∧ b ≤ b1

    p = true  : "Max player"
    p = false : "Min player"

    ⊥(true)  = "-inf"
    ⊥(false) = "+inf"

    v ≤true w  = v <= w
    v ≤false w = v >= w

    (a,b)[true =v] = (v,b)
    (a,b)[false=v] = (a,v)

    ab(p, 0,   I, t) = v(t)
    ab(p, d+1, I, t) = abs(p, d, I, bot(p), ch(t))

    abs(p, d, I, v, []  ) = v
    abs(p, d, I, v, t:ts)
      | v1 ≤p v  = abs(p, d, I, v, ts)
      | I ≤p v1  = v1
      | otherwise = abs(d, I[p=v1], v1, ts)
      where
      v1 = ab(¬p, d, I, t)
```

Lemma: If `I1 ⫃ I2` then

  1. `ab(p, d, I1, t)     ≤p ab(p, d, I2, t)`.
  2. `abs(p,d, I1, v, ts) ≤p abs(p, d, I2, v, ts)`  if  `v ≤p I1`  and  `v ≤p I2`.

Proof by induction on `d`:
1. - Case `0`: by reflexivity since `ab(_, 0, _, t) = v(t)`
   - Case `d+1`: by induction hypothesis for `abs`
2. By side induction on `ch(t)`:
   - Case `[]`: by reflexivity
   - Case `t:ts`: Let `v_i = ab(¬p, d, I_i, t)`.
     By induction hypothesis on `ab` we have `v1 ≤(¬p) v2` meaning `v2 ≤p v1`.
     - Subcase `v1 ≤p v`: Then `v2 ≤p v` by transitivity so the goal simplifies to
       `abs(p, d, I1, v, ts) ≤p abs(p, d, I2, v, ts)` which is the induction hypothesis.
     - Subcase `I2 ≤p v2` which implies `I1 ≤p v1` by transitivity.
       If we can reduce the goal with the second clause on each side,
       with `v ≤p v1` and `v ≤p v2`
       we would reach the goal `v1 ≤p v2` which is only possible if `v1 = v2`.
       We would like to reduce our goal to compute
     - Subcase `v ≤p v1` and `I1 ≤p v1`