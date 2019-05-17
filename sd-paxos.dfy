datatype St  = E | F | L
datatype Msg = P1A(b: int) |
               P1B(b: int, c: int, v: int, s: int) |
               P2A(b: int, v: int) |
               P2B(b: int, v: int, s: int)

lemma in_range(A: set<int>, N: int)
    requires forall i :: i in A ==> 0 <= i < N
    requires N  >= 0
    ensures |A| <= N
    decreases N
{
    if (N == 0) {
        forall i | i in A
            ensures false
        {}
        assert A == {};
    } else if N - 1 in A {
        in_range(A - {N - 1}, N - 1);
    } else {
        in_range(A, N - 1);
    }
}

lemma quorums_intersect(A: set<int>, A': set<int>, N: nat)
    requires forall i :: i in A  ==> 0 <= i < N
    requires forall i :: i in A' ==> 0 <= i < N
    requires |A| + |A'| > N
    ensures A * A' != {}
{
    if A * A' == {} {
        in_range(A + A', N);
        assert false;
    }
}

method pick_with_max_cbal(xs: set<Msg>) returns (m: Msg)
    requires forall m :: m in xs ==> m.P1B?
    requires exists m :: m in xs && m.v != -1
    ensures m in xs && m.P1B? && m.v != -1
    ensures forall m' :: m' in xs && m'.P1B? && m'.v != -1 ==> m'.c <= m.c
{
    m :| m in xs && m.P1B? && m.v != -1;
    var q', q := {m}, xs - {m};
    while (q != {})
        decreases q
        invariant q + q' == xs
        invariant m in xs && m.P1B? && m.v != -1
        invariant forall m' :: m' in q' && m'.P1B? && m'.v != -1 ==> m'.c <= m.c
    {
        var y :| y in q;
        q, q' := q - {y}, q' + {y};
        if (y.P1B? && y.v != -1 && m.c < y.c) {
            m := y;
        }
    }
}

method new_bal(b: int, p: int, N: int) returns (b': int)
    requires b >= -1 && N > 0
    ensures b' > -1 && b' > b && b' % N == p
    decreases *
{
    b' := b + 1;
    while (b' % N != p)
        decreases *
        invariant b' > -1
        invariant b' > b
    {
        b' := b' + 1;
    }
}

predicate choosable(A: set<int>, b: int, v: int, bal: map<int, int>, ios: set<Msg>, ps: set<int>)
    requires bal.Keys == ps
{
    2 * |A| > |ps| && A <= ps &&
    (forall p :: p in A ==> P2B(b, v, p) in ios || bal[p] <= b)
}

predicate chosen(A: set<int>, b: int, v: int, ios: set<Msg>, ps: set<int>)
{
    2 * |A| > |ps| && A <= ps &&
    (forall p :: p in A ==> P2B(b, v, p) in ios)
}

method {:timeLimit 0} sd_paxos(ps: set<int>, N: int)
    requires N > 0 && |ps| == N
    requires forall p :: p in ps ==> 0 <= p < N
    decreases *
{
    var st:   map<int, St>       := map p | p in ps ::  E;
    var av:   map<int, int>      := map p | p in ps :: -1;
    var bal:  map<int, int>      := map p | p in ps ::  p;
    var cbal: map<int, int>      := map p | p in ps :: -1;
    var p1bs: map<int, set<Msg>> := map p | p in ps :: {};

    var ios: set<Msg> := {};

    ghost var ios' := ios;
    ghost var bal' := bal;

    while true
        decreases *

        invariant st.Keys == av.Keys == bal.Keys == cbal.Keys == p1bs.Keys == bal'.Keys == ps

        invariant forall p :: p in ps ==> bal[p] >= cbal[p] >= -1
        invariant forall p, b, c, v :: p in ps && P1B(b, c, v, p) in ios ==> b <= bal[p]
        invariant forall p, b, v :: p in ps && P2B(b, v, p) in ios ==> b <= cbal[p]
        invariant forall p, b, v, b', c', v' :: P2B(b, v, p) in ios && P1B(b', c', v', p) in ios && b' > b ==> c' >= b

        invariant forall p, b, v :: P2B(b, v, p) in ios ==> P2A(b, v) in ios
        invariant forall p :: p in ps ==> cbal[p] != -1 ==> P2A(cbal[p], av[p]) in ios
        invariant forall p, b, c, v :: P1B(b, c, v, p) in ios && c != -1 ==> P2A(c, v) in ios

        invariant forall b, v :: P2A(b, v) in ios && b != -1 ==> v != -1
        invariant forall p :: p in ps && cbal[p] != -1 ==> av[p] != -1
        invariant forall p, b, c, v :: P1B(b, c, v, p) in ios && c != -1 ==> v != -1

        invariant forall p :: p in ps && st[p] in {E, L} ==> bal[p] % N == p
        invariant forall b, v :: P2A(b, v) in ios ==> b % N in ps
        invariant forall b, v :: P2A(b, v) in ios ==> b <= bal[b % N]
        invariant forall b, v :: P2A(b, v) in ios && st[b % N] == E ==> b < bal[b % N]
        invariant forall b, v, v' :: P2A(b, v) in ios && P2A(b, v') in ios ==> v' == v

        invariant forall p, m :: p in ps && m in p1bs[p] ==> m.P1B?
        invariant forall p, m :: p in ps && m in p1bs[p] ==> m in ios
        invariant forall p, m :: p in ps && m in p1bs[p] ==> m.s in ps
        invariant forall p, m :: p in ps && st[p] == E && m in p1bs[p] ==> m.b == bal[p]
        invariant forall p, m :: p in ps && st[p] == E && m in p1bs[p] ==> bal[m.s] >= bal[p]

        invariant forall A, b, v :: chosen(A, b, v, ios, ps) ==> choosable(A, b, v, bal, ios, ps)
        invariant forall A, b, v :: choosable(A, b, v, bal, ios, ps) ==> choosable(A, b, v, bal', ios', ps)
        invariant forall A, b, v, b', v' :: choosable(A, b, v, bal, ios, ps) && P2A(b', v') in ios && b' > b > -1 ==> v' == v
        invariant forall A, A', b, v, b', v' :: chosen(A, b, v, ios, ps) && chosen(A', b', v', ios, ps) && b' > b > -1 ==> v' == v
    {
        bal' := bal; ios' := ios;

        var p     :| p in ps;
        var bcast :| bcast in {false, true};

        if bcast || ios == {} {
            var val :| val > 0;
            var b := new_bal(bal[p], p, N);

            st   := st  [p := E];
            bal  := bal [p := b];
            p1bs := p1bs[p := {}];

            ios := ios + { P1A(bal[p]) };
        } else {
            var msg :| msg in ios;

            if (msg.P1A? && bal[p] < msg.b) {
                if (bal[p] != msg.b) {
                    st := st[p := F];
                }
                bal := bal[p := msg.b];
                ios := ios + { P1B(bal[p], cbal[p], av[p], p) };
            }

            if (msg.P1B? && bal[p] == msg.b && st[p] == E && msg.s in ps) {
                p1bs   := p1bs[p := p1bs[p] + {  msg  }];
                var A' := set m | m in p1bs[p] :: m.s;

                if (2 * |A'| > N) {
                    st := st[p := L];

                    if (exists m :: m in p1bs[p] && m.v != -1) {
                        var m' := pick_with_max_cbal(p1bs[p]);
                        ios    := ios + { P2A(bal[p], m'.v) };

                        /* Begin proof */
                        forall A, b, v | choosable(A, b, v, bal, ios, ps) && bal[p] > b > -1
                        ensures m'.v == v
                        {
                            quorums_intersect(A, A', N);
                            var m :| m in p1bs[p] && m.s in A * A';
                            assert choosable(A, b, v, bal', ios', ps);
                        }
                        /* End proof */
                    } else {
                        var v'' :| v'' != -1;
                        ios     := ios + { P2A(bal[p], v'') };

                        /* Begin proof */
                        forall A, b, v | choosable(A, b, v, bal, ios, ps) && bal[p] > b > -1
                        ensures !choosable(A, b, v, bal, ios, ps)
                        {
                            quorums_intersect(A, A', N);
                            var m :| m in p1bs[p] && m.s in A * A';
                        }
                        /* End proof */
                    }
                }
            }

            if (msg.P2A? && bal[p] == msg.b) {
                av   := av  [p := msg.v];
                cbal := cbal[p := msg.b];
                ios  := ios + { P2B(bal[p], av[p], p) };
            }
        }
    }
}
