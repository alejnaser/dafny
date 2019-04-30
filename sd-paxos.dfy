datatype St  = E | F | L
datatype Msg = P1A(b: int) |
               P1B(b: int, c: int, v: int, s: int) |
               P2A(b: int, v: int) |
               P2B(b: int, v: int, s: int) 

function domain<U,V>(m: map<U, V>): set<U>
{
    set u | u in m :: u
}

lemma InRange(A: set<int>, N: int)
    requires forall i :: i in A ==> 0 <= i < N
    requires N >= 0
	ensures |A| <= N
	decreases N
{
	if (N == 0) {
		forall i | i in A
			ensures false
		{}
		assert A == {};
	} else if N - 1 in A {
		InRange(A - {N - 1}, N - 1);
	} else {
		InRange(A, N - 1);
	}
}

lemma QuorumsIntersect(A: set<int>, A': set<int>, N: nat)
    requires forall i :: i in A ==> 0 <= i < N
    requires forall i :: i in A' ==> 0 <= i < N
	requires |A| + |A'| > N
	ensures A * A' != {}
{
	if A * A' == {} {
		InRange(A + A', N);
		assert false;
	}
}

method xj0(xs: set<Msg>) returns (m: Msg)
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

predicate P(A: set<int>, b: int, v: int, bal: map<int, int>, ios: set<Msg>, ps: set<int>)
    requires domain(bal) == ps
{
    2 * |A| > |ps| && A <= ps && 
    forall p :: p in A ==> P2B(b, v, p) in ios || bal[p] <= b
}

method SdPaxos(ps: set<int>, N: int)
    requires N > 0 && |ps| == N
    requires forall p :: p in ps ==> 0 <= p < N
    decreases *
{
    var st: map<int, St>    := map p | p in ps ::  E;
    var av: map<int, int>   := map p | p in ps :: -1;
    var bal: map<int, int>  := map p | p in ps ::  p;
    var cbal: map<int, int> := map p | p in ps :: -1;
    var p1bs: map<int, set<Msg>> := map p | p in ps :: {};

    var ios: set<Msg> := {};

    ghost var bal': map<int, int>;
    ghost var ios': set<Msg>;

    while true
        decreases *
    
        invariant domain(st)   == ps
        invariant domain(av)   == ps
        invariant domain(bal)  == ps
        invariant domain(cbal) == ps
        invariant domain(p1bs) == ps

        invariant forall p :: p in ps ==> bal[p] >= cbal[p]
        invariant forall p :: p in ps ==> cbal[p] != -1 ==> av[p] != -1
        invariant forall p :: p in ps && st[p] in {E, L} ==> bal[p] % N == p      

        invariant forall p, m :: p in ps && m in p1bs[p] ==> m.P1B?
        invariant forall p, m :: p in ps && m in p1bs[p] ==> m in ios
        invariant forall p, m :: p in ps && m in p1bs[p] ==> m.s in ps
        invariant forall p, m :: p in ps && st[p] == E && m in p1bs[p] ==> m.b == bal[p]

        invariant forall p, b, v :: P2B(b, v, p) in ios ==> P2A(b, v) in ios
        invariant forall p :: p in ps && av[p] != -1 ==> P2A(cbal[p], av[p]) in ios
        invariant forall p, b, c, v :: P1B(b, c, v, p) in ios && v != -1 ==> P2A(c, v) in ios
        invariant forall p, b, c, v :: P1B(b, c, v, p) in ios && c != -1 ==> v != -1

        invariant forall b, v :: P2A(b, v) in ios ==> b % N in ps
        invariant forall b, v :: P2A(b, v) in ios ==> b <= bal[b % N]
        invariant forall p, b, v :: p in ps && P2B(b, v, p) in ios ==> b <= cbal[p]
        invariant forall p, b, c, v :: p in ps && P1B(b, c, v, p) in ios ==> b <= bal[p]
        invariant forall p, b, v, b', c', v' :: P2B(b, v, p) in ios && P1B(b', c', v', p) in ios && b' > b ==> c' >= b

        invariant forall b, v :: P2A(b, v) in ios && st[b % N] == E ==> b < bal[b % N]
        invariant forall b, v, v' :: P2A(b, v) in ios && P2A(b, v') in ios ==> v' == v

        invariant forall A, b, v, b', v' :: P(A, b, v, bal, ios, ps) && P2A(b', v') in ios && b' > b ==> v' == v
    {
        bal' := bal; ios' := ios;

        var p :| p in ps;
        var bcast :| bcast in {false, true};

        if bcast || ios == {} {
            var val :|  val > 0;
            var b := *; assume b > bal[p] && b % N == p;

            st   := st [p := E];
            bal  := bal[p := b];
            p1bs := p1bs  [p := {}];

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
                p1bs := p1bs[p := p1bs[p] + {  msg  }];
                var A' := set m | m in p1bs[p] :: m.s;
                assert A' <= ps && p1bs[p] <= ios;

                if (2 * |A'| > N) {
                    st  := st[p := L];
                    if (forall m :: m in p1bs[p] ==> m.v == -1) {
                        var v': int;
                        ios := ios + { P2A(bal[p], v') };
                    } else {
                        var m' := xj0(p1bs[p]);                    
                        var v' := m'.v;
                        ios := ios + { P2A(bal[p], v') };

                        /* Begin proof */
                        forall A, b, v | P(A, b, v, bal, ios, ps) && bal[p] > b
                        ensures v' == v
                        {
                            QuorumsIntersect(A, A', N);
                            var m :| m in p1bs[p] && m.s in A * A';
                            assert m.s in A && m.s in A' && bal[m.s] >= bal[p] &&
                                   (P2B(b, v, m.s) in ios || bal[m.s] <= b) &&
                                   m.c >= b && m.v != -1;

                            //assume m.v != -1;
                            //assert m.c >= b;
                            //assert m'.c >= m.c;
                            //assert m'.c >= b;
                            //assert (m' in ios && m'.c >= b);
                            //assert m'.c >= b;
                            if (m'.c > b) {
                                assert P(A, b, v, bal', ios', ps);
                                assert P2A(m'.c, v') in ios';
                            }
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

        assert forall A, b, v :: P(A, b, v, bal, ios, ps) ==> P(A, b, v, bal', ios', ps);
    }
}
