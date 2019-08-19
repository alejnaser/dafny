datatype St  = L | F | R | S

datatype Msg = BROADCAST(m: int) |
               ACCEPT(b: int, k: int, m: int) |
               ACCEPT_ACK(b: int, k: int, m: int, s: int) |
               COMMIT(b: int, k: int, m: int) |
               NEW_LEADER(b: int) |
               NEW_LEADER_ACK(b: int, c: int, log: map<int, int>, s: int) |
               NEW_STATE(b: int, log: map<int, int>) |
               NEW_STATE_ACK(b: int, s: int)

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

lemma quorums_intersect(ps: set<int>, N: int)
    requires N > 0 && |ps| == N
    requires forall p :: p in ps ==> 0 <= p < N
    ensures forall A, A' :: A <= ps && A' <= ps && N < 2 * |A| && N < 2 * |A'| ==>  A * A' != {}
{
    forall A, A' | A <= ps && A' <= ps && 2 * |A| > N && 2 * |A'| > N
        ensures A * A' != {}
    {
        if A * A' == {} {
            in_range(A + A', N);
            assert false;
        }
    }
}

method max(xs: set<int>) returns (m: int)
    ensures xs != {} ==> (m in xs && forall x :: x in xs ==> x <= m)
    ensures xs == {} ==> m == -1
{
    if (xs != {}) {
        m :| m in xs;
        var q', q := {m}, xs - {m};
        while (q != {})
            decreases q
            invariant q + q' == xs
            invariant m in q'
            invariant q' != {} ==> (m in q' && forall x :: x in q' ==> x <= m)
        {
            var y :| y in q;
            q, q' := q - {y}, q' + {y};
            if (m < y) {
                m := y;
            }
        }
    } else {
        return -1;
    }
}

method pick_with_max_cbal_and_len(acks: set<Msg>) returns (m: Msg)
    requires acks != {}
    requires forall m :: m in acks ==> m.NEW_LEADER_ACK?
    ensures m in acks
    ensures forall m' :: m' in acks ==> m'.c < m.c || (m'.c == m.c && |m'.log| <= |m.log|)
{
    m :| m in acks;
    var q', q := {m}, acks - {m};
    while (q != {})
        decreases q
        invariant q + q' == acks
        invariant m in acks
        invariant forall m' :: m' in q' ==>  m'.c < m.c || (m'.c == m.c && |m'.log| <= |m.log|)
    {
        var y :| y in q;
        q, q' := q - {y}, q' + {y};
        if (m.c < y.c || (m.c == y.c && |y.log| > |m.log|)) {
            m := y;
        }
    }
}

method new_bal(b: int, p: int, N: int) returns (b': int)
    requires b >= -1 && N > 0
    ensures b' > b && b' % N == p
    decreases *
{
    b' := b + 1;
    while (b' % N != p)
        decreases *
        invariant b' > b
    {
        b' := b' + 1;
    }
}

predicate is_prefix(s: seq<(int, int)>, s': seq<(int, int)>)
{
    |s| <= |s'| && forall i :: 0 <= i < |s| ==> s[i].1 == s'[i].1
}

predicate choosable(A: set<int>, b: int, k: int, m: int, ps: set<int>, bal: map<int, int>, ios: set<Msg>)
    requires bal.Keys == ps
{
    2 * |A| >= |ps| && A <= ps &&
    forall p :: p in A ==> (ACCEPT_ACK(b, k, m, p) in ios || bal[p] <= b)
}

method zab(ps: set<int>, N: int)
    requires N > 0 && |ps| == N
    requires forall p :: p in ps ==> 0 <= p < N
    decreases *
{
    var st: map<int, St> := map p | p in ps :: F;
    var log: map<int, map<int, int>> := map p | p in ps :: map[];
    var bal: map<int, int> := map p | p in ps :: -1;
    var cbal: map<int, int> := map p | p in ps :: -1;
    var next: map<int, int> := map p | p in ps :: -1;

    var last_delivered: map<int, int> := map p | p in ps :: -1;
    var dlog: map<int, seq<(int, int)>> := map p | p in ps :: [];

    var accept_acks: map<int, map<int, set<Msg>>> := map p | p in ps :: map[];
    var new_leader_acks: map<int, set<Msg>> := map p | p in ps :: {};
    var new_state_acks: map<int, set<Msg>> := map p | p in ps :: {};

    var ios: set<Msg> := {};

    var bal' := bal;
    var ios' := ios;

    quorums_intersect(ps, N);

    while (true)
        decreases *

        invariant st.Keys == log.Keys == bal.Keys == cbal.Keys == next.Keys ==
                  last_delivered.Keys == dlog.Keys == accept_acks.Keys ==
                  new_leader_acks.Keys == new_state_acks.Keys == bal'.Keys == ps

        invariant forall b, s :: NEW_STATE_ACK(b, s) in ios ==> s in ps
        invariant forall b, k, m, s :: ACCEPT_ACK(b, k, m, s) in ios ==> s in ps
        invariant forall b, c, log, s :: NEW_LEADER_ACK(b, c, log, s) in ios ==> s in ps

        invariant forall p, m :: p in ps && m in new_state_acks[p] ==> m in ios
        invariant forall p, m :: p in ps && m in new_state_acks[p] ==> m.NEW_STATE_ACK?
        invariant forall p, m :: p in ps && m in new_state_acks[p] ==> m == NEW_STATE_ACK(m.b, m.s)

        invariant forall p, m :: p in ps && m in new_leader_acks[p] ==> m in ios
        invariant forall p, m :: p in ps && m in new_leader_acks[p] ==> m.NEW_LEADER_ACK?
        invariant forall p, m :: p in ps && m in new_leader_acks[p] ==> m == NEW_LEADER_ACK(m.b, m.c, m.log, m.s)

        invariant forall p, k, m :: p in ps && k in accept_acks[p] && m in accept_acks[p][k] ==> m in ios
        invariant forall p, k, m :: p in ps && k in accept_acks[p] && m in accept_acks[p][k] ==> m.ACCEPT_ACK?
        invariant forall p, k, m :: p in ps && k in accept_acks[p] && m in accept_acks[p][k] ==> m == ACCEPT_ACK(m.b, m.k, m.m, m.s)

        invariant forall p :: p in ps ==> bal[p] >= cbal[p] >= -1
        invariant forall p :: p in ps && st[p] in {L, F, S} ==> bal[p] == cbal[p]

        invariant forall b, k, m, p :: p in ps && ACCEPT_ACK(b, k, m, p) in ios ==> cbal[p] >= b
        invariant forall b, c, m, p :: p in ps && NEW_LEADER_ACK(b, c, m, p) in ios ==> bal[p] >= b
        invariant forall b, k, m, b', c', m', p :: p in ps && ACCEPT_ACK(b, k, m, p) in ios && NEW_LEADER_ACK(b', c', m', p) in ios && b' > b ==> c' >= b

        invariant forall A, b, k, m :: choosable(A, b, k, m, ps, bal, ios) ==> choosable(A, b, k, m, ps, bal', ios')

    {
        bal' := bal; ios' := ios;

        var p :| p in ps;
        var recover :| recover in {false, true};

        if (recover || ios == {}) {
            var b := new_bal(bal[p], p, N);
            ios := ios + {NEW_LEADER(b)};
        } else {
            var bcast :| bcast in {false, true};

            if (st[p] == L && bcast) {
                var m: int := *;
                next := next[p := next[p] + 1];
                log := log[p := log[p][next[p] := m]];
                ios := ios + {ACCEPT(bal[p], next[p], m)};
            } else {
                var msg :| msg in ios;

                if (msg.ACCEPT? && st[p] in {L, F} && msg.b == bal[p]) {
                    log := log[p := log[p][msg.k := msg.m]];
                    ios := ios + {ACCEPT_ACK(msg.b, msg.k, msg.m, p)};
                }

                if (msg.ACCEPT_ACK? && st[p] == L && msg.b == bal[p]) {
                    if (msg.k !in accept_acks[p]) {
                        accept_acks := accept_acks[p := accept_acks[p][msg.k := {}]];
                    }
                    accept_acks := accept_acks[p := accept_acks[p][msg.k := accept_acks[p][msg.k] + {msg}]];
                    var A' := set m | m in accept_acks[p][msg.k] :: m.s;
                    if (2 * |A'| > N) {
                        ios := ios + {COMMIT(msg.b, msg.k, msg.m)};
                    }
                }

                if (msg.COMMIT? && st[p] in {L, F} && bal[p] >= msg.b && last_delivered[p] < msg.k) {
                    last_delivered := last_delivered[p := msg.k];
                    log := log[p := log[p][msg.k := msg.m]];
                    dlog := dlog[p := dlog[p] + [(msg.b, msg.m)]];
                }

                if (msg.NEW_LEADER? && msg.b > bal[p]) {
                    st := st[p := R];
                    bal := bal[p := msg.b];
                    ios := ios + {NEW_LEADER_ACK(bal[p], cbal[p], log[p], p)};
                }

                if (msg.NEW_LEADER_ACK? && st[p] == R && msg.b == bal[p]) {
                    new_leader_acks := new_leader_acks[p := new_leader_acks[p] + {msg}];
                    var A' := set m | m in new_leader_acks[p] :: m.s;
                    if (2 * |A'| > N) {
                        var m := pick_with_max_cbal_and_len(new_leader_acks[p]);
                        var k := max(m.log.Keys);
                        cbal := cbal[p := bal[p]];
                        log := log[p := m.log];
                        next := next[p := k];
                        st := st[p := S];
                        new_state_acks := new_state_acks[p := {}];
                        ios := ios + {NEW_STATE(bal[p], log[p])};
                    }
                }

                if (msg.NEW_STATE? && msg.b >= bal[p]) {
                    bal := bal[p := msg.b];
                    cbal := cbal[p := msg.b];
                    log := log[p := msg.log];
                    st := st[p := F];
                    ios := ios + {NEW_STATE_ACK(msg.b, p)};
                }

                if (msg.NEW_STATE_ACK? && st[p] == S && bal[p] == msg.b) {
                    new_state_acks := new_state_acks[p := new_state_acks[p] + {msg}];
                    var A' := (set m | m in new_state_acks[p] :: m.s) + {p};
                    if (2 * |A'| > N) {
                        st := st[p := L];
                        ios := ios + (set k | k in log[p] :: COMMIT(bal[p], k, log[p][k]));
                    }
                }
            }
        }

    }
}
