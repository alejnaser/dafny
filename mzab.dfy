datatype St  = L | F | R

datatype Msg = ACCEPT(b: int, k: int, m: int, s: int) |
               ACCEPT_ACK(b: int, k: int, ghost gm: int, s: int, d: int) |
               COMMIT(b: int, k: int, m: int, s: int) |
               NEW_LEADER(b: int, c: int, l: int, s: int) |
               NEW_LEADER_ACK(b: int, ghost gc: int, ghost gl: int, s: int, d: int) |
               NEW_STATE(b: int, msg: map<int, int>, s: int) |
               NEW_STATE_ACK(b: int, ghost gmsg: map<int, int>, s: int, d: int)

lemma in_range(Q: set<int>, N: int)
    requires forall p :: p in Q ==> 0 <= p < N
    requires N  >= 0
    ensures |Q| <= N
    decreases N
{
    if (N == 0) {
        forall p | p in Q
            ensures false
        {}
        assert Q == {};
    } else if N - 1 in Q {
        in_range(Q - {N - 1}, N - 1);
    } else {
        in_range(Q, N - 1);
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

method new_bal(b: int, p: int, N: int) returns (b': int)
    requires N > 0
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

class MZab
{
    const N:       int;
    const ps:      set<int>;
    ghost var net: set<Msg>;

    var st:   map<int, St>;
    var msg:  map<int, map<int, int>>;
    var bal:  map<int, int>;
    var cbal: map<int, int>;
    var next: map<int, int>;
    var ld:   map<int, int>;
    var dmsg: map<int, seq<(int, int)>>;

    lemma quorums_intersect()
        requires Invariant()
        ensures forall Q, Q' :: is_quorum(Q) && is_quorum(Q') ==> Q * Q' != {}
    {
        forall Q, Q' | is_quorum(Q) && is_quorum(Q')
            ensures Q * Q' != {}
        {
            if Q * Q' == {} {
                in_range(Q + Q', N);
                assert false;
            }
        }
    }

    predicate Invariant()
        reads this
    {
        && (N > 0)
        && (N == |ps|)
        && (forall p :: p in ps ==> 0 <= p < N)
        && (st.Keys == msg.Keys == bal.Keys == cbal.Keys == next.Keys == ld.Keys == dmsg.Keys == ps)

        // all sources and destinations are valid processes
        && (forall b, k, m, s :: ACCEPT(b, k, m, s) in net ==> s in ps)
        && (forall b, k, m, s :: COMMIT(b, k, m, s) in net ==> s in ps)
        && (forall b, msg, s :: NEW_STATE(b, msg, s) in net ==> s in ps)
        && (forall b, c, l, s :: NEW_LEADER(b, c, l, s) in net ==> s in ps)
        && (forall b, k, m, s, d :: ACCEPT_ACK(b, k, m, s, d) in net ==> s in ps && d in ps)
        && (forall b, msg, s, d :: NEW_STATE_ACK(b, msg, s, d) in net ==> s in ps && d in ps)
        && (forall b, c, l, s, d :: NEW_LEADER_ACK(b, c, l, s, d) in net ==> s in ps && d in ps)

        // if process p is a leader, then it owns its ballot
        && (forall p :: p in ps && st[p] == L ==> bal[p] % N == p)

        // only leader(b) can send an ACCEPT, COMMIT or NEW_LEADER
        // message for ballot b
        && (forall b, k, m, s :: ACCEPT(b, k, m, s) in net ==> b % N == s)
        && (forall b, k, m, s :: COMMIT(b, k, m, s) in net ==> b % N == s)
        && (forall b, msg, s :: NEW_STATE(b, msg, s) in net ==> b % N == s)
        && (forall b, c, l, s :: NEW_LEADER(b, c, l, s) in net ==> b % N == s)

        // only leader(b) can receive an ACCEPT_ACK, NEW_STATE_ACK or NEW_LEADER_ACK
        // message for ballot b
        && (forall b, k, m, s, d :: ACCEPT_ACK(b, k, m, s, d) in net ==> b % N == d)
        && (forall b, msg, s, d :: NEW_STATE_ACK(b, msg, s, d) in net ==> b % N == d)
        && (forall b, c, l, s, d :: NEW_LEADER_ACK(b, c, l, s, d) in net ==> b % N == d)

        // relation between messages
        && (forall b, k, m, s, d :: ACCEPT_ACK(b, k, m, s, d) in net ==> ACCEPT(b, k, m, d) in net)
        && (forall b, msg, s, d :: NEW_STATE_ACK(b, msg, s, d) in net ==> NEW_STATE(b, msg, d) in net)
        && (forall b, c, l, s, d :: NEW_LEADER_ACK(b, c, l, s, d) in net ==> NEW_LEADER(b, c, l, d) in net)

        && (forall p :: p in ps ==> bal[p] >= cbal[p]) // inv 1
        && (forall p :: p in ps && st[p] == R ==> bal[p] > cbal[p]) // inv 2
        && (forall p :: p in ps && st[p] in {L, F} ==> bal[p] == cbal[p]) // inv 3
        && (forall b, c, l, s, d :: NEW_LEADER_ACK(b, c, l, s, d) in net ==> bal[s] >= b) // inv 4
        && (forall b, k, m, s, d :: ACCEPT_ACK(b, k, m, s, d) in net ==> cbal[s] >= b) // inv 5
        && (forall b, msg, s, d :: NEW_STATE_ACK(b, msg, s, d) in net ==> cbal[s] >= b) // inv 6
        && (forall b, msg, s :: NEW_STATE(b, msg, s) in net ==> cbal[s] >= b) // inv 7
        && (forall b, k, m, s, b', c', l', s', s'' :: NEW_LEADER_ACK(b', c', l', s, s'') in net
            && ACCEPT_ACK(b, k, m, s, s') in net && b' > b ==> c' >= b) // inv 8
        && (forall b, m, b', c', l', s, s', s'' :: NEW_LEADER_ACK(b', c', l', s, s'') in net
            && NEW_STATE_ACK(b, m, s, s') in net && b' > b ==> c' >= b) // inv 9
        && (forall b, msg, s, b', c', l', s' :: NEW_LEADER_ACK(b', c', l', s, s') in net
            && NEW_STATE(b, msg, s) in net && b' > b ==> c' >= b) // inv 10
    }

    predicate is_quorum(Q: set<int>)
        requires Invariant()
        reads this
    {
        Q <= ps && N < 2 * |Q|
    }

    predicate acceptable(b: int, k: int, m: int, Q: set<int>)
        requires Invariant()
        requires is_quorum(Q)
        reads this
    {
        forall q :: q in Q ==> ACCEPT_ACK(b, k, m, q, b % N) in net || bal[q] <= b
    }

    predicate recoverable(b: int, k: int, m: int, Q: set<int>, msg: map<int, int>)
        requires Invariant()
        requires is_quorum(Q)
        requires k in msg && msg[k] == m
        reads this
    {
        forall q :: q in Q ==> NEW_STATE_ACK(b, msg, q, b % N) in net || NEW_STATE(b, msg, q) in net || bal[q] <= b
    }

    predicate commitable(b: int, k: int, m: int)
        requires Invariant()
        reads this
    {
        (exists Q :: is_quorum(Q) && acceptable(b, k, m, Q)) ||
        (exists Q, msg :: is_quorum(Q) && k in msg && msg[k] == m && recoverable(b, k, m, Q, msg))
    }

    constructor(ps: set<int>)
        requires ps != {}
        requires forall p :: p in ps ==> 0 <= p < |ps|
        ensures Invariant()
    {
        N       := |ps|;
        net     := {};
        this.ps := ps;

        st   := map p | p in ps :: F;
        msg  := map p | p in ps :: map[];
        bal  := map p | p in ps ::  0;
        cbal := map p | p in ps ::  0;
        next := map p | p in ps :: -1;
        ld   := map p | p in ps :: -1;
        dmsg := map p | p in ps :: [];
    }

    method broadcast(p: int, m: int)
        requires Invariant() && p in ps
        requires st[p] == L

        modifies this
        ensures Invariant()
    {
        next := next[p := next[p] + 1];
        msg  := msg[p := msg[p][next[p] := m]];
        net  := net + {ACCEPT(bal[p], next[p], m, p)};
    }

    method accept(p: int, b: int, k: int, m: int, s: int)
        requires Invariant() && p in ps && ACCEPT(b, k, m, s) in net
        requires st[p] in {L, F} && bal[p] == b

        modifies this
        ensures Invariant()
    {
        msg := msg[p := msg[p][k := m]];
        net := net + {ACCEPT_ACK(b, k, m, p, s)};
    }

    method quorum_of_accept_ack(p: int, b: int, k: int, m: int, Q: set<int>)
        requires Invariant() && p in ps && is_quorum(Q) &&
            (forall q :: q in Q ==> ACCEPT_ACK(b, k, m, q, p) in net)
        requires st[p] == L && bal[p] == b

        modifies this
        ensures Invariant()
    {
        var q :| q in Q; // needed to instantiate a quantifier
        net   := net + {COMMIT(b, k, m, p)}; // TODO: msg[p][k] = m
    }

    method commit(p: int, b: int, k: int, m: int, s: int)
        requires Invariant() && p in ps && COMMIT(b, k, m, s) in net
        requires st[p] in {L, F} && bal[p] == b && ld[p] == k - 1

        modifies this
        ensures Invariant()
    {
        ld   := ld[p := k];
        msg  := msg[p := msg[p][k := m]];
        dmsg := dmsg[p := dmsg[p] + [(b, m)]];
    }

    method recover(p: int)
        requires Invariant() && p in ps

        modifies this
        ensures Invariant()
        decreases *
    {
        var b       := new_bal(bal[p], p, N);
        var msg_len := max(msg[p].Keys);
        net         := net + {NEW_LEADER(b, cbal[p], msg_len, p)};
    }

    method new_leader(p: int, b: int, c: int, l: int, s: int)
        requires Invariant() && p in ps && NEW_LEADER(b, c, l, s) in net
        requires bal[p] < b

        modifies this
        ensures Invariant()
        decreases *
    {
        var msg_len := max(msg[p].Keys);
        if c > cbal[p] || (c == cbal[p] && l >= msg_len) {
            st  := st[p := R];
            bal := bal[p := b];
            net := net + {NEW_LEADER_ACK(b, c, l, p, s)};
        } else {
            var b := new_bal(bal[p], p, N);
            net := net + {NEW_LEADER(b, cbal[p], msg_len, p)};
        }
    }

    method quorum_of_new_leader_ack(p: int, b: int, c: int, l: int, Q: set<int>)
        requires Invariant() && p in ps && is_quorum(Q) &&
            (forall q :: q in Q ==> NEW_LEADER_ACK(b, c, l, q, p) in net)
        requires st[p] == R && bal[p] == b

        modifies this
        ensures Invariant()
    {
        var k := max(msg[p].Keys);
        cbal  := cbal[p := b];
        st    := st[p := L];
        next  := next[p := k];
        net   := net + {NEW_STATE(b, msg[p], p)};
    }

    method new_state(p: int, b: int, msg': map<int, int>, s: int)
        requires Invariant() && p in ps && NEW_STATE(b, msg', s) in net
        requires bal[p] < b || (bal[p] == b && st[p] == R)

        modifies this
        ensures Invariant()
    {
        bal  := bal[p := b];
        cbal := cbal[p := b];
        msg  := msg[p := msg'];
        st   := st[p := F];
        net  := net + {NEW_STATE_ACK(b, msg', p, s)};
    }

    method quorum_of_new_state_ack(p: int, b: int, m: map<int, int>, Q: set<int>)
        requires Invariant() && p in ps && is_quorum(Q) &&
            (forall q :: q in Q ==> NEW_STATE_ACK(b, m, q, p) in net || q == p)
        requires st[p] == L && bal[p] == b

        modifies this
        ensures Invariant()
    {
        net := net + (set k | k in msg[p] :: COMMIT(b, k, msg[p][k], p));
    }
}
