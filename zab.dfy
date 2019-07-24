datatype St  = L | F | R | S
datatype Msg = BROADCAST(m: int) |
  ACCEPT(b: int, k: int, m: int) |
  ACCEPT_ACK(b: int, k: int, m: int, s: int) |
  COMMIT(b: int, k: int, m: int) |
  DELIVER(k: int, m: int, s: int) |
  NEW_LEADER(b: int) |
  NEW_LEADER_ACK(b: int, c: int, log: map<int, int>, s: int) |
  NEW_STATE(b: int, log: map<int, int>) |
  NEW_STATE_ACK(b: int, s: int)

	method pick_with_max_cbal_and_len(acks: set<Msg>) returns (m: Msg)
    requires acks != {}
    requires forall m :: m in acks ==> m.NEW_LEADER_ACK?
			ensures m in acks && m.NEW_LEADER_ACK?
			ensures forall m' :: m' in acks ==> m'.c < m.c || (m'.c == m.c && |m'.log| <= |m.log|)
	{
    m :| m in acks;
    var q', q := {m}, acks - {m};
    while (q != {})
      decreases q
      invariant q + q' == acks
      invariant m in acks && m.NEW_LEADER_ACK?
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

	method zab(ps: set<int>, N: int)
    requires N > 0 && |ps| == N
    requires forall p :: p in ps ==> 0 <= p < N
    decreases *
	{
    var st:             map<int, St>            := map p | p in ps ::     F;
    var log:            map<int, map<int, int>> := map p | p in ps :: map[];
    var bal:            map<int, int>           := map p | p in ps ::    -1;
    var cbal:           map<int, int>           := map p | p in ps ::    -1;
    var next_send:      map<int, int>           := map p | p in ps ::    -1;
    var next_recv:      map<int, int>           := map p | p in ps ::    -1;
    var last_delivered: map<int, int>           := map p | p in ps ::    -1;

    var accept_acks:     map<int, set<Msg>> := map p | p in ps :: {};
    var new_leader_acks: map<int, set<Msg>> := map p | p in ps :: {};
    var new_state_acks:  map<int, set<Msg>> := map p | p in ps :: {};

    var ios: set<Msg> := {};

    ghost var accepts:     map<int, set<Msg>>      := map p | p in ps ::    {};
    ghost var initial_msg: map<int, map<int, int>> := map p | p in ps :: map[];

    ghost var ios': set<Msg>;
    ghost var bal': map<int, int>;

    while true
      decreases *

      invariant st.Keys == log.Keys == bal.Keys == cbal.Keys == next_send.Keys ==
      next_recv.Keys == last_delivered.Keys == accept_acks.Keys ==
      new_leader_acks.Keys == new_state_acks.Keys == accepts.Keys ==
      initial_msg.Keys == ps

      invariant forall p, m :: p in ps && m in accept_acks[p] ==> m.ACCEPT_ACK?
      invariant forall p, m :: p in ps && m in new_leader_acks[p] ==> m.NEW_LEADER_ACK?
      invariant forall p, m :: p in ps && m in new_state_acks[p] ==> m.NEW_STATE_ACK?

      invariant forall p :: p in ps ==> bal[p] >= -1          
    {
      bal' := bal; ios' := ios;

      var p       :| p in ps;
      var recover :| recover in {false, true};

      if recover {
        var b := new_bal(bal[p], p, N);
        ios := ios + { NEW_LEADER(bal[p]) };
      } else {
        var bcast :| bcast in {false, true};

        if ((st[p] == L && bcast) || ios == {}) {
          next_send := next_send[p := next_send[p] + 1];
          var m: int := *;
          var tmp := log[p][next_send[p] := m];
          log := log[p := tmp];
          accept_acks := accept_acks[p := {}];
          ios := ios + { ACCEPT(bal[p], next_send[p], m) };
        } else {
          var msg :| msg in ios;

          if (msg.ACCEPT? && st[p] in {L, F} && msg.b == bal[p] && msg.k == next_recv[p]) {
            var tmp := log[p][msg.k := msg.m];
            log := log[p := tmp];
            next_recv := next_recv[p := next_recv[p] + 1];
            ios  := ios + { ACCEPT_ACK(msg.b, msg.k, msg.m, p) };
          }

          if (msg.ACCEPT_ACK? && st[p] == L && msg.b == bal[p]) {
            var tmp := accept_acks[p] + { msg };
            accept_acks := accept_acks[p := tmp];
            var A' := set m | m in accept_acks[p] :: m.s;
            if (2 * |A'| > N) {
              ios := ios + { COMMIT(msg.b, msg.k, msg.m) };
            }
          }

          if (msg.COMMIT? && st[p] in {L, F} && bal[p] >= msg.b && last_delivered[p] < msg.k) {
            last_delivered := last_delivered[p := msg.k];
            var tmp := log[p][msg.k := msg.m];
            log := log[p := tmp];
            ios := ios + { DELIVER(msg.k, msg.m, p) };
          }

          if (msg.NEW_LEADER? && msg.b > bal[p]) {
            st := st[p := R];
            bal := bal[p := msg.b];
            ios := ios + { NEW_LEADER_ACK(bal[p], cbal[p], log[p], p) };
          }

          if (msg.NEW_LEADER_ACK? && st[p] == R && msg.b == bal[p]) {
            var tmp := new_leader_acks[p] + { msg };
            new_leader_acks := new_leader_acks[p := tmp];
            var A' := set m | m in new_leader_acks[p] :: m.s;
            if (2 * |A'| > N) {
              var m := pick_with_max_cbal_and_len(new_leader_acks[p]);
              cbal := cbal[p := bal[p]];
              log := log[p := m.log];
              next_send := next_send[p := |m.log| + 1];
              st := st[p := S];
              ios := ios + { NEW_STATE(bal[p], log[p]) };
            }
          }

          if (msg.NEW_STATE? && msg.b >= bal[p]) {
            bal := bal[p := msg.b];
            cbal := cbal[p := msg.b];
            log := log[p := msg.log];
            st := st[p := F];
            ios := ios + { NEW_STATE_ACK(bal[p], p) };
          }

          if (msg.NEW_STATE_ACK? && st[p] == S && bal[p] == msg.b) {
            var tmp := new_state_acks[p] + { msg };
            var A' := (set m | m in new_state_acks[p] :: m.s) + { p };
            if (2 * |A'| > N) {
              st := st[p := L];
              ios := ios + (set k | k in log[p] :: COMMIT(bal[p], k, log[p][k]));
            }
          }
        }
      }
    }
	}
