-------------------------------- MODULE wire --------------------------------

EXTENDS Integers

(*--algorithm wire
    variables
        people = {"alice", "bob"},
        acc = [p \in people |-> 5],
        sender = "alice",
        receiver = "bob",
        amount = 3;

define
    NoOverdrafts == \A p \in people: acc[p] >= 0
end define;

begin
    Withdraw:
        acc[sender] := acc[sender] - amount;
    Deposit:
        acc[receiver] := acc[receiver] - amount;
end algorithm;*)


=============================================================================
\* Modification History
\* Last modified Sun Mar 24 12:36:03 ART 2019 by jrediger
\* Created Sun Mar 24 12:31:13 ART 2019 by jrediger
