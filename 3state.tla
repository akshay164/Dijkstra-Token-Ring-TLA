-------------------- MODULE 3state -------------------
EXTENDS Integers, FiniteSets
CONSTANT N
ASSUME N \in Nat \ {0}
Procs == 1..N-1


(* Dijkstra's stabilizing 3 state token ring with processes
--algorithm 3StateTokenRing {
  variable c = [k \in 0..N |-> IF k=0 THEN 1 ELSE 0]; 
  

   fair process (j \in Procs)
   
    { J0: while (TRUE)
        {either
            { await (c[self]+1) % 3 = c[(self-1)];
                 c[self] := c [(self-1)];
               }
         or
         { await (c[self]+1) % 3 = c[(self+1)];
               c[self] := c[(self+1)]
             }
         }
    }
   fair process (i \in {0})
    { I0: while (TRUE)
           { await ((c[self]+1) % 3 = c[1]);
             c[self] := (c[1]+1) % 3;
           }
    }
    fair process (k \in {N})
    
    { N0: while (TRUE)
        
            { await c[(self-1)] = c[0] /\ c[self] /= (c[(N-1)]+1) % 3;
              c[self] := (c[(self-1)]+1) % 3;
            }
    }
}
 ****************************************************************)

\* BEGIN TRANSLATION
VARIABLE c

vars == << c >>

ProcSet == (Procs) \cup ({0}) \cup ({N})

Init == (* Global variables *)
        /\ c = [k \in 0..N |-> IF k=0 THEN 1 ELSE 0]

j(self) == \/ /\ (c[self]+1) % 3 = c[(self-1)]
              /\ c' = [c EXCEPT ![self] = c [(self-1)]]
           \/ /\ (c[self]+1) % 3 = c[(self+1)]
              /\ c' = [c EXCEPT ![self] = c[(self+1)]]

i(self) == /\ ((c[self]+1) % 3 = c[1])
           /\ c' = [c EXCEPT ![self] = (c[1]+1) % 3]

k(self) == /\ c[(self-1)] = c[0] /\ c[self] /= (c[(N-1)]+1) % 3
           /\ c' = [c EXCEPT ![self] = (c[(self-1)]+1) % 3]

Next == (\E self \in Procs: j(self))
           \/ (\E self \in {0}: i(self))
           \/ (\E self \in {N}: k(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(j(self))
        /\ \A self \in {0} : WF_vars(i(self))
        /\ \A self \in {N} : WF_vars(k(self))

\* END TRANSLATION

Tokens == Cardinality({x \in Procs: (c[x]+1) % 3 = c[(x-1)] \/ (c[x]+1) % 3 = c[(x+1)]})
          + IF ((c[0]+1) % 3 = c[1]) THEN 1 ELSE 0
          + IF c[(N-1)] = c[0] /\ c[N] /= (c[(N-1)]+1) % 3 THEN 1 ELSE 0
InvProp == Tokens = 1
Stabilization == <> InvProp
LowerBound == Tokens >= 1
NotIncrease == [][Tokens'<=Tokens]_vars
Decrease == \A m \in 1..N+1: [] <> (Tokens <= m)
TypeOK == \A x \in 0..N: c[x] < 3

==================================================================

Dijkstra's stabilizing 3 State token ring algorithm.
Made by 
Akshay Kumar - 50169103
Rohin Mittal - 50168799

