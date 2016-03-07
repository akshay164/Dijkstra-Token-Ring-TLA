-------------------- MODULE 4state -------------------
EXTENDS Integers, FiniteSets
CONSTANT N
ASSUME N \in Nat \ {0}
Procs == 1..N-1


(* Dijkstra's stabilizing 4 state token ring with processes
--algorithm TokenRing {
\*  variable c = [k \in 0..N |-> (k%2)], up = [k \in 0..N |-> IF k=N THEN FALSE ELSE TRUE]; 
    variable c = [k \in 0..N |-> 0], up = [k \in 0..N |-> IF k=0 THEN TRUE ELSE FALSE]; 

   fair process (j \in Procs)
   
    { J0: while (TRUE)
        {either
            { await c[self] /= c[(self-1)];
                 c[self] := c [(self-1)];
                 up[self] := TRUE;
               }
         or
         { await c[self] = c[(self+1)] /\ up[self] = TRUE /\ up[(self+1)] = FALSE;
               up[self] := FALSE;
             }
         }
    }
   fair process (i \in {0})
    { I0: while (TRUE)
           { await (c[self] = c[1] /\ up[1] = FALSE);
             c[self] := (c[self]+1) % 2;
           }
    }
    fair process (k \in {N})
    
    { N0: while (TRUE)
        \*up[self] := FALSE;                  \* It is wrong to assign 'up' value here, because what if program executes process in procs before process in N in the start
            { await c[self] /= c[(self-1)];
              c[self] := c[(self-1)];
            }
    }
}
 ****************************************************************)

\* BEGIN TRANSLATION
VARIABLES c, up

vars == << c, up >>

ProcSet == (Procs) \cup ({0}) \cup ({N})

Init == (* Global variables *)
        /\ c = [k \in 0..N |-> 0]
        /\ up = [k \in 0..N |-> IF k=0 THEN TRUE ELSE FALSE]

j(self) == \/ /\ c[self] /= c[(self-1)]
              /\ c' = [c EXCEPT ![self] = c [(self-1)]]
              /\ up' = [up EXCEPT ![self] = TRUE]
           \/ /\ c[self] = c[(self+1)] /\ up[self] = TRUE /\ up[(self+1)] = FALSE
              /\ up' = [up EXCEPT ![self] = FALSE]
              /\ c' = c

i(self) == /\ (c[self] = c[1] /\ up[1] = FALSE)
           /\ c' = [c EXCEPT ![self] = (c[self]+1) % 2]
           /\ up' = up

k(self) == /\ c[self] /= c[(self-1)]
           /\ c' = [c EXCEPT ![self] = c[(self-1)]]
           /\ up' = up

Next == (\E self \in Procs: j(self))
           \/ (\E self \in {0}: i(self))
           \/ (\E self \in {N}: k(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(j(self))
        /\ \A self \in {0} : WF_vars(i(self))
        /\ \A self \in {N} : WF_vars(k(self))

\* END TRANSLATION

Tokens == Cardinality({x \in Procs: c[x] /= c[(x-1)] \/ (c[x] = c[(x+1)] /\ up[x] = TRUE /\ up[(x+1)] = FALSE)})
          + IF (c[0] = c[1]) /\ up[1] = FALSE THEN 1 ELSE 0
          + IF c[N] /= c[(N-1)] THEN 1 ELSE 0
InvProp == Tokens = 1
Stabilization == <> InvProp
LowerBound == Tokens >= 1
NotIncrease == [][Tokens'<=Tokens]_vars
Decrease == \A m \in 1..N+1: [] <> (Tokens <= m)
TypeOK == \A x \in 0..N: c[x] < 2

==================================================================

Dijkstra's stabilizing 4 State token ring algorithm.
Made by
Akshay Kumar - 50169103
Rohin Mittal - 50168799

