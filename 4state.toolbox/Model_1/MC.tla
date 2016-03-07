---- MODULE MC ----
EXTENDS 4state, TLC

\* CONSTANT definitions @modelParameterConstants:0N
const_144995693682474000 == 
6
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_144995693683675000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_144995693684776000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_144995693685877000 ==
LowerBound
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_144995693686978000 ==
Stabilization
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_144995693688079000 ==
NotIncrease
----
\* PROPERTY definition @modelCorrectnessProperties:2
prop_144995693689180000 ==
Decrease
----
=============================================================================
\* Modification History
\* Created Sat Dec 12 16:48:56 EST 2015 by akshaykumar
