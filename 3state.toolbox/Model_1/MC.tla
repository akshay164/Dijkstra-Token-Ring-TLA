---- MODULE MC ----
EXTENDS 3state, TLC

\* CONSTANT definitions @modelParameterConstants:0N
const_144989641206466000 == 
6
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_144989641207467000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_144989641208568000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_144989641209669000 ==
LowerBound
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_144989641210770000 ==
InvProp
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_144989641211771000 ==
Stabilization
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_144989641212872000 ==
NotIncrease
----
\* PROPERTY definition @modelCorrectnessProperties:2
prop_144989641213973000 ==
Decrease
----
=============================================================================
\* Modification History
\* Created Sat Dec 12 00:00:12 EST 2015 by akshaykumar
