--------------------------- MODULE TrafficLight ---------------------------
(*
 * Traffic Light State Machine
 *
 * Models a traffic light cycling: Red → Green → Yellow → Red
 *
 * Safety property: Never transitions directly from Red to Yellow
 *
 * Run with: tlc -workers auto -config TrafficLight.cfg TrafficLight.tla
 *)

VARIABLE
    light,          \* Current light state
    prevLight       \* Previous light state (for transition checking)

vars == <<light, prevLight>>

States == {"Red", "Green", "Yellow"}

TypeOK ==
    /\ light \in States
    /\ prevLight \in States

Init ==
    /\ light = "Red"
    /\ prevLight = "Red"

RedToGreen ==
    /\ light = "Red"
    /\ prevLight' = light
    /\ light' = "Green"

GreenToYellow ==
    /\ light = "Green"
    /\ prevLight' = light
    /\ light' = "Yellow"

YellowToRed ==
    /\ light = "Yellow"
    /\ prevLight' = light
    /\ light' = "Red"

Next == RedToGreen \/ GreenToYellow \/ YellowToRed

Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* PROPERTIES *)

\* Safety: Never transition directly from Red to Yellow
NeverRedToYellow == ~(prevLight = "Red" /\ light = "Yellow")

\* Liveness: The light eventually changes
EventuallyCycles == []<>(light = "Green")

=============================================================================
