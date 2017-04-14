// Three munchkin/three monster puzzle in Alloy!

// I've seen a similar problem with "cannibals and missionaries"
// but not solved anything like these with Alloy.

open util/ordering [PuzzleState]

abstract sig Entity {}
abstract sig Character extends Entity {}

one sig Boat extends Entity {}
sig Munchkin extends Character {}
sig Monster extends Character {}

sig PuzzleState { // represents a point in time
    leftOfRiver : set Entity,
    rightOfRiver : set Entity
} {
    // constraint 1 - sets must be disjoint
    // no characters can be on both sides of the river at one time
    leftOfRiver & rightOfRiver = none

    // constraint 2 - every entity must be accounted for
    Entity - (leftOfRiver+rightOfRiver) = none

    // constraint 3a - munchkins never outnumbered on LHS
    all mun:Munchkin | mun in leftOfRiver => (#(leftOfRiver & Monster) =< #(leftOfRiver & Munchkin))

    // constraint 3b - munchkins never outnumbered on RHS
    all mun:Munchkin | mun in rightOfRiver => (#(rightOfRiver & Monster) =< #(rightOfRiver & Munchkin))
}

pred init[p: PuzzleState] {
    // all characters start on the LHS in our model
    #{ mun:Munchkin | mun in p.leftOfRiver } = 3
    #{ mon:Monster | mon in p.leftOfRiver } = 3

    Boat in p.leftOfRiver // boat starts on the left too
}

pred validRightMove[p,p': PuzzleState] {
    // The boat is on the RHS afterwards, therefore RHS has has >=1 new character
    // These characters must come from the previous LHS so:
    // The difference between the intersection of all characters and those on the RHS afterwards
    // and the intersection of all characters and those on the RHS before is known as "gainedOnRight"

    // We enforce that it cannot be empty (some characters have to move), less than eq 2 characters can move (#gainedOnRight =< 2)
    // and the new left hand side (where the characters came from) must be deprived of all those characters in the new state.
    let gainedOnRight = (Character & p'.rightOfRiver) - (Character & p.rightOfRiver) |
        { gainedOnRight != none
          #gainedOnRight =< 2
          ((Character & p'.leftOfRiver)+gainedOnRight) = (Character & p.leftOfRiver) }
}

pred validLeftMove[p,p': PuzzleState] {
    // The boat is on the LHS afterwards, therefore LHS has has >=1 new character
    // These characters must come from the previous RHS
    let gainedOnLeft = (Character & p'.leftOfRiver) - (Character & p.leftOfRiver) |
        { gainedOnLeft != none
          #gainedOnLeft =< 2
          ((Character & p'.rightOfRiver)+gainedOnLeft) = (Character & p.rightOfRiver) }
}

pred validMove[p, p': PuzzleState] {
    // now the fun part! Ensuring steps are valid
    all b:Boat |
        (b in p'.leftOfRiver => (b not in p.leftOfRiver && validLeftMove[p,p'])) &&
        (b in p'.rightOfRiver => (b not in p.rightOfRiver && validRightMove[p,p']))
}

fact traces {
    init[first[]] // First state
    
    all psBefore: PuzzleState - last[] | let psAfter = next[psBefore] | validMove[psBefore, psAfter]
    let psFinal = last[] | #(psFinal.leftOfRiver) = 0 // everyone is on the right
}

// We know the optimal solution involves 11 steps from Wikipedia.
// Since we have a start state we constrain the model to 12 states in total.
run {} for 12 but exactly 6 Character, 1 Boat, 12 PuzzleState
