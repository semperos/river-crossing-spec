--------------------------- MODULE RiverCrossing ---------------------------
(***************************************************************************)
(* This specification describes a history of the universe where the rules  *)
(* of the "Fox, goose, and bag of beans" puzzle are enforced.  As taken    *)
(* from Wikipedia                                                          *)
(* (https://en.wikipedia.org/wiki/Fox,_goose_and_bag_of_beans_puzzle):     *)
(*                                                                         *)
(* `^ \begin{verse} Once upon a time a farmer went to a market and         *)
(* purchased a fox, a goose, and a bag of beans.  On his way home, the     *)
(* farmer came to the bank of a river and rented a boat.  But in crossing  *)
(* the river by boat, the farmer could carry only himself and a single one *)
(* of his purchases: the fox, the goose, or the bag of beans.              *)
(*                                                                         *)
(* If left unattended together, the fox would eat the goose, or the goose  *)
(* would eat the beans.                                                    *)
(*                                                                         *)
(* The farmer's challenge was to carry himself and his purchases to the    *)
(* far bank of the river, leaving each purchase intact.  How did he do it? *)
(* \end{verse} ^'                                                          *)
(*                                                                         *)
(* This specification includes the following invariants:                   *)
(*                                                                         *)
(* `^ \begin{itemize}                                                      *)
(*                                                                         *)
(* \item \emph{TypeOK}: Type invariant that ensures the river banks are    *)
(* represented by the actors on them.                                      *)
(*                                                                         *)
(* \item \emph{NothingEatenNow}: Invariant that ensures the fox doesn't    *)
(* eat the goose and the goose doesn't eat the beans.                      *)
(*                                                                         *)
(* \item \emph{SolutionInvariant}: An invariant that we know does not      *)
(* hold.  By adding it as an invariant to a model, TLC will provide an     *)
(* error trace that provides a solution to the puzzle.                     *)
(*                                                                         *)
(* \end{itemize} ^'                                                        *)
(*                                                                         *)
(***************************************************************************)

EXTENDS TLC \* Pull in PrintT for debugging

----------

\* `^\Large{State}^'
 
(***************************************************************************)
(* The riverbanks the farmer starts from and finishes at.                  *)
(***************************************************************************)
VARIABLES riverbanka, riverbankz

(***************************************************************************)
(* All the actors in this puzzle.                                          *)
(***************************************************************************)
Actors == { "farmer", "fox", "goose", "beans" }

(***************************************************************************)
(* Riverbanks are represented by the actors on them.  The boat, though     *)
(* critical to the human perception of how the farmer transports the       *)
(* items, does not play any role in the specification itself and is        *)
(* therefore excluded.                                                     *)
(***************************************************************************)
TypeOK == /\ riverbanka \subseteq Actors
          /\ riverbankz \subseteq Actors

----------

\* `^\Large{Operations}^'

(***************************************************************************)
(* Items are only safe when the fox isn't left alone with the goose and    *)
(* the goose isn't left alone with the beans.                              *)
(***************************************************************************)
ItemsAreSafe(riverbank) == /\ riverbank /= {"fox",   "goose"}
                           /\ riverbank /= {"goose", "beans"}

(***************************************************************************)
(* Helpers to ensure things don't get eaten on either bank, either in      *)
(* current state or next (primed).                                         *)
(***************************************************************************)
NothingEatenNow  == ItemsAreSafe(riverbanka)  /\ ItemsAreSafe(riverbankz)
NothingEatenNext == ItemsAreSafe(riverbanka') /\ ItemsAreSafe(riverbankz')
NothingGetsEaten == NothingEatenNow /\ NothingEatenNext

(***************************************************************************)
(* This was useful for debugging purposes as I wrote the initial           *)
(* specification of this system.  Include as the last conjunct in an       *)
(* expression to minimize the number of things printed.                    *)
(***************************************************************************)
PrintVariables == PrintT(<<"Bank A was", riverbanka, " and is now ", riverbanka',
                           "Bank Z was", riverbankz, " and is now ", riverbankz'>>)
                            
(****************************************************************************
Move an item from one bank to the other, maintaining safety.
****************************************************************************)
MoveItem(item, start, finish) ==
    \* The farmer finds himself on riverbanka
    /\ "farmer" \in start
    \* He leaves riverbanka with himself and one `item'
    /\ start' = start \ {item, "farmer"}
    \* He immediately takes that `item' and himself to riverbankz
    /\ finish' = finish \cup {item, "farmer"}
    \* Everything survives or we don't do it
    /\ NothingGetsEaten

MoveItemAZ(item) == MoveItem(item, riverbanka, riverbankz)
MoveItemZA(item) == MoveItem(item, riverbankz, riverbanka)

(***************************************************************************)
(* Operations for moving specific items to/from riverbanka and riverbankz. *)
(***************************************************************************)
MoveFoxAZ   == MoveItemAZ("fox")
MoveFoxZA   == MoveItemZA("fox")
MoveGooseAZ == MoveItemAZ("goose")
MoveGooseZA == MoveItemZA("goose")
MoveBeansAZ == MoveItemAZ("beans")
MoveBeansZA == MoveItemZA("beans")
                      
----------
                      
\* `^\Large{Spec}^'

(***************************************************************************)
(* We begin with all items on riverbanka and nothing on riverbankz.        *)
(***************************************************************************)
Init == /\ riverbanka = Actors
        /\ riverbankz = {}
        
(***************************************************************************)
(* We can move items from one bank to the other, maintaining the safety    *)
(* invariant that nothing gets eaten.                                      *)
(***************************************************************************)
Next == \/ MoveFoxAZ
        \/ MoveFoxZA
        \/ MoveGooseAZ
        \/ MoveGooseZA
        \/ MoveBeansAZ
        \/ MoveBeansZA
        
Spec == Init /\ [][Next]_<<riverbanka,riverbankz>>

----------

(***************************************************************************)
(* See a solution to this puzzle by setting this as an invariant in the    *)
(* model.                                                                  *)
(***************************************************************************)
SolutionInvariant == riverbankz /= Actors

=============================================================================
\* Modification History
\* Last modified Wed Nov 15 16:37:49 EST 2017 by dgregoire
\* Created Tue Nov 14 15:18:30 EST 2017 by dgregoire
