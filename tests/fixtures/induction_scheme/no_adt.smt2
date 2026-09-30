; Pure equality, no forall-ADT induct var
(set-logic ALL)
(declare-fun a () Int)
(declare-fun b () Int)
; proof goal
(assert (not (= a b)))
; proof goal end
(check-sat)
