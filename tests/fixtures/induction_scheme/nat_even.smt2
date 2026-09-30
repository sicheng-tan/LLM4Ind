; Nat Peano structural
(set-logic UFDT)
(declare-datatypes ((nat 0)) (((zero) (s (s0 nat)))))
(declare-fun even (nat) Bool)
(assert (even zero))
(assert (forall ((n nat)) (= (even (s (s n))) (even n))))
(assert (forall ((n nat)) (not (even (s zero)))))
; proof goal — simplified; structural on n:nat
(assert (not (forall ((n nat)) (=> (even n) (even (s (s n)))))))
; proof goal end
(check-sat)
