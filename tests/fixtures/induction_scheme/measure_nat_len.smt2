; Nat-valued length → measure scheme needs __scheme_nat_to_int prelude.
(set-logic ALL)
(declare-datatypes ((Nat 0)) (((Z) (S (p Nat)))))
(declare-datatypes ((Lst 0)) (((nil) (cons (head Int) (tail Lst)))))
(declare-fun len (Lst) Nat)
(declare-fun append (Lst Lst) Lst)
(assert (= (len nil) Z))
(assert (forall ((x Int) (xs Lst)) (= (len (cons x xs)) (S (len xs)))))
(assert (forall ((ys Lst)) (= (append nil ys) ys)))
(assert (forall ((x Int) (xs Lst) (ys Lst))
  (= (append (cons x xs) ys) (cons x (append xs ys)))))
; proof goal
(assert (not (forall ((xs Lst)) (= (len (append xs nil)) (len xs)))))
; proof goal end
(check-sat)
