; list structure: len (app xs nil) = len xs
(set-logic ALL)
(declare-datatypes ((Lst 0)) (((nil) (cons (head Nat) (tail Lst)))))
(declare-datatypes ((Nat 0)) (((zero) (succ (pred Nat)))))
(declare-fun append (Lst Lst) Lst)
(declare-fun len (Lst) Nat)
(assert (forall ((ys Lst)) (= (append nil ys) ys)))
(assert (forall ((x Nat) (xs Lst) (ys Lst))
  (= (append (cons x xs) ys) (cons x (append xs ys)))))
(assert (= (len nil) zero))
(assert (forall ((x Nat) (xs Lst)) (= (len (cons x xs)) (succ (len xs)))))
; proof goal
(assert (not (forall ((xs Lst)) (= (len (append xs nil)) (len xs)))))
; proof goal end
(check-sat)
