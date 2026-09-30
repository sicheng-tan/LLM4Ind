; Int-valued len: supports both structural and measure schemes.
(set-logic ALL)
(declare-datatypes ((Lst 0)) (((nil) (cons (head Int) (tail Lst)))))
(declare-fun append (Lst Lst) Lst)
(declare-fun len (Lst) Int)
(assert (forall ((ys Lst)) (= (append nil ys) ys)))
(assert (forall ((x Int) (xs Lst) (ys Lst))
  (= (append (cons x xs) ys) (cons x (append xs ys)))))
(assert (= (len nil) 0))
(assert (forall ((x Int) (xs Lst)) (= (len (cons x xs)) (+ 1 (len xs)))))
; proof goal
(assert (not (forall ((xs Lst)) (= (len (append xs nil)) (len xs)))))
; proof goal end
(check-sat)
