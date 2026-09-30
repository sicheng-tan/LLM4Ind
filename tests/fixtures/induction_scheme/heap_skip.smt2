; Heap binder with no structural recursion definitions → skip scheme
(set-logic UFDT)
(declare-datatypes ((Nat 0) (Heap 0))
  (((Z) (S (proj1-S Nat)))
   ((hleaf) (heap (rk Nat) (value Nat) (left Heap) (right Heap)))))
(declare-fun hsize (Heap) Nat)
(declare-fun soften (Heap) Heap)
(assert (forall ((h Heap)) (= (soften h) h)))
; proof goal — Heap quantified but no structural recursion evidence
(assert (not (forall ((h Heap)) (= (hsize h) (hsize (soften h))))))
; proof goal end
(check-sat)
