#!/usr/bin/chez --script
(import (chezscheme))

(define Y
  (lambda (h)
    ((lambda (x) (h (lambda a (apply (x x) a))))
     (lambda (x) (h (lambda a (apply (x x) a)))))))


(define Zero (vector 'Zero))
(define (Pair a b) (vector 'Pair a b))
(define Env (vector 'Env))
(define (SetEnv x) (vector 'SetEnv x))
(define (Defer x) (vector 'Defer x))
(define (Gate a b) (vector 'Gate a b))
(define (PLeft x) (vector 'PLeft x))
(define (PRight x) (vector 'PRight x))
(define Trace (vector 'Trace))

(define (iEval f) ; iEval :: (iExpr -> iExpr -> iExpr) -> iExpr -> iExpr -> iExpr    iExpr -> IExpr -> IExpr
  (lambda (env x)
    (case (vector-ref x 0)
      ('Zero Zero)
      ('Defer (Defer (vector-ref x 1)))
      ('Pair (Pair (f env (vector-ref x 1)) (f env (vector-ref x 2))))
      ('Gate (Gate (vector-ref x 1) (vector-ref x 2)))
      ('Env env)
      ('SetEnv (let ((y (f env (vector-ref x 1))))
                 (case (vector-ref y 0)
                   ('Pair (case (vector-ref (vector-ref y 1) 0)
                            ('Defer (f (vector-ref y 2) (vector-ref (vector-ref y 1) 1)))
                            ('Gate (case (vector-ref (vector-ref y 2) 0)
                                     ('Zero (f env (vector-ref (vector-ref y 1) 1)))
                                     (else (f env (vector-ref (vector-ref y 1) 2)))
                            ; (haskell-syntax: z -> throwError $ SetEnvError z -- This should never actually occur, because it should be caught by typecheck)
                                     ))))
                   ; (haskell-syntax: bx -> throwError $ SetEnvError bx -- This should never actually occur, because it should be caught by typecheck)
                   )))
      ('PLeft (case (vector-ref (f env (vector-ref x 1)) 0)
                ('Pair (vector-ref (f env (vector-ref x 1)) 1))
                (else Zero)))
      ('PRight (case (vector-ref (f env (vector-ref x 1)) 0)
                ('Pair (vector-ref (f env (vector-ref x 1)) 2))
                (else Zero))))))


(define (evalLoop n)
  (let ((result (eval2 n)))
  (case (vector-ref result 0)
      ((Zero) (display "aborted"))
      ((Pair) (begin
		  (printf "~A ~%" (g2s (vector-ref result 1)))
		  (case (vector-ref result 2)
		    (#(Zero) (display "done"))
		    (else (let ((inp (get-line(current-input-port))))
			    (evalLoop (Pair (s2g inp) (vector-ref result 2)))))
		     
		    )
		  ))
      (else (display "runtime error, dumped!"))
      )
  ))


(define (eval2 n)
  ((Y iEval) Zero n))



(define (g2Ints n)
  (case (vector-ref n 0)
    (Zero '())
    (Pair (cons (g2i (vector-ref n 1)) (g2Ints (vector-ref n 2))))
    (else (display "g2Ints error?"))
    ))

(define (g2i n)
  (case (vector-ref n 0)
    (Zero 0)
    (Pair (+ 1 (+ (g2i (vector-ref n 1)) (g2i (vector-ref n 2)))))
    (else (display "g2i error?"))
    ))

(define (g2s n)
  (list->string (map integer->char (g2Ints n)))
  )

(define (s2g s)
  (ints2g (map char->integer (string->list s)))
  )

(define (ints2g ss)
  (foldr (lambda (i g) (Pair (i2g i) g)) Zero ss)
  )

(define (i2g n)
  (cond ((= n 0) Zero)
      (else (Pair (i2g (- n 1)) Zero))
    )
  )

(define (foldr proc init lst)
  (if (null? lst)
      init
      (proc (car lst)
            (foldr proc init (cdr lst)))))


(define testfile
  (call-with-input-file "scheme.txt"
    (lambda (port)
      (eval (read port) ))))

(evalLoop testfile)

