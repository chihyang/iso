#lang racket
(require "qsim-compiler.rkt" racket/cmdline)

(define working-directory (make-parameter (current-directory)))
(define (create-if-not-exist dir)
  (unless (directory-exists? dir)
    (make-directory* dir)))
(define (create-case-dir tag)
  (create-if-not-exist (build-path (working-directory) (symbol->string tag) "iso"))
  (create-if-not-exist (build-path (working-directory) (symbol->string tag) "python")))

(define (gen-iso-case tag gen-spec f in-size out-size)
  (to-iso (gen-spec f in-size out-size) (build-path (working-directory) (format "~a-~a-~a.iso" tag in-size out-size))))

(define (gen-qiskit-case tag gen-spec f in-size out-size)
  (to-qiskit (gen-spec f in-size out-size) (build-path (working-directory) (format "~a-~a-~a.py" tag in-size out-size))))

;;; Oracles
(define (not n)
  (if (eq? n 0) 1 0))

(define (to-zero n) 0)

(define (to-one n) 1)

(define (is-even n)
  (if (even? n) 0 1))

(define (simon-f size c)
  (λ (n)
    (min n (bitwise-xor n c))))

;;; Hadamard to the last qubit
(define (had-to-last-spec f in-size out-size)
  (let ((circ (to-gate (had-to-last in-size)
                (para hadamard (range (sub1 in-size) in-size)))))
    (list circ (list circ in-size))))

;;; General Deutsch-Jozsa
(define (deutsch-jozsa-spec f in-size out-size)
  (let* ((n (+ in-size out-size))
         (uf (to-unitary uf in-size out-size f))
         (circ (to-gate (deutch n)
                 (para hadamard n)
                 (uf (range 0 n))
                 (para hadamard in-size))))
    (list uf circ (list circ (sub1 (expt 2 out-size))))))


;;; Simplified Deutsch Jozsa, constant 0, ISO
(define (simplified-deutsch-jozsa-to-zero f in-size out-size)
  (let* ((n (add1 in-size))
         (circ (to-gate (deutsch n)
                 (para hadamard n)
                 (para hadamard in-size))))
    (list circ (list circ 1))))

;;; Simplified Deutsch Jozsa, constant 0, Qiskit
(define (qiskit-deutsch-jozsa-to-zero f in-size out-size)
  (let* ((n (add1 in-size))
         (circ (to-gate (deutsch n)
                 (para hadamard n)
                 (para hadamard (range 1 n)))))
    (list circ (list circ 1))))

;;; Simplified Deutsch Jozsa, balanced, ISO
(define (simplified-deutsch-jozsa-is-even f in-size out-size)
  (let* ((n (add1 in-size))
         (uf (let* ((bvars (map (λ (id) (format "a~a" id))
                                (range 0 (sub1 in-size))))
                    (lvar (format "a~a" in-size))
                    (fvars (append bvars `(#f ,lvar)))
                    (tvars (append bvars `(#t ,lvar))))
               (scircuit 'uf n `((,tvars ,tvars)
                                 (,fvars (let ((,lvar (neg ,lvar)))
                                           ,(append bvars `(#f ,lvar))))))))
         (circ (to-gate (deutsch n)
                 (para hadamard n)
                 (uf (range 0 n))
                 (para hadamard in-size))))
    (list uf circ (list circ 1))))

;;; Simplified Deutsch Jozsa, balanced, Qiskit
(define (qiskit-deutsch-jozsa-is-even f in-size out-size)
  (let* ((n (add1 in-size))
         (uf (let* ((bvars (map (λ (id) (format "a~a" id))
                                (range 0 (sub1 in-size))))
                    (lvar (format "a~a" in-size))
                    (fvars (append bvars `(#f ,lvar)))
                    (tvars (append bvars `(#t ,lvar)))
                    (sn-1 (/ (expt 2 n) 4)))
               (qcircuit 'uf n
                 (format
                  "np.kron(np.eye(~a), np.array([[1,0,0,0],[0,1,0,0],[0,0,0,1],[0,0,1,0]]))"
                  sn-1))))
         (circ (to-gate (deutsch n)
                 (para hadamard n)
                 (uf (range 0 n))
                 (para hadamard (range 1 n)))))
    (list uf circ (list circ 1))))

;;; General Simon
(define (simon-spec f in-size out-size)
  (let* ((n (+ in-size out-size))
         (uf (to-unitary uf in-size out-size f))
         (circ (to-gate (simon n)
                 (para hadamard in-size)
                 (uf (range 0 n))
                 (para hadamard in-size))))
    (list uf circ (list circ (sub1 (expt 2 out-size))))))

;;; Generate cases
(define (gen-had-case tag)
  (create-case-dir tag)
  (parameterize ((working-directory (build-path (working-directory) (symbol->string tag) "iso")))
    (map (λ (in-size)
           (gen-iso-case tag had-to-last-spec identity in-size in-size))
         (range 1 41)))
  (parameterize ((working-directory (build-path (working-directory) (symbol->string tag) "python")))
    (map (λ (in-size)
           (gen-qiskit-case tag had-to-last-spec identity in-size in-size))
         (range 1 41))))

(define (gen-dj-case tag spec-iso spec-qiskit oracle)
  (create-case-dir tag)
  (parameterize ((working-directory (build-path (working-directory) (symbol->string tag) "iso")))
    (map (λ (in-size)
           (gen-iso-case tag spec-iso oracle in-size 1))
         (range 1 20)))
  (parameterize ((working-directory (build-path (working-directory) (symbol->string tag) "python")))
    (map (λ (in-size)
           (gen-qiskit-case tag spec-qiskit oracle in-size 1))
         (range 1 20))))

(define (gen-simon-case tag)
  (create-case-dir tag)
  (parameterize ((working-directory (build-path (working-directory) (symbol->string tag) "iso")))
    (map (λ (in-size)
           (gen-iso-case 'simon simon-spec (simon-f in-size (sub1 (expt 2 in-size))) in-size in-size))
         (range 1 5)))
  (parameterize ((working-directory (build-path (working-directory) (symbol->string tag) "python")))
    (map (λ (in-size)
           (gen-qiskit-case 'simon simon-spec (simon-f in-size (sub1 (expt 2 in-size))) in-size in-size))
         (range 1 5))))

(define (gen-cases)
  (gen-had-case 'had-last-qubit)
  (gen-dj-case 'deutsch-jozsa-to-zero simplified-deutsch-jozsa-to-zero qiskit-deutsch-jozsa-to-zero to-zero)
  (gen-dj-case 'deutsch-jozsa-is-even simplified-deutsch-jozsa-is-even qiskit-deutsch-jozsa-is-even is-even)
  (gen-simon-case 'simon))

(command-line
 #:program "cases"
 #:once-each
 [("-d" "--dest") dest "Target directory" (working-directory dest)]
 #:args ()
 (gen-cases))
