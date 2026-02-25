#lang racket
(require "qsim-compiler.rkt" racket/cmdline)

(define working-directory (make-parameter (current-directory)))
(define (create-if-not-exist dir)
  (unless (directory-exists? dir)
    (make-directory* dir)))

(define (create-case-dir tag name)
  (create-if-not-exist (build-path (working-directory) (symbol->string tag) (symbol->string name))))

(define (gen-iso-case tag gen-spec f in-size out-size)
  (to-iso (gen-spec f in-size out-size) (build-path (working-directory) (format "~a-~a-~a.iso" tag in-size out-size))))

(define (gen-qiskit-case tag gen-spec f in-size out-size)
  (to-qiskit (gen-spec f in-size out-size) (build-path (working-directory) (format "~a-~a-~a.py" tag in-size out-size))))

(define (gen-qasm-case tag gen-spec f in-size out-size)
  (to-qasm (gen-spec f in-size out-size)
           (path->string
            (build-path (working-directory) (format "~a-~a-~a" tag in-size out-size)))))

(define (gen-cirq-case tag gen-spec f in-size out-size)
  (to-cirq (gen-spec f in-size out-size) (build-path (working-directory) (format "~a-~a-~a.py" tag in-size out-size))))

(define supported-simulators
  (make-parameter
   `((iso    . ,gen-iso-case)
     (qiskit . ,gen-qiskit-case)
     (qtorch . ,gen-qasm-case)
     (qsim   . ,gen-cirq-case))))

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


;;; Simplified Deutsch Jozsa, constant 0
(define (simplified-deutsch-jozsa-to-zero f in-size out-size)
  (let* ((n (add1 in-size))
         (circ (to-gate (deutsch n)
                 (para hadamard n)
                 (para hadamard in-size))))
    (list circ (list circ 1))))

;;; Simplified Deutsch Jozsa, balanced
(define (simplified-deutsch-jozsa-is-even f in-size out-size)
  (let* ((n (add1 in-size))
         (circ (to-gate (deutsch n)
                 (para hadamard n)
                 (para cx (range (- n 2) n))
                 (para hadamard in-size))))
    (list circ (list circ 1))))

;;; Deutsch Jozsa, balanced, ISO
(define (iso-deutsch-jozsa-is-even f in-size out-size)
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

;;; Deutsch Jozsa, balanced, Qiskit
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
                 (para hadamard in-size))))
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
(define (gen-one-benchmark case-generator algo-name simulator spec oracle f-out-size qubits)
  (parameterize ((working-directory (build-path (working-directory)
                                                (symbol->string algo-name)
                                                (symbol->string simulator))))
    (map (λ (in-size)
           (case-generator algo-name spec (oracle in-size) in-size (f-out-size in-size)))
         qubits)))

(define (gen-benchmarks algo-name specs oracle out-size qubits)
  (define all-specs
    (cond
      ((list? specs) specs)
      ((procedure? specs) (make-list (length (supported-simulators)) specs))
      (else (error 'gen-benchmarks "Invalid case spec: must be a list of procedures or one procedure."))))

  (for-each
   (λ (gen spec simulator)
     (create-case-dir algo-name simulator)
     (gen-one-benchmark gen algo-name simulator spec oracle out-size qubits))
   (map cdr (supported-simulators))
   all-specs
   (map car (supported-simulators))))

(define (gen-had-case tag)
  (define algo-name tag)
  (define spec had-to-last-spec)
  (define oracle identity)
  (define out-size identity)
  (define qubits (range 1 20))
  (gen-benchmarks algo-name spec oracle out-size qubits))

(define (gen-dj-case tag specs oracle^)
  (define algo-name tag)
  (define spec specs)
  (define oracle (λ (_) oracle^))
  (define out-size (λ (_) 1))
  (define qubits (range 1 20))
  (gen-benchmarks algo-name spec oracle out-size qubits))

(define (gen-simon-case tag)
  (define algo-name tag)
  (define spec simon-spec)
  (define oracle (λ (in-size) (simon-f in-size (sub1 (expt 2 in-size)))))
  (define out-size identity)
  (define qubits (range 1 5))
  (gen-benchmarks algo-name spec oracle out-size qubits))

(define (gen-cases)
  (gen-had-case 'had-last-qubit)
  (gen-dj-case 'deutsch-jozsa-to-zero simplified-deutsch-jozsa-to-zero to-zero)
  (gen-dj-case 'deutsch-jozsa-is-even
               (list iso-deutsch-jozsa-is-even qiskit-deutsch-jozsa-is-even
                     simplified-deutsch-jozsa-to-zero
                     simplified-deutsch-jozsa-to-zero)
               is-even)
  (gen-dj-case 'deutsch-jozsa-is-even-simplified simplified-deutsch-jozsa-is-even is-even)
  (parameterize [(supported-simulators `((iso    . ,gen-iso-case)
                                         (qiskit . ,gen-qiskit-case)))]
    (gen-simon-case 'simon)))

(command-line
 #:program "cases"
 #:once-each
 [("-d" "--dest") dest "Target directory" (working-directory dest)]
 #:args ()
 (gen-cases))
