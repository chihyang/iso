#lang racket
(require "qsim-compiler.rkt" racket/cmdline)

(define unused identity)
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

(define (gen-quimb-case tag gen-spec f in-size out-size)
  (to-quimb (gen-spec f in-size out-size) (build-path (working-directory) (format "~a-~a-~a.py" tag in-size out-size))))

(define (count-case tag gen-spec f in-size out-size)
  (count-gates (gen-spec f in-size out-size)))

(define supported-simulators
  (make-parameter
      `((iso    . ,gen-iso-case)
        (qiskit . ,gen-qiskit-case)
        (qtorch . ,gen-qasm-case)
        (qsim   . ,gen-cirq-case)
        (quimb  . ,gen-quimb-case))))

;;; Oracles
(define (not n)
  (if (eq? n 0) 1 0))

(define (to-zero n) 0)

(define (to-one n) 1)

(define (is-even n)
  (if (even? n) 1 0))

(define (simon-f c)
  (λ (n)
    (min n (bitwise-xor n c))))

;;; Hadamard to the last qubit
(define (had-to-last-spec f in-size out-size)
  (let ((circ (to-gate (had-to-last in-size)
                (para hadamard (range (sub1 in-size) in-size)))))
    (apply-gate circ in-size)))

;;; Bell state
(define (bell-cx in-size)
  (cond
    ((zero? in-size) (empty-circ))
    ((zero? (sub1 in-size)) (apply-circ hadamard 0))
    (else
     (casc
      ,(apply-circ hadamard 0)
      ,(append* (map (λ (v) (apply-circ cx v (add1 v)))
                     (range 0 (sub1 in-size))))))))

(define (bell-state-spec f in-size out-size)
  (let* ((n in-size)
         (circ (to-gate (bell-state n)
                  ,(bell-cx in-size))))
    (apply-gate circ 0)))

;;; had after a bell
(define (casc-had-first-bell-spec f in-size out-size)
  (let* ((n in-size)
         (circ (to-gate (bell-state n)
                        ,(apply-circ hadamard 0)
                        ,(bell-cx in-size))))
    (apply-gate circ 0)))

(define (casc-had-last-bell-spec f in-size out-size)
  (let* ((n in-size)
         (circ (to-gate (casc-had-last-bell n)
                 ,(apply-circ hadamard (sub1 n))
                 ,(bell-cx n))))
    (apply-gate circ 0)))

(define (parallel-repeat gate size end)
  (if (< end size)
      (empty-circ)
      (casc
       ,(parallel-repeat gate size (- end size))
       (para gate (range (- end size) end)))))

(define (para-n-ten-qubit-bell-spec f in-size out-size)
  (let* ((bell-size 10)
         (n (* bell-size in-size))
         (gate (to-gate (bell-state bell-size)
                 ,(bell-cx bell-size)))
         (circ (to-gate (para-n-ten-qubit-bell n)
                 ,(parallel-repeat gate bell-size n))))
    (apply-gate circ 0)))

;;; had increases, bell keeps the same
(define (para-n-had-last-ten-qubit-bell-spec f in-size out-size)
  (let* ((bell-size 10)
         (n (+ bell-size in-size))
         (gate (to-gate (bell-state bell-size)
                 ,(bell-cx bell-size)))
         (circ (to-gate (hlf-bell n)
                 ,(apply-circ hadamard (sub1 in-size))
                 (para gate (range in-size n)))))
    (apply-gate circ (* in-size (expt 2 bell-size)))))

;;; had increases, bell keeps the same
(define (para-n-had-last-n-bell-spec f in-size out-size)
  (let* ((n (* 2 in-size))
         (gate (to-gate (bell-state in-size)
                        ,(bell-cx in-size)))
         (circ (to-gate (hl-bell n)
                        ,(apply-circ hadamard (sub1 in-size))
                        (para gate (range in-size n)))))
    (apply-gate circ (* in-size (expt 2 in-size)))))

;;; parallel bell spec
(define (para-two-n-bell-state-spec f in-size out-size)
  (let* ((n (* 2 in-size))
         (gate (to-gate (bell-state in-size)
                        ,(bell-cx in-size)))
         (circ (to-gate (paralle-bell-state n)
                        (para gate (range 0 in-size))
                        (para gate (range in-size n)))))
    (apply-gate circ 0)))

;;; cascade bell spec
(define (casc-two-n-bell-state-spec f in-size out-size)
  (let* ((n in-size)
         (gate (to-gate (bell-state in-size)
                        ,(bell-cx in-size)))
         (circ (to-gate (paralle-bell-state n)
                        (para gate (range 0 in-size))
                        (para gate (range 0 in-size)))))
    (apply-gate circ 0)))

;;; General Deutsch-Jozsa
(define (deutsch-jozsa-spec f in-size out-size)
  (let* ((n (+ in-size out-size))
         (uf (to-permutation uf in-size out-size f))
         (circ (to-gate (deutsch n)
                 (para hadamard (range 0 n))
                 (uf (range 0 n))
                 (para hadamard (range 0 in-size)))))
    (apply-gate circ (sub1 (expt 2 out-size)))))


;;; Simplified Deutsch Jozsa, constant 0
(define (simplified-deutsch-jozsa-to-zero f in-size out-size)
  (let* ((n (add1 in-size))
         (circ (to-gate (deutsch n)
                 (para hadamard (range 0 n))
                 (para hadamard (range 0 in-size)))))
    (apply-gate circ 1)))

;;; Simplified Deutsch Jozsa, balanced
(define (simplified-deutsch-jozsa-is-even f in-size out-size)
  (let* ((n (add1 in-size))
         (circ (to-gate (deutsch n)
                 (para hadamard (range 0 n))
                 (para x (range (- n 2) (- n 1)))
                 (para cx (range (- n 2) n))
                 (para x (range (- n 2) (- n 1)))
                 (para hadamard (range 0 in-size)))))
    (apply-gate circ 1)))

;;; Deutsch Jozsa, balanced, ISO
(define (iso-deutsch-jozsa-is-even f in-size out-size)
  (let* ((n (add1 in-size))
         (uf (let* ((bvars (map (λ (id) (format "a~a" id))
                                (range 0 (sub1 in-size))))
                    (lvar (format "a~a" in-size))
                    (fvars (append bvars `(#f ,lvar)))
                    (tvars (append bvars `(#t ,lvar))))
               (scircuit 'uf n `((,tvars ,tvars)
                                 (,fvars (let ((,lvar (,x ,lvar)))
                                           ,(append bvars `(#f ,lvar))))))))
         (circ (to-gate (deutsch n)
                 (para hadamard (range 0 n))
                 (uf (range 0 n))
                 (para hadamard (range 0 in-size)))))
    (apply-gate circ 1)))

;;; Deutsch Jozsa, balanced, Qiskit
(define (qiskit-deutsch-jozsa-is-even f in-size out-size)
  (let* ((n (add1 in-size))
         (uf (let ((sn-1 (/ (expt 2 n) 4)))
               (qcircuit 'uf n
                 (format
                  "np.kron(np.eye(~a), np.array([[1,0,0,0],[0,1,0,0],[0,0,0,1],[0,0,1,0]]))"
                  sn-1))))
         (circ (to-gate (deutsch n)
                 (para hadamard (range 0 n))
                 (uf (range 0 n))
                 (para hadamard (range 0 in-size)))))
    (apply-gate circ 1)))

;;; General Simon
(define (simon-decompose-spec f in-size out-size)
  (let* ((n (+ in-size out-size))
         (uf (to-permutation uf in-size out-size f))
         (circ (to-gate (simon n)
                 (para hadamard (range 0 in-size))
                 (uf (range 0 n))
                 (para hadamard (range 0 in-size)))))
    (apply-gate circ (sub1 (expt 2 out-size)))))

(define (simon-big-matrix-spec f in-size out-size)
  (let* ((n (+ in-size out-size))
         (uf (to-unitary uf in-size out-size f))
         (circ (to-gate (simon n)
                 (para hadamard (range 0 in-size))
                 (uf (range 0 n))
                 (para hadamard (range 0 in-size)))))
    (apply-gate circ (sub1 (expt 2 out-size)))))

;;; Grover's algorithm
(define (mc-rz size)
  (casc
   (hadamard (sub1 size))
   ((mcx size) (range 0 size))
   (hadamard (sub1 size))))

(define (grover-wrap-x size w)
  (let ((v (val->bits size w)))
    (append*
     (map (λ (v id)
            (if (zero? v)
                (apply-circ x id)
                (empty-circ)))
          v (range 0 size)))))

;;; A = I - 2|w⟩⟨w|
;;; where w is the expected number
(define (grover-a size w)
  (let ((wrap-seq (grover-wrap-x size w)))
    (casc
     ,wrap-seq
     ,(mc-rz size)
     ,(reverse wrap-seq))))

;;; A = 2|s⟩⟨s| - I
;;; where s is the all fused state
(define (grover-b size)
  (casc
   (para hadamard (range 0 size))
   ,(mc-rz size)
   (para hadamard (range 0 size))))

(define (grover-iteration A B times)
  (cond
    ((zero? times) '())
    (else (casc ,A ,B ,(grover-iteration A B (sub1 times))))))

(define (grover size w)
  (let ((A (grover-a size w))
        (B (grover-b size))
        (times (floor (/ (* pi (sqrt (expt 2 size))) 4))))
    (casc
     (para hadamard (range 0 size))
     ,(grover-iteration A B times))))

;;; Here, f is supposed to be a constant function that returns the expected
;;; value from the database.
(define (grover-spec f in-size out-size)
  (let ((circ (to-gate (grover in-size)
                ,(grover in-size (f 0)))))
    (apply-gate circ 0)))

;;; Quantum Fourier Transform
(define (ctrl-rz k c-id rz-id)
  (let ((deg (/ pi (expt 2 k))))
    (casc
     ((rz deg) rz-id)
     (cx c-id rz-id)
     ((rz (- deg)) rz-id)
     (cx c-id rz-id)
     ((phase deg) c-id))))

(define (rotations head-id size)
  (append*
   (map (λ (k)
          (ctrl-rz (add1 (- k head-id)) k head-id))
        (range (add1 head-id) (+ head-id size)))))

(define (qft in-size head-id)
  (cond
    ((eqv? in-size 0) (empty-circ))
    (else
     (casc
      ,(apply-circ hadamard head-id)
      ,(rotations head-id in-size)
      ,(qft (sub1 in-size) (add1 head-id))))))

(define (qft-spec f in-size out-size)
  (let* ((circ (to-gate (qft in-size)
                 ,(qft in-size 0))))
    (apply-gate circ 0)))

;;; Decomposed MCX in an exponential way
(define (mcx-spec f in-size out-size)
  (let* ((circ (mcx in-size)))
    (apply-gate circ 0)))

;;; Parallel two circuits
(define (had-to-last-simplified-dj-to-zero-spec f in-size out-size)
  (let* ((n (* in-size 2))
         (circ (to-gate (had-to-last-dj-to-zero n)
                 (para hadamard (range (sub1 in-size) n))
                 (para hadamard (range in-size (sub1 n))))))
    (apply-gate circ in-size)))

(define (had-to-last-simplified-dj-is-even-spec f in-size out-size)
  (let* ((n (* in-size 2))
         (circ (to-gate (deutsch n)
                 (para hadamard (range (sub1 in-size) n))
                 (para x (range (- n 2) (- n 1)))
                 (para cx (range (- n 2) n))
                 (para x (range (- n 2) (- n 1)))
                 (para hadamard (range in-size n)))))
    (apply-gate circ 1)))

;;; Randomize 1-qubit symmetry
(define randomized-choices
  '(x y z rx ry rz hadamard))

(define (random-deg)
  (/ (* (random 0 360)) pi 180))

(define (random-one-gate)
  (let ((idx (random (length randomized-choices))))
    (match (list-ref randomized-choices idx)
      ('x 'x)
      ('y `(ry ,pi))
      ('z `(rz ,pi))
      ('rx `(rx ,(random-deg)))
      ('ry `(ry ,(random-deg)))
      ('rz `(rz ,(random-deg)))
      ('hadamard 'hadamard))))

(define (randomize-1 depth)
  (cond
    ((zero? depth) '())
    (else
     (cons (random-one-gate) (randomize-1 (sub1 depth))))))

(define (inv-gate gate)
  (match gate
    ('x 'x)
    (`(rx ,deg) `(rx ,(- deg)))
    (`(ry ,deg) `(ry ,(- deg)))
    (`(rz ,deg) `(rz ,(- deg)))
    ('hadamard 'hadamard)))

(define (gate->circuit gate)
  (match gate
    ('x x)
    (`(rx ,deg) (rx deg))
    (`(ry ,deg) (ry deg))
    (`(rz ,deg) (rz deg))
    ('hadamard hadamard)))

(define (symmetry-gates gates)
  (match gates
    ('() '())
    ((cons a d)
     (cons (inv-gate a) (symmetry-gates d)))))

(define (gen-one-circuit depth)
  (let ((gates (randomize-1 depth)))
    (map gate->circuit gates)))

(define (gen-one-symmetry-circuit depth)
  (let ((gates (randomize-1 depth)))
    (map gate->circuit (append* (map list gates (symmetry-gates gates))))))

;;; here out size serves as circuit depth
(define (random-symmetry-spec f in-size out-size)
  (let ((circ (to-gate (random-circ in-size)
                 (casc
                  ,(append*
                    (map (λ (i)
                           (append* (map (λ (g) (apply-circ g i)) (gen-one-symmetry-circuit out-size))))
                         (range in-size)))))))
    (apply-gate circ 0)))

;;; Random
(define (random-spec f in-size out-size)
  (let ((circ (to-gate (random-circ in-size)
                 (casc
                  ,(append*
                    (map (λ (i)
                           (append* (map (λ (g) (apply-circ g i)) (gen-one-circuit out-size))))
                         (range in-size)))))))
    (apply-gate circ 0)))

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

(define (count-one-benchmark algo-name spec oracle f-out-size qubits)
  (map (λ (in-size)
         (count-case algo-name spec (oracle in-size) in-size (f-out-size in-size)))
       qubits))

(define (count-benchmarks algo-name specs oracle out-size qubits)
  (define spec
    (cond
      ((list? specs) (cdr specs))
      ((procedure? specs) specs)
      (else (error 'gen-benchmarks "Invalid case spec: must be a list of procedures or one procedure."))))
  (let* ((out-meta (build-path (working-directory) (format "~a.csv" algo-name)))
         (port (open-output-file out-meta #:exists 'replace)))
    (fprintf port "qubit-number,gate-number")
    (newline port)
    (for-each
     (λ (v)
       (fprintf port "~a,~a" (car v) (cdr v))
       (newline port))
     (count-one-benchmark algo-name spec oracle out-size qubits))
    (close-output-port port)))

(define (gen-bell-state tag gen-benchmarks)
  (define algo-name tag)
  (define spec bell-state-spec)
  (define oracle unused)
  (define out-size unused)
  (define qubits (range 1 41))
  (gen-benchmarks algo-name spec oracle out-size qubits))

(define (gen-casc-had-first-bell tag gen-benchmarks)
  (define algo-name tag)
  (define spec casc-had-first-bell-spec)
  (define oracle unused)
  (define out-size unused)
  (define qubits (range 1 41))
  (gen-benchmarks algo-name spec oracle out-size qubits))

(define (gen-casc-had-last-bell tag gen-benchmarks)
  (define algo-name tag)
  (define spec casc-had-last-bell-spec)
  (define oracle unused)
  (define out-size unused)
  (define qubits (range 1 41))
  (gen-benchmarks algo-name spec oracle out-size qubits))

(define (gen-para-n-ten-qubit-bell tag gen-benchmarks)
  (define algo-name tag)
  (define spec para-n-ten-qubit-bell-spec)
  (define oracle unused)
  (define out-size unused)
  (define qubits (range 1 10))
  (gen-benchmarks algo-name spec oracle out-size qubits))

(define (gen-para-n-had-last-ten-qubit-bell tag gen-benchmarks)
  (define algo-name tag)
  (define spec para-n-had-last-ten-qubit-bell-spec)
  (define oracle unused)
  (define out-size unused)
  (define qubits (range 1 41))
  (gen-benchmarks algo-name spec oracle out-size qubits))

(define (gen-para-n-had-last-n-bell tag gen-benchmarks)
  (define algo-name tag)
  (define spec para-n-had-last-n-bell-spec)
  (define oracle unused)
  (define out-size unused)
  (define qubits (range 1 41))
  (gen-benchmarks algo-name spec oracle out-size qubits))

(define (gen-para-two-n-bell-state tag gen-benchmarks)
  (define algo-name tag)
  (define spec para-two-n-bell-state-spec)
  (define oracle unused)
  (define out-size unused)
  (define qubits (range 1 41))
  (gen-benchmarks algo-name spec oracle out-size qubits))

(define (gen-casc-two-n-bell-state tag gen-benchmarks)
  (define algo-name tag)
  (define spec casc-two-n-bell-state-spec)
  (define oracle unused)
  (define out-size unused)
  (define qubits (range 1 41))
  (gen-benchmarks algo-name spec oracle out-size qubits))

(define (gen-had-case tag gen-benchmarks)
  (define algo-name tag)
  (define spec had-to-last-spec)
  (define oracle unused)
  (define out-size unused)
  (define qubits (range 1 41))
  (gen-benchmarks algo-name spec oracle out-size qubits))

(define (gen-dj-case tag specs oracle^ qubits gen-benchmarks)
  (define algo-name tag)
  (define spec specs)
  (define oracle (λ (_) oracle^))
  (define out-size (λ (_) 1))
  (gen-benchmarks algo-name spec oracle out-size qubits))

(define (gen-simon-decompose-case tag qubits gen-benchmarks)
  (define algo-name tag)
  (define spec simon-decompose-spec)
  (define oracle (λ (in-size) (λ (n) ((simon-f (sub1 (expt 2 in-size))) n))))
  (define out-size identity)
  (gen-benchmarks algo-name spec oracle out-size qubits))

(define (gen-simon-big-matrix-case tag qubits gen-benchmarks)
  (define algo-name tag)
  (define spec simon-big-matrix-spec)
  (define oracle (λ (in-size) (λ (n) ((simon-f (sub1 (expt 2 in-size))) n))))
  (define out-size identity)
  (gen-benchmarks algo-name spec oracle out-size qubits))

(define (gen-grover-case w tag gen-benchmarks)
  (define algo-name tag)
  (define spec grover-spec)
  (define oracle (λ (in-size) (λ (_) w)))
  (define out-size unused)
  (define qubits (range 1 8))
  (gen-benchmarks algo-name spec oracle out-size qubits))

(define (gen-qft tag gen-benchmarks)
  (define algo-name tag)
  (define spec qft-spec)
  (define oracle unused)
  (define out-size unused)
  (define qubits (range 1 20))
  (gen-benchmarks algo-name spec oracle out-size qubits))

(define (gen-mcx tag gen-benchmarks)
  (define algo-name tag)
  (define spec mcx-spec)
  (define oracle unused)
  (define out-size unused)
  (define qubits (range 1 8))
  (gen-benchmarks algo-name spec oracle out-size qubits))

(define (gen-had-to-last-dj-to-zero tag gen-benchmarks)
  (define algo-name tag)
  (define spec had-to-last-simplified-dj-to-zero-spec)
  (define oracle unused)
  (define out-size unused)
  (define qubits (range 1 20))
  (gen-benchmarks algo-name spec oracle out-size qubits))

(define (gen-had-to-last-dj-is-even tag gen-benchmarks)
  (define algo-name tag)
  (define spec had-to-last-simplified-dj-is-even-spec)
  (define oracle unused)
  (define out-size unused)
  (define qubits (range 1 20))
  (gen-benchmarks algo-name spec oracle out-size qubits))

(define (gen-random-symmetry tag gen-benchmarks)
  (random-seed 0)
  (define algo-name tag)
  (define spec random-symmetry-spec)
  (define oracle unused)
  (define out-size (λ (in) (* in in)))
  (define qubits (range 1 10))
  (gen-benchmarks algo-name spec oracle out-size qubits))

(define (gen-random tag gen-benchmarks)
  (random-seed 0)
  (define algo-name tag)
  (define spec random-spec)
  (define oracle unused)
  (define out-size (λ (in) (* in in)))
  (define qubits (range 1 10))
  (gen-benchmarks algo-name spec oracle out-size qubits))

(define (had-last-qubit-case gen-benchmarks)
  (gen-had-case 'had-last-qubit gen-benchmarks))
(define (bell-state-case gen-benchmarks)
  (gen-bell-state 'bell-state gen-benchmarks))
(define (casc-had-first-bell-case gen-benchmarks)
  (gen-casc-had-first-bell 'casc-had-first-bell gen-benchmarks))
(define (casc-had-last-bell-case gen-benchmarks)
  (gen-casc-had-last-bell 'casc-had-last-bell gen-benchmarks))
(define (para-n-ten-qubit-bell-case gen-benchmarks)
  (gen-para-n-ten-qubit-bell 'para-n-ten-qubit-bell gen-benchmarks))
(define (para-n-had-last-ten-qubit-bell-case gen-benchmarks)
  (gen-para-n-had-last-ten-qubit-bell 'para-n-had-last-ten-qubit-bell gen-benchmarks))
(define (para-n-had-last-n-bell-case gen-benchmarks)
  (gen-para-n-had-last-n-bell 'para-n-had-last-n-bell gen-benchmarks))
(define (para-two-n-bell-state-case gen-benchmarks)
  (gen-para-two-n-bell-state 'para-two-n-bell-state gen-benchmarks))
(define (casc-two-n-bell-state-case gen-benchmarks)
  (gen-casc-two-n-bell-state 'casc-two-n-bell-state gen-benchmarks))
(define (deutsch-jozsa-is-even-case gen-benchmarks)
  (gen-dj-case 'deutsch-jozsa-is-even deutsch-jozsa-spec is-even (range 1 5) gen-benchmarks))
(define (deutsch-jozsa-to-zero-simplified-case gen-benchmarks)
  (gen-dj-case 'deutsch-jozsa-to-zero-simplified simplified-deutsch-jozsa-to-zero to-zero (range 1 21) gen-benchmarks))
(define (deutsch-jozsa-is-even-simplified-case gen-benchmarks)
  (gen-dj-case 'deutsch-jozsa-is-even-simplified simplified-deutsch-jozsa-is-even is-even (range 1 21) gen-benchmarks))
(define (simon-case gen-benchmarks)
  (parameterize [(supported-simulators `((qtorch . ,gen-qasm-case)))]
    (gen-simon-big-matrix-case 'simon (range 1 2) gen-benchmarks))
  (parameterize [(supported-simulators `((iso    . ,gen-iso-case)
                                         (qiskit . ,gen-qiskit-case)
                                         (qsim   . ,gen-cirq-case)
                                         (quimb  . ,gen-quimb-case)))]
    (gen-simon-big-matrix-case 'simon (range 1 5) gen-benchmarks)))
(define (simon-decompose-case gen-benchmarks)
  (gen-simon-decompose-case 'simon-decompose (range 1 4) gen-benchmarks))
(define (grover-case gen-benchmarks)
  (gen-grover-case 0 'grover gen-benchmarks))
(define (qft-case gen-benchmarks)
  (gen-qft 'qft gen-benchmarks))
(define (mcx-case gen-benchmarks)
  (gen-mcx 'mcx gen-benchmarks))
(define (had-last-dj-zero-case gen-benchmarks)
  (gen-had-to-last-dj-to-zero 'had-last-dj-zero gen-benchmarks))
(define (had-last-dj-even-case gen-benchmarks)
  (gen-had-to-last-dj-is-even 'had-last-dj-even gen-benchmarks))
(define (random-symmetry-case gen-benchmarks)
  (gen-random-symmetry 'random-symmetry gen-benchmarks))
(define (random-case gen-benchmarks)
  (gen-random 'random gen-benchmarks))

(define benchmarks
  `((had-last-qubit . ,had-last-qubit-case)
    (bell-state . ,bell-state-case)
    (casc-had-first-bell . ,casc-had-first-bell-case)
    (casc-had-last-bell . ,casc-had-last-bell-case)
    (para-n-ten-qubit-bell . ,para-n-ten-qubit-bell-case)
    (para-n-had-last-ten-qubit-bell . ,para-n-had-last-ten-qubit-bell-case)
    (para-n-had-last-n-bell . ,para-n-had-last-n-bell-case)
    (para-two-n-bell-state . ,para-two-n-bell-state-case)
    (casc-two-n-bell-state . ,casc-two-n-bell-state-case)
    (deutsch-jozsa-is-even . ,deutsch-jozsa-is-even-case)
    (deutsch-jozsa-to-zero-simplified . ,deutsch-jozsa-to-zero-simplified-case)
    (deutsch-jozsa-is-even-simplified . ,deutsch-jozsa-is-even-simplified-case)
    (simon . ,simon-case)
    (simon-decompose . ,simon-decompose-case)
    (grover . ,grover-case)
    (qft . ,qft-case)
    (mcx . ,mcx-case)
    (had-last-dj-zero . ,had-last-dj-zero-case)
    (had-last-dj-even . ,had-last-dj-even-case)
    (random-symmetry . ,random-symmetry-case)
    (random . ,random-case)))

(define (gen-cases cases)
  (for-each
   (λ (tag) ((dict-ref benchmarks tag) gen-benchmarks))
   cases))

(define (count-bench)
  (create-if-not-exist (working-directory))
  (for-each
   (λ (bench) ((cdr bench) count-benchmarks))
   benchmarks))

(define (verify-bench! c)
  (unless (dict-has-key? benchmarks c)
    (error 'cases
           "The specified benchmark ~a doesn't exist, available:\n~a"
           c (dict-keys benchmarks))))

(define command-mode (make-parameter 'gen))
(define picked-benches (make-parameter '()))

(define (main)
  (match (command-mode)
    ['gen (gen-cases (picked-benches))]
    ['list (printf "Available benchmarks are: \n~a\n" (dict-keys benchmarks))]
    ['meta (count-bench)]))

(command-line
 #:program "cases"
 #:once-any
 [("-d" "--dest")
  dest "Target directory"
  (command-mode 'gen)
  (working-directory dest)]
 [("-l" "--list")
  "List all available benchmarks"
  (command-mode 'list)]
 [("-m" "--metadata")
  dest
  "Generate CSVs containing qubit-number,gate-number for all benchmarks and put them into the specified directory"
  (command-mode 'meta)
  (working-directory dest)]
 #:multi
 [("+b" "++bench")
  specified-bench
  "Specify the benchmarks that you want to generate"
  (verify-bench! (string->symbol specified-bench))
  (picked-benches (cons (string->symbol specified-bench) (picked-benches)))]
 #:args ()
 (main))
