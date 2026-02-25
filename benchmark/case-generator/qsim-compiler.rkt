#lang racket
(require (for-syntax syntax/parse)
         racket/format)
(provide define-gate define-unitary to-gate to-unitary
         para casc n-casc
         scircuit qcircuit
         hadamard x cx
         to-iso to-iso/port
         to-qiskit to-qiskit/port
         to-qasm to-qasm/port)

;;; Spec of the case generator:
;;; Prog      ::= Circ ... Main
;;; Main      ::= Circ Nat ; apply a circuit to the initial input
;;; Circ      ::= circuit | unitary | scircuit | qcircuit
;;; circuit   ::= (circuit Symbol Nat Spec ...)
;;; unitary   ::= (unitary Symbol Nat Map)
;;; scircuit  ::= (scircuit Symbol Nat SSpec ...)
;;; qcircuit  ::= (scircuit Symbol Nat Spec ...)
;;; Spec      ::= (para Circ Ids) | (casc Spec ...) | (Circ Ids) | Symbol
;;; ScircSpec ::= (Exp Exp) ...
;;; Exp       ::= String | Symbol | #t | #f | () |
;;;               (let ((var (Symbol Exp))) Exp) | (Exp) | (Exp . Exp)
;;; Ids       ::= (range Nat Nat) | Nat | Nat ...

(define-struct circuit
  (name size spec)
  #:transparent)

(define-struct unitary
  (name size mapping)
  #:transparent)

;;; for iso
(define-struct scircuit
  (name size spec)
  #:transparent)

;;; for qiskit, qasm
(define-struct qcircuit
  (name size spec)
  #:transparent)

(define (gate-name gate)
  (match gate
    ((circuit name _ _) name)
    ((unitary name _ _) name)
    ((scircuit name _ _) name)
    ((qcircuit name _ _) name)))

(define (gate-size gate)
  (match gate
    ((circuit _ size _) size)
    ((unitary _ size _) size)
    ((scircuit _ size _) size)
    ((qcircuit _ size _) size)))

(define hadamard
  (make-circuit 'hadamard 1 '()))

(define x
  (make-circuit 'neg 1 '()))

(define cx
  (make-circuit 'cx 2 '()))

(define (file-writer f name)
  (let ([src (open-output-file name)])
    (f src)
    (close-output-port src)))

(define-syntax (define-gate stx)
  (syntax-parse stx
    [(_ (name size) spec ...)
     #'(define name (to-gate (name size) spec ...))]))

(define-syntax (to-gate stx)
  (syntax-parse stx
    [(_ (name size) spec ...)
     #'(make-circuit 'name size (casc spec ...))]))

(define make-value-table
  (λ (f qnum-in qnum-out)
    (let ((in-bit (expt 2 qnum-in))
          (out-bit (expt 2 qnum-out)))
      (append*
       (for/list ((x (range in-bit)))
         (for/list ((y (range out-bit)))
           (list (+ (arithmetic-shift x qnum-out) (bitwise-xor y (f x)))
                 (+ (arithmetic-shift x qnum-out) y))))))))

(define-syntax (define-unitary stx)
  (syntax-parse stx
    [(_ name in-size out-size f)
     #'(define name (to-unitary name in-size out-size f))]))

(define-syntax (to-unitary stx)
  (syntax-parse stx
    [(_ name in-size out-size f)
     #'(make-unitary 'name (+ in-size out-size) (make-value-table f in-size out-size))]))

(define-syntax (para stx)
  (syntax-parse stx
    [(_ gate id ...)
     #'(let* ((g gate)
              (g-size (gate-size g))
              (qids (gate-input id ...))
              (q-num (length qids)))
         (if (zero? (remainder q-num g-size))
             (map (λ (ids) (cons g ids)) (split-list qids g-size))
             (error 'para "qbits spec ~a is not a multiple of gate size ~a" qids (gate-size g))))]))

(define-syntax (casc stx)
  (syntax-parse stx
    [(_ gate ...)
     #'(append (gate-spec gate) ...)]))

(define (split-list lst n)
  (if (null? lst)
      '()
      (let-values (((h t) (split-at lst n)))
        (cons h (split-list t n)))))

(define-syntax (gate-spec stx)
  (syntax-parse stx
    [(_ ((~datum para) gate id ...))
     #'(para gate id ...)]
    [(_ ((~datum casc) gate ...))
     #'(casc gate ...)]
    [(_ (gate id ...))
     #'(list (cons gate (gate-input id ...)))]
    [(_ g:id) #'g]))

(define-syntax (gate-input stx)
  (syntax-parse stx
    [(_ (range s e))
     #'(range s e)]
    [(_ id)
     #'(range 0 id)]
    [(_ id ...)
     #'(list id ...)]))

(define (n-casc m spec)
  (append* (make-list m spec)))

;;; Compiler to other languages
(define join
  (λ (lst separater)
    (string-append*
     (add-between lst separater))))

(define (generate-lines* str . strs)
  (join (cons str (flatten strs)) "\n"))

(define (generate-lines strs)
  (join strs "\n"))

(define (new-safe-char char)
  (cond
    [(eqv? #\? char) ""]
    [(eqv? #\! char) ""]
    [(eqv? #\. char) ""]
    [(eqv? #\+ char) ""]
    [(eqv? #\- char) ""]
    [(eqv? #\* char) ""]
    [(eqv? #\/ char) ""]
    [(eqv? #\< char) ""]
    [(eqv? #\> char) ""]
    [(eqv? #\: char) ""]
    [(eqv? #\% char) ""]
    [(eqv? #\^ char) "_cap"]
    [(eqv? #\& char) ""]
    [(eqv? #\~ char) ""]
    [(eqv? #\' char) ""]
    [(and (char>=? char #\0) (char<=? char #\9))
     (string-append "r" (list->string `(,char)))]
    [else (list->string `(,char))]))

(define (raw-safe sym)
  (if (or (symbol? sym) (string? sym))
      (let loop ([l (string->list (if (symbol? sym) (symbol->string sym) sym))])
        (cond
          [(null? l) ""]
          [else (string-append
                 (new-safe-char (car l))
                 (loop (cdr l)))]))
      sym))

(define (make-qbits-str size val)
  (~r val #:base 2 #:min-width size #:pad-string "0"))

;;; Compiler to Iso
(define (generate-iso-header)
  "Hadamard :: (Unit + Unit) <-> (Unit + Unit)
Hadamard =
{
  left unit <-> [0.707106781188 * left unit + 0.707106781188 * right unit];
  right unit <-> [0.707106781188 * left unit - 0.707106781188 * right unit]
}

Neg :: (Unit + Unit) <-> (Unit + Unit)
Neg = { left unit <-> right unit; right unit <-> left unit }

Cx :: ((Unit + Unit) x (Unit + Unit)) <-> ((Unit + Unit) x (Unit + Unit))
Cx =
{
  <right unit, x> <-> <right unit, x>;
  <left unit, right unit> <-> <left unit, left unit>;
  <left unit, left unit> <-> <left unit, right unit>
}")

;;; Name converters.
(define iso-keywords
  '(Int Unit fix in left let mu right unit μ))

(define (new-iso-indent)
  "  ")

(define (incre-iso-indent indent)
  (string-append indent (new-iso-indent)))

(define (safe-iso-name name)
  (let ([str-sym (raw-safe name)])
    (cond
      [(memv str-sym iso-keywords)
       =>
       (λ (_) (string-append "Iso" str-sym))]
      [else str-sym])))

(define (generate-iso-type size)
  (let ((side (join (make-list size "(Unit + Unit)") " × ")))
    (if (eq? size 1)
        (format "~a <-> ~a" side side)
        (format "(~a) <-> (~a)" side side))))

(define (generate-iso-name name)
  (string-titlecase (safe-iso-name name)))

(define (generate-iso-circ-type name size)
  (format "~a :: ~a" (generate-iso-name name) (generate-iso-type size)))

(define (generate-iso-vals var ids)
  (let ((vals (join (map (λ (n) (format "~a~a" var n)) ids) ", ")))
    (if (eq? (length ids) 1)
        vals
        (format "<~a>" vals))))

(define (generate-iso-lhs var size)
  (generate-iso-vals var (range size)))

(define (generate-iso-gate var app indent)
  (match app
    (`(,gate ,qids ...)
     (let ((name (gate-name gate))
           (vars (generate-iso-vals var qids)))
       (format "~alet ~a = ~a ~a in\n" indent vars (generate-iso-name name) vars)))))

(define (generate-iso-rhs var size spec indent)
  (define (foo var body spec indent)
    (match spec
      (`() (format "~a~a" indent body))
      (`(,g . ,gs)
       (let ((bind (generate-iso-gate var g indent)))
         (string-append bind
                        (foo var body gs (incre-iso-indent indent)))))))
  (let ((body (generate-iso-vals var (range size))))
    (foo var body spec indent)))

(define (generate-iso-circ-body size spec)
  (let* ((var (gensym "var"))
         (lhs (generate-iso-lhs var size))
         (rhs (generate-iso-rhs var size spec (new-iso-indent))))
    (format "~a~a <->\n~a\n" (new-iso-indent) lhs rhs)))

(define (generate-iso-circ name size spec)
  (format "~a = {\n~a\n}" (generate-iso-name name) (generate-iso-circ-body size spec)))

(define (make-iso-qbits size val)
  (let* ((bits (string->list (make-qbits-str val size)))
         (vals (join (map (λ (v)
                            (match v
                              (#\1 "right unit")
                              (#\0 "left unit")))
                       bits)
                     ", ")))
    (if (eq? size 1)
        vals
        (format "<~a>" vals))))

(define (generate-iso-unitary-mapping size mapping indent)
  (match mapping
    (`(,l ,r)
     (let ((lstr (make-iso-qbits size l))
           (rstr (make-iso-qbits size r)))
       (format "~a~a <-> ~a" indent lstr rstr)))))

(define (generate-iso-unitary-body size mapping)
  (join
   (map (λ (mapping) (generate-iso-unitary-mapping size mapping (new-iso-indent))) mapping)
   ";\n"))

(define (generate-iso-unitary name size mapping)
  (format "~a = {\n~a\n}" (generate-iso-name name) (generate-iso-unitary-body size mapping)))

(define ((generate-iso-scirc-side indent) spec)
  (define recur (generate-iso-scirc-side indent))
  (match spec
    (`,x #:when (symbol? x) (symbol->string x))
    (`,x #:when (string? x) x)
    (#t "left unit")
    (#f "right unit")
    ('() "unit")
    (`(let ((,lvar (,gate ,spec))) ,body)
     (let ((lvar (format "~a" lvar)))
       (format "~alet ~a = ~a ~a in\n~a~a"
               indent lvar (generate-iso-name gate) (recur spec)
               (incre-iso-indent indent) (recur body))))
    (`(,s) (recur s))
    (`(,a . ,d)
     (let ((l (recur a)))
       (format "<~a, ~a>" l ((generate-iso-scirc-side (+ 2 (string-length l))) d))))))

(define (generate-iso-scirc-pair lhs rhs indent)
  (let ((ls ((generate-iso-scirc-side indent) lhs))
        (rs ((generate-iso-scirc-side indent) rhs)))
    (format "~a~a <->\n~a~a" indent ls indent rs)))

(define (generate-iso-scirc-body size spec)
  (let* ((pairs (map (λ (p) (generate-iso-scirc-pair (car p) (cadr p) (new-iso-indent)))
                     spec)))
    (join pairs ";\n")))

(define (generate-iso-scirc name size spec)
  (format "~a = {\n~a\n}" (generate-iso-name name) (generate-iso-scirc-body size spec)))

(define (generate-iso-elem code)
  (match code
    ((scircuit name size spec)
     (generate-lines*
      (generate-iso-circ-type name size)
      (generate-iso-scirc name size spec)))
    ((circuit 'hadamard _ _)
     (error 'generate-iso-elem "Cannot redefine hadamard!"))
    ((circuit 'neg _ _)
     (error 'generate-iso-elem "Cannot redefine neg!"))
    ((circuit 'cx _ _)
     (error 'generate-iso-elem "Cannot redefine cx!"))
    ((circuit name size spec)
     (generate-lines*
      (generate-iso-circ-type name size)
      (generate-iso-circ name size spec)))
    ((unitary name size mapping)
     (generate-lines*
      (generate-iso-circ-type name size)
      (generate-iso-unitary name size mapping)))
    (`,var #:when (symbol? var) (generate-iso-name var))
    (`(,gate ,n) #:when (integer? n)
     (let ((name (gate-name gate))
           (size (gate-size gate)))
       (format "(~a ~a)" (generate-iso-name name) (make-iso-qbits size n))))))

(define (generate-iso-prog prog)
  (join (map generate-iso-elem prog) "\n\n"))

;;; a prog is a list of circuits + a (symbol | application)
(define (generate-iso-source! prog port)
  (display
   (generate-lines*
    (generate-iso-header) ""
    (generate-iso-prog prog))
   port))

(define (to-iso/port prog out-port)
  (generate-iso-source! prog out-port))

(define (to-iso prog source-name)
  (when (file-exists? source-name)
    (delete-file source-name))
  (file-writer ((curry to-iso/port) prog) source-name))

;;; compiler to Qiskit
(define qiskit-keywords
  '(False class from or None continue global pass True
    def if raise and del import return as elif
    in try assert else is while async except
    lambda with await finally nonlocal yield break
    for not))

(define generate-qiskit-header
  (λ ()
    "### Install Qiskit, if needed

\"\"\"
!pip install qiskit[visualization]==1.0.2
!pip install qiskit_aer
!pip install qiskit_ibm_runtime
!pip install matplotlib
!pip install numpy
!pip install pylatexenc
!pip install prototype-zne
\"\"\"

import numpy as np
from qiskit import transpile
from qiskit.circuit import QuantumCircuit
from qiskit.circuit.library import UnitaryGate
from qiskit.quantum_info import Statevector
from qiskit_aer import Aer, AerSimulator"))

(define (new-python-indent)
  "    ")

(define (safe-qiskit-name name)
  (let ([str-sym (raw-safe name)])
    (cond
      [(memv str-sym qiskit-keywords)
       =>
       (λ (_) (string-append "Qiskit" str-sym))]
      [else str-sym])))

(define (generate-qiskit-name name)
  (string-titlecase (safe-qiskit-name name)))

(define (generate-qiskit-circ-def name size)
  (format "~a = QuantumCircuit(~a)" (generate-qiskit-name name) size))

(define (generate-qiskit-circ-args size qids)
  (join (map (λ (id) (number->string (- size id 1))) qids) ", "))

(define ((generate-qiskit-circ-spec name size) spec)
  (match spec
    (`(,gate ,qids ...)
     (match (gate-name gate)
       ('hadamard (format "~a.h(~a)" name (generate-qiskit-circ-args size qids)))
       ('x (format "~a.x(~a)" name (generate-qiskit-circ-args size qids)))
       ('cx (format "~a.cx(~a)" name (generate-qiskit-circ-args size qids)))
       (`,g (format "~a.append(~a, [~a])" name (generate-qiskit-name g)
                    (generate-qiskit-circ-args size qids)))))))

(define (generate-qiskit-circ name size spec)
  (map (generate-qiskit-circ-spec (generate-qiskit-name name) size) spec))

(define (generate-qiskit-unitary name size mapping)
  (let ((mat (gensym 'mat))
        (indices (gensym 'indices))
        (ug (gensym 'ug))
        (gate (generate-qiskit-name name)))
    (generate-lines*
     (format "~a = np.zeros((~a, ~a))" mat (expt 2 size) (expt 2 size))
     (format "~a = [~a]" indices (join (map (λ (p) (format "(~a, ~a)" (car p) (cadr p))) mapping) ", "))
     (format "for i, j in ~a:\n~a~a[i, j] = 1" indices (new-python-indent) mat)
     (format "~a = UnitaryGate(~a)" ug mat)
     (format "~a.append(~a, [~a])" gate ug (join (map number->string (range size)) ", ")))))

(define (generate-qiskit-qcirc name size spec)
  (let ((um (gensym 'um))
        (mat (gensym 'mat)))
    (generate-lines*
     (format "~a = ~a" mat spec)
     (format "~a = UnitaryGate(~a)" um mat)
     (format "~a.append(~a, [~a])"
             (generate-qiskit-name name)
             um
             (join (map number->string (range size)) ", ")))))

(define (generate-qiskit-elem code)
  (match code
    ((qcircuit name size spec)
     (generate-lines*
      (generate-qiskit-circ-def name size)
      (generate-qiskit-qcirc name size spec)))
    ((scircuit name _ _)
     (error 'generate-qiskit-elem "Unsupported circuit type: scircuit ~a" name))
    ((circuit name _ _) #:when (memv name '(hadamard neg cx))
     (error 'generate-qiskit-elem "Cannot redefine ~a!" name))
    ((circuit name size spec)
     (generate-lines*
      (generate-qiskit-circ-def name size)
      (generate-qiskit-circ name size spec)))
    ((unitary name size mapping)
     (generate-lines*
      (generate-qiskit-circ-def name size)
      (generate-qiskit-unitary name size mapping)))
    (`,var #:when (symbol? var) (generate-qiskit-name var))
    (`(,gate ,n)
     #:when (integer? n)
     (let* ((name (gate-name gate))
            (size (gate-size gate))
            (final (generate-qiskit-name (gensym 'fg))))
       (generate-lines*
        (format "~a = QuantumCircuit(~a, ~a)" final size size)
        (format "~a.initialize('~a', ~a.qubits)"
                final (make-qbits-str size n) final)
        (format "~a.append(~a, ~a.qubits)" final (generate-qiskit-name name) final)
        (format "simulator = AerSimulator()")
        (format "~a = transpile(~a, simulator, optimization_level=2)" final final)
        (format "job = Aer.get_backend('statevector_simulator').run(~a, shots=1)"
                final)
        (format "result = job.result()")
        (format "print(f'execution time: {result.time_taken}')")
        (format "state = result.get_statevector()")
        (format "print(state)"))))))

(define (generate-qiskit-prog prog)
  (join (map generate-qiskit-elem prog) "\n\n"))

(define (generate-qiskit-source! prog port)
  (display
   (generate-lines*
    (generate-qiskit-header) ""
    (generate-qiskit-prog prog))
   port))

(define (to-qiskit/port prog out-port)
  (generate-qiskit-source! prog out-port))

(define (to-qiskit prog source-name)
  (when (file-exists? source-name)
    (delete-file source-name))
  (file-writer ((curry to-qiskit/port) prog) source-name))

;;; compiler to qasm
(define qasm-builtin
  '(CNOT SWAP H Rx Ry Rz X Y Z CPHASE CRk CZ))

(define qasm-keywords
  '(def1 def2))

(define (safe-qasm-name name)
  (let ([str-sym (raw-safe name)])
    (cond
      [(memv str-sym qasm-keywords)
       (string-append "Qasm" str-sym)]
      [else str-sym])))

(define (generate-qasm-name name)
  (string-upcase (safe-qasm-name name)))

(define ((generate-qasm-circ-spec name size) spec)
  (match spec
    (`(,gate ,qids ...)
     (match (gate-name gate)
       (`hadamard (format "H ~a" (join (map number->string qids) " ")))
       (`neg (format "X ~a" (join (map number->string qids) " ")))
       (`,g #:when (memv g qasm-builtin) (format "~a ~a" g (join (map number->string qids) " ")))
       (`,g (format "~a ~a" (generate-qasm-name g) (join (map number->string qids) " ")))))))

(define (generate-qasm-circ name size spec)
  (map (generate-qasm-circ-spec (generate-qasm-name name) size) spec))

(define (generate-qasm-unitary-matrix size mapping)
  (let ((sz (expt 2 size)))
    (flatten
     (map (λ (i)
            (map (λ (j)
                   (if (member (list i j) mapping) 1 0))
                 (range sz)))
          (range sz)))))

(define (generate-qasm-unitary-file size mapping)
  (match size
    (n #:when (or (eqv? n 1) (eqv? n 2))
     (join (map number->string (generate-qasm-unitary-matrix size mapping)) " "))
    (_ (error 'generate-qasm-unitary "QASM only supports 1 or 2 qubits gates!"))))

(define (generate-qasm-unitary-def source-name gate)
  (match gate
    ((unitary name size _)
     (let ((gate (generate-qasm-name name)))
       (match size
         (1 (format "def1 ~a ~a.gate" gate source-name))
         (2 (format "def2 ~a ~a.gate" gate source-name))
         (_ (error 'generate-qasm-unitary "QASM only supports 1 or 2 qubits gates!")))))))

(define (generate-qasm-main gate)
  (match gate
    ((circuit name size spec)
     (generate-qasm-circ name size spec))
    ((unitary name size _)
     (format "~a ~a" name (join (map number->string (range size)) " ")))
    ((qcircuit _ _ _)
     (error 'generate-qasm-scirc "QASM doesn't support Qiskit circuit!"))
    ((scircuit _ _ _)
     (error 'generate-qasm-scirc "QASM doesn't support ISO circuit!"))
    (`,var #:when (symbol? var) (generate-qasm-name var))))

(define (generate-qasm-initialize size val)
  (let ((bit-str (string->list (make-qbits-str size val))))
    (join (map (λ (v)
                 (format "X ~a" (cdr v)))
               (filter
                (λ (v) (eqv? (car v) #\1))
                (map cons bit-str (range (length bit-str)))))
          "\n")))

(define (generate-qasm-prog prog source-mats)
  (match prog
    (`(,_ ... (,gate ,n))
     (generate-lines*
      (number->string (gate-size gate))
      (map generate-qasm-unitary-def source-mats (collect-unitary-defs prog))
      (generate-qasm-initialize (gate-size gate) n)
      (generate-qasm-main gate)))))

(define (generate-qasm-source! prog source-mats port)
  (display
   (generate-qasm-prog prog source-mats)
   port))

(define (generate-qasm-unitary-file! unitary-circ port)
  (match unitary-circ
    ((unitary name size mapping)
     (display (generate-qasm-unitary-file size mapping) port))))

(define (collect-unitary-defs prog)
  (match prog
    (`(,circ ... (,_ ,_))
     (filter unitary? circ))))

(define (generate-qasm-unitary-defs! prog port)
  (match prog
    (map (λ (c) (generate-qasm-unitary-file! c port))
         (collect-unitary-defs prog))))

(define (generate-qasm-measurement prog)
  (match prog
    (`(,_ ... (,gate ,_))
     (join (map (λ (_) "0") (range (gate-size gate))) " "))))

(define (generate-qasm-measurement! prog port)
  (display
   (generate-qasm-measurement prog)
   port))

(define (generate-qasm-simulation! qasm-path measurement-path thread-num contraction output-path port)
  (display
   (generate-lines*
    (format ">int threads ~a" thread-num)
    (format ">string qasm ~a" qasm-path)
    (format ">string measurement ~a" measurement-path)
    (format ">string contractmethod ~a" contraction)
    (format ">string outputpath ~a" output-path))
   port))

(define (to-qasm/port prog out-port)
  (display "unitary defs:\n" out-port)
  (generate-qasm-unitary-defs! prog out-port)
  (display "\nqasm:\n" out-port)
  (generate-qasm-source! prog (collect-unitary-def-names prog "") out-port)
  (display "\nmeasurement:\n" out-port)
  (generate-qasm-measurement! prog out-port)
  (display "\nsimulation:\n" out-port)
  (generate-qasm-simulation! "<test-qasm>" "<test-measurement>" "8" "simple-stoch" "<test-out>" out-port))

(define (collect-unitary-def-names prog source-name)
  (map (λ (c)
          (build-path source-name
                      (string-append (symbol->string (unitary-name c)) ".def")))
       (collect-unitary-defs prog)))

(define (to-qasm prog source-name)
  (let ((qasm-name (build-path (string-append source-name ".qasm")))
        (meas-name (build-path (string-append source-name ".meas")))
        (sim-name (build-path (string-append source-name ".sim")))
        (mat-names (collect-unitary-def-names prog source-name))
        (out-name (build-path (string-append source-name ".out"))))
    (for-each
     (λ (name)
       (when (file-exists? name)
         (delete-file name)))
     (append `(,qasm-name ,meas-name ,sim-name) mat-names))
    ;; generate all unitary defines
    (unless (directory-exists? source-name)
      (make-directory source-name))
    (let ((unitaries (map cons (collect-unitary-defs prog) mat-names)))
      (for-each
       (λ (u)
         (file-writer ((curry generate-qasm-unitary-file!) (car u)) (cdr u)))
       unitaries))
    ;; generate the qasm
    (file-writer ((curry generate-qasm-source!) prog mat-names) qasm-name)
    ;; generate the measurement
    (file-writer ((curry generate-qasm-measurement!) prog) meas-name)
    ;; generate the instruction
    (file-writer ((curry generate-qasm-simulation!)
                  qasm-name meas-name "8" "simple-stoch" out-name)
                 sim-name)))

;;; compiler to Cirq
(define cirq-builtin
  '(CNOT SWAP H X Y Z))

(define cirq-keywords
  '(False class from or None continue global pass True
    def if raise and del import return as elif
    in try assert else is while async except
    lambda with await finally nonlocal yield break
    for not))

(define (generate-cirq-header)
  "### Install Cirq, if needed

\"\"\"
!pip install numpy
!pip install cirq --quiet
!pip install qsimcirq --quiet
\"\"\"

import numpy as np
import cirq
import qsimcirq")

(define (safe-cirq-name name)
  (let ([str-sym (raw-safe name)])
    (cond
      [(memv str-sym cirq-keywords)
       =>
       (λ (_) (string-append "Cirq" str-sym))]
      [else str-sym])))

(define (generate-cirq-name name)
  (string-titlecase (safe-cirq-name name)))

(define (generate-cirq-circ-append circ-name op-name qids-name qids)
  (format "~a.append(~a(~a))"
          circ-name
          op-name
          (join (map (λ (id) (format "~a[~a]" qids-name (number->string id))) qids) ", ")))

(define ((generate-cirq-circ-spec circ-name qids-name) spec)
  (match spec
    (`(,gate ,qids ...)
     (match (gate-name gate)
       (`hadamard
        (generate-cirq-circ-append circ-name "cirq.H" qids-name qids))
       (`neg
        (generate-cirq-circ-append circ-name "cirq.X" qids-name qids))
       (`cx
        (generate-cirq-circ-append circ-name "cirq.CX" qids-name qids))
       (`,g #:when (memv g cirq-builtin)
        (generate-cirq-circ-append circ-name (format "cirq.~a" g) qids-name qids))
       (`,g
        (generate-cirq-circ-append circ-name (generate-cirq-name g) qids-name qids))))))

(define (generate-cirq-class name size array)
  (format
   "class ~a(cirq.Gate):
    def __init__(self):
        super(~a, self)

    def _num_qubits_(self):
        return ~a

    def _unitary_(self):
        return ~a

    def _circuit_diagram_info_(self, args):
        return \"~a\""
   name name size array name))

(define (generate-cirq-unitary-def gate)
  (match gate
    ((unitary name size mapping)
     (let ((mat (gensym 'mat))
           (indices (gensym 'indices))
           (ug (gensym 'ug))
           (gate (generate-cirq-name name)))
       (generate-lines*
        (format "~a = np.zeros((~a, ~a))" mat (expt 2 size) (expt 2 size))
        (format "~a = [~a]" indices (join (map (λ (p) (format "(~a, ~a)" (car p) (cadr p))) mapping) ", "))
        (format "for i, j in ~a:\n~a~a[i, j] = 1" indices (new-python-indent) mat)
        (generate-cirq-class ug size indices))))))

(define (generate-cirq-defs circs)
  (join (map generate-cirq-unitary-def (filter unitary? circs)) "\n\n"))

(define (generate-cirq-initialize circ-name qbits size val)
  (generate-lines*
   (format "~a = cirq.LineQubit.range(~a)" qbits size)
   (let ((bit-str (string->list (make-qbits-str size val))))
     (join (map (λ (v)
                  (format "~a.append(cirq.X(~a[~a]))" circ-name qbits (cdr v)))
                (filter
                 (λ (v) (eqv? (car v) #\1))
                 (map cons bit-str (range (length bit-str)))))
           "\n"))))

(define (generate-cirq-main-spec circ-name gate qbits)
  (match gate
    ((circuit name size spec)
     (join (map (generate-cirq-circ-spec circ-name qbits) spec) "\n"))
    ((unitary name _ _)
     (format "~a.append(~a.on(*~a))" circ-name (generate-cirq-name name) qbits))
    ((qcircuit _ _ _)
     (error 'generate-qasm-scirc "Cirq doesn't support Qiskit circuit!"))
    ((scircuit _ _ _)
     (error 'generate-qasm-scirc "Cirq doesn't support ISO circuit!"))))

(define (generate-cirq-execution circ-name)
  (generate-lines*
   (format "qsim_simulator = qsimcirq.QSimSimulator()")
   (format "qsim_results = qsim_simulator.simulate(~a)" circ-name)
   (format "print(qsim_results)")))

(define (generate-cirq-main gate initials)
  (let* ((name (generate-cirq-name (gensym (gate-name gate))))
         (size (gate-size gate))
         (qbits (gensym 'q)))
    (generate-lines*
     (format "~a = cirq.Circuit()" name)
     (generate-cirq-initialize name qbits size initials)
     (generate-cirq-main-spec name gate qbits)
     (generate-cirq-execution name))))

(define (generate-cirq-prog prog)
  (match prog
    (`(,circ ... (,gate ,n))
     (generate-cirq-defs circ)
     (generate-cirq-main gate n))))

(define (generate-cirq-source! prog port)
  (display
   (generate-lines*
    (generate-cirq-header) ""
    (generate-cirq-prog prog))
   port))

(define (to-cirq/port prog out-port)
  (generate-cirq-source! prog out-port))

(define (to-cirq prog source-name)
  (when (file-exists? source-name)
    (delete-file source-name))
  (file-writer ((curry to-cirq/port) prog) source-name))
