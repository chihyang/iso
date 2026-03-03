#lang racket
(require (for-syntax syntax/parse)
         racket/format)
(provide define-gate define-unitary to-gate to-unitary
         para casc n-casc
         scircuit qcircuit
         hadamard x cx
         to-iso to-iso/port
         to-qiskit to-qiskit/port
         to-qasm to-qasm/port
         to-cirq to-cirq/port)

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

(define (gate-spec gate)
  (match gate
    ((circuit _ _ spec) spec)
    ((unitary _ _ spec) spec)
    ((scircuit _ _ spec) spec)
    ((qcircuit _ _ spec) spec)))

(define hadamard
  (make-circuit 'hadamard 1 '()))

(define x
  (make-circuit 'neg 1 '()))

(define cx
  (make-circuit 'cx 2 '()))

(define swap
  (make-circuit 'swap 2 '()))

(define (rx deg)
  (make-circuit 'rx 1 `(,deg)))

(define (ry deg)
  (make-circuit 'ry 1 `(,deg)))

(define (rz deg)
  (make-circuit 'rz 1 `(,deg)))

(define (rotation-deg deg)
  (- deg (* 2 pi (floor (/ deg (* 2 pi))))))

(define rotation-gates '(rx ry rz))

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
     #'(append (make-spec gate) ...)]))

(define (split-list lst n)
  (if (null? lst)
      '()
      (let-values (((h t) (split-at lst n)))
        (cons h (split-list t n)))))

(define-syntax (make-spec stx)
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

;;; Decompose a permutation into a series of one or two permutations
;;; Each two permutations will become a swap
;;;
;;; map-classify : Dict(Nat, Nat) -> List(Dict(Nat, Nat))
;;;
;;; Given a permutation represented as a map, return a list of maps that have no
;;; interaction.
(define (map-classify mapping)
  (cond
    ((null? mapping) '())
    (else (update-or-append (caar mapping) (cadar mapping) (map-classify (cdr mapping))))))

(define (update-or-append k v maps)
  (cond
    ((null? maps) (list (list (list k v))))
    ((assv v (car maps)) (cons (cons (list k v) (car maps)) (cdr maps)))
    (else
     (cons (car maps)
           (update-or-append k v (cdr maps))))))

;;; map-decompose : Dict(Nat, Nat) -> Dict(Nat, Nat)
;;; Given a permutation, decompose it into a list of two permutations.
;;; WARNING: the meaning of the output is different from input!
;;; For example, the input is:
;;;   ((1 2) (2 3) (3 4) (4 5))
;;; The result is in cycle notation:
;;;   ((1 4) (2 4) (3 4))
;;; which can be converted to the equivalent input form of three maps:
;;;   (((1 4) (4 1))
;;;    ((2 4) (4 2))
;;;    ((3 4) (4 4)))
(define (map-decompose mapping)
  (map-decompose-helper
   mapping
   (map (λ (kv) (list (cadr kv) (car kv))) mapping)))

(define (map-decompose-helper mapping reverse-mapping)
  (match mapping
    ('() '())
    (`((,k ,v) . ,mapping^)
     #:when (eqv? k v)
     (map-decompose-helper mapping^ reverse-mapping))
    (`((,k ,v) . ,mapping^)
     (let* ((v^ (cadr (assv k reverse-mapping)))
            (mapping^ (dict-set mapping^ v^ `(,v)))
            (reverse-mapping (dict-set reverse-mapping v `(,v^))))
       (if (eqv? v^ v)
           (list (list k v^))
           (cons (list k v^)
                 (map-decompose-helper mapping^ reverse-mapping)))))))

;;; Decompose a unitary map to transpositions (two-cycles) in cyclic notation.
;;; unitary-decompose : List((Nat, Nat)) -> List((Nat, Nat))
(define (unitary-decompose mapping)
  (append* (map map-decompose (map-classify mapping))))

;;; Decompose a unitary map to transpositions (two-cycles) in cyclic notation.
;;; permutation->commands : List((Nat, Nat)) -> List(Spec)
(define (permutation->commands transpositions)
  (append*
   (map (λ (qids)
          (match (sort qids <)
            (`(,a ,d) #:when (eqv? (add1 a) d)
             (make-spec (swap a d)))
            (`(,a ,d)
             (make-spec (swap a d)))))
        transpositions)))

(define (name-conflict name)
  (memv name (append builtin-gates rotation-gates)))

(define (collect-defs-from-scirc-side spec)
  (match spec
    (`(let ((,lvar (,gate ,spec))) ,body)
     (set-union (collect-defs-from-gate gate)
                (collect-defs-from-scirc-side spec)
                (collect-defs-from-scirc-side body)))
    (`(,s) (collect-defs-from-scirc-side s))
    (`(,a . ,d)
     (set-union (collect-defs-from-scirc-side a)
                (collect-defs-from-scirc-side d)))
    (_ (set))))

(define (collect-from-scirc-spec spec)
  (foldl (λ (p r) (set-union (collect-defs-from-scirc-side (cadr p)) r))
         (set)
         spec))

(define (collect-defs-from-spec spec)
  (match spec
    (`(,gate ,_ ...)
     (collect-defs-from-gate gate))))

(define (collect-defs-from-specs specs)
  (foldl (λ (spec r) (set-union (collect-defs-from-spec spec) r))
         (set)
         specs))

(define (collect-defs-from-gate gate)
  (match gate
    ((scircuit name _ spec)
     #:when (not (name-conflict name))
     (set-union (set gate) (collect-from-scirc-spec spec)))
    ((circuit name _ _)
     #:when (memv name builtin-gates)
     (set gate))
    ((circuit name 1 `(,deg))
     #:when (memv name rotation-gates)
     (set (circuit name 1 `(,(rotation-deg deg)))))
    ((circuit name _ spec)
     #:when (not (name-conflict name))
     (set-union (set gate) (collect-defs-from-specs spec)))
    ((unitary name _ _)
     #:when (not (name-conflict name))
     (set gate))
    ((qcircuit name _ _)
     #:when (not (name-conflict name))
     (set gate))))

(define (gate-comp g1 g2)
  (match `(,g1 ,g2)
    (`(,(unitary name1 _ _) ,(unitary name2 _ _)) (symbol<? name1 name2))
    (`(,(unitary _ _ _) ,_) #t)
    (`(,(qcircuit _ _ _) ,(unitary _ _ _)) #f)
    (`(,(qcircuit name1 _ _) ,(qcircuit name2 _ _)) (symbol<? name1 name2))
    (`(,(qcircuit _ _ _) ,_) #t)
    (`(,(circuit _ _ _) ,(unitary _ _ _)) #f)
    (`(,(circuit _ _ _) ,(qcircuit _ _ _)) #f)
    (`(,(circuit name1 _ _) ,(circuit name2 _ _))
     (cond
       ((and (memv name1 builtin-gates) (memv name2 builtin-gates))
        (symbol<? name1 name2))
       ((and (memv name1 builtin-gates)) #t)
       ((memv name2 builtin-gates) #f)
       ((and (memv name1 rotation-gates) (memv name2 rotation-gates))
        (symbol<? name1 name2))
       ((memv name1 rotation-gates) #t)
       ((memv name2 rotation-gates) #f)
       (else (symbol<? name1 name2))))
    (`(,(circuit _ _ _) ,_) #t)
    (`(,(scircuit name1 _ _) ,(scircuit name2 _ _)) (symbol<? name1 name2))
    (`(,(scircuit _ _ _) ,_) #f)))

(define (collect-defs gates)
  (let ((all-gates
         (foldl (λ (gate r) (set-union (collect-defs-from-gate gate) r))
                (set)
                gates)))
    (sort (set->list all-gates) gate-comp)))

;;; Compiler to Iso
(define builtin-gates
  '(hadamard neg cx swap))

(define (generate-iso-had name)
  (format
   "~a :: (Unit + Unit) <-> (Unit + Unit)
~a =
{
  left unit <-> [0.707106781188 * left unit + 0.707106781188 * right unit];
  right unit <-> [0.707106781188 * left unit - 0.707106781188 * right unit]
}" name name))

(define (generate-iso-x name)
  (format
   "~a :: (Unit + Unit) <-> (Unit + Unit)
~a = { left unit <-> right unit; right unit <-> left unit }"
   name name))

(define (generate-iso-cx name)
  (format
   "~a :: ((Unit + Unit) x (Unit + Unit)) <-> ((Unit + Unit) x (Unit + Unit))
~a =
{
  <left unit, x>           <-> <left unit, x>;
  <right unit, right unit> <-> <right unit, left unit>;
  <right unit, left unit>  <-> <right unit, right unit>
}"
   name name))

(define (generate-iso-swap name)
  (format
   "~a :: ((Unit + Unit) x (Unit + Unit)) <-> ((Unit + Unit) x (Unit + Unit))
~a = { <x, y> <-> <y, x> }"
   name name))

(define (generate-iso-builtin name)
  (match name
    ('hadamard (generate-iso-had 'Hadamard))
    ('neg (generate-iso-x 'Neg))
    ('cx (generate-iso-cx 'Cx))
    ('swap (generate-iso-swap 'Swap))))

(define (print-iso-scalar num)
  (if (< num 0)
      (format "(~a)" (~r num #:precision 10))
      (~r num #:precision 10)))

(define (generate-iso-rx name deg)
  (let ((c (cos (/ deg 2)))
        (s (sin (/ deg 2))))
    (format
     "~a :: (Unit + Unit) <-> (Unit + Unit)
~a =
{
  left unit  <-> [~a * left unit + (0 :+ ~a) * right unit];
  right unit <-> [(0 :+ ~a) * left unit + ~a * right unit]
}"
     name name
     (print-iso-scalar c) (print-iso-scalar (- s))
     (print-iso-scalar (- s)) (print-iso-scalar c))))

(define (generate-iso-ry name deg)
  (let ((c (cos (/ deg 2)))
        (s (sin (/ deg 2))))
    (format
     "~a :: (Unit + Unit) <-> (Unit + Unit)
~a =
{
  left unit  <-> [~a * left unit + ~a * right unit];
  right unit <-> [~a * left unit + ~a * right unit]
}"
     name name
     (print-iso-scalar c) (print-iso-scalar (- s))
     (print-iso-scalar s) (print-iso-scalar c))))

(define (generate-iso-rz name deg)
  (let ((c (cos (/ deg 2)))
        (s (sin (/ deg 2))))
    (format
     "~a :: (Unit + Unit) <-> (Unit + Unit)
~a =
{
  left unit  <-> (~a :+ ~a) * right unit;
  right unit <-> (~a :+ ~a) * left unit
}"
     name name
     (print-iso-scalar c) (print-iso-scalar (- s))
     (print-iso-scalar c) (print-iso-scalar s))))

(define (generate-iso-rotation-name name deg)
  (let ((deg (- deg (* 2 pi (floor (/ deg (* 2 pi) ))))))
    (format "~a~a"
            (generate-iso-name name)
            (list->string
             (filter char-numeric? (string->list (number->string deg)))))))

(define (generate-iso-rotation name deg)
  (match deg
    (`(,val)
     (let ((name^ (generate-iso-rotation-name name val)))
       (match name
         ('rx (generate-iso-rx name^ val))
         ('ry (generate-iso-ry name^ val))
         ('rz (generate-iso-rz name^ val)))))))

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

(define (generate-iso-gate-name gate)
  (if (memv (gate-name gate) rotation-gates)
      (generate-iso-rotation-name (gate-name gate) (car (gate-spec gate)))
      (generate-iso-name (gate-name gate))))

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
     (let ((name (generate-iso-gate-name gate))
           (vars (generate-iso-vals var qids)))
       (format "~alet ~a = ~a ~a in\n" indent vars name vars)))))

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
  (let* ((bits (string->list (make-qbits-str size val)))
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
               indent lvar (generate-iso-gate-name gate) (recur spec)
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

(define (generate-iso-def gate)
  (match gate
    ((scircuit name size spec)
     (generate-lines*
      (generate-iso-circ-type name size)
      (generate-iso-scirc name size spec)))
    ((circuit name _ _) #:when (memv name builtin-gates)
     (generate-iso-builtin name))
    ((circuit name 1 spec) #:when (memv name rotation-gates)
     (generate-iso-rotation name spec))
    ((circuit name size spec)
     (generate-lines*
      (generate-iso-circ-type name size)
      (generate-iso-circ name size spec)))
    ((unitary name size mapping)
     (generate-lines*
      (generate-iso-circ-type name size)
      (generate-iso-unitary name size mapping)))
    (_ (error 'generate-iso-def "Unsupported gate type: ~a" gate))))

(define (generate-iso-defs circs)
  (join (map generate-iso-def (collect-defs circs)) "\n\n"))

(define (generate-iso-main gate n)
  (let ((name (generate-iso-gate-name gate))
        (size (gate-size gate)))
    (format "(~a ~a)" name (make-iso-qbits size n))))

(define (generate-iso-prog prog)
  (match prog
    (`(,circ ... (,gate ,n))
     (generate-lines*
      (generate-iso-defs `(,gate))
      ""
      (generate-iso-main gate n)))))

;;; a prog is a list of circuits + a (symbol | application)
(define (generate-iso-source! prog port)
  (display
   (generate-iso-prog prog)
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
from qiskit.circuit.library import UnitaryGate, RXGate, RYGate, RZGate, HGate, CXGate, XGate, SwapGate
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

(define (generate-qiskit-gate-name gate)
  (if (memv (gate-name gate) rotation-gates)
      (generate-qiskit-rotation-name (gate-name gate) (car (gate-spec gate)))
      (generate-qiskit-name (gate-name gate))))

(define (generate-qiskit-rotation-name name deg)
  (let ((deg (- deg (* 2 pi (floor (/ deg (* 2 pi) ))))))
    (format "~a~a"
            (generate-iso-name name)
            (list->string
             (filter char-numeric? (string->list (number->string deg)))))))

(define (generate-qiskit-builtin name)
  (match name
    ('hadamard
     (format "~a = ~aGate()" (generate-qiskit-name name) 'H))
    ('neg
     (format "~a = ~aGate()" (generate-qiskit-name name) 'X))
    ('cx
     (format "~a = ~aGate()" (generate-qiskit-name name) 'CX))
    ('swap
     (format "~a = ~aGate()" (generate-qiskit-name name) 'Swap))))

(define (generate-qiskit-circ-def name size)
  (format "~a = QuantumCircuit(~a)" (generate-qiskit-name name) size))

(define (generate-qiskit-circ-args size qids)
  (join (map (λ (id) (number->string (- size id 1))) qids) ", "))

(define ((generate-qiskit-circ-spec name size) spec)
  (match spec
    (`(,gate ,qids ...)
     (match (gate-name gate)
       (`,g (format "~a.append(~a, [~a])" name (generate-qiskit-gate-name gate)
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

(define (generate-qiskit-def gate)
  (match gate
    ((qcircuit name size spec)
     (generate-lines*
      (generate-qiskit-circ-def name size)
      (generate-qiskit-qcirc name size spec)))
    ((scircuit name _ _)
     (error 'generate-qiskit-elem "Unsupported circuit type: scircuit ~a" name))
    ((circuit name _ _) #:when (memv name builtin-gates)
     (generate-qiskit-builtin name))
    ((circuit name 1 `(,deg)) #:when (memv name rotation-gates)
     (let ((rotation-name (generate-qiskit-rotation-name name deg)))
       (format "~a = ~aGate(~a)" rotation-name (string-upcase (symbol->string name)) deg)))
    ((circuit name size spec)
     (generate-lines*
      (generate-qiskit-circ-def name size)
      (generate-qiskit-circ name size spec)))
    ((unitary name size mapping)
     (generate-lines*
      (generate-qiskit-circ-def name size)
      (generate-qiskit-unitary name size mapping)))))

(define (generate-qiskit-elem code)
  (match code
    ((qcircuit name size spec)
     (generate-lines*
      (generate-qiskit-circ-def name size)
      (generate-qiskit-qcirc name size spec)))
    ((scircuit name _ _)
     (error 'generate-qiskit-elem "Unsupported circuit type: scircuit ~a" name))
    ((circuit name _ _) #:when (memv name '(hadamard neg cx swap))
                        (error 'generate-qiskit-elem "Cannot redefine ~a!" name))
    ((circuit name 1 `(,deg)) #:when (memv name rotation-gates)
     (let ((rotation-name (generate-qiskit-rotation-name name deg)))
       (format "~a = ~aGate(~a)" rotation-name (string-upcase (symbol->string name)) deg)))
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
        (format "~a.append(~a, ~a.qubits)" final (generate-qiskit-gate-name gate) final)
        (format "simulator = AerSimulator()")
        (format "~a = transpile(~a, simulator, optimization_level=2)" final final)
        (format "job = Aer.get_backend('statevector_simulator').run(~a, shots=1)"
                final)
        (format "result = job.result()")
        (format "print(f'execution time: {result.time_taken}')")
        (format "state = result.get_statevector()")
        (format "print(state)"))))))

(define (generate-qiskit-defs circs)
  (join (map generate-qiskit-def (collect-defs circs)) "\n\n"))

(define (generate-qiskit-main gate n)
  (let ((name (generate-qiskit-gate-name gate))
        (size (gate-size gate)))
    (let* ((name (gate-name gate))
           (size (gate-size gate))
           (final (generate-qiskit-name (gensym 'fg))))
      (generate-lines*
       (format "~a = QuantumCircuit(~a, ~a)" final size size)
       (format "~a.initialize('~a', ~a.qubits)"
               final (make-qbits-str size n) final)
       (format "~a.append(~a, ~a.qubits)" final (generate-qiskit-gate-name gate) final)
       (format "simulator = AerSimulator()")
       (format "~a = transpile(~a, simulator, optimization_level=2)" final final)
       (format "job = Aer.get_backend('statevector_simulator').run(~a, shots=1)"
               final)
       (format "result = job.result()")
       (format "print(f'execution time: {result.time_taken}')")
       (format "state = result.get_statevector()")
       (format "print(state)")))))

(define (generate-qiskit-prog prog)
  (match prog
    (`(,circ ... (,gate ,n))
     (generate-lines*
      (generate-qiskit-defs `(,gate))
      ""
      (generate-qiskit-main gate n)))))

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
    (deg #:when (number? deg)
     (match name
      (`,g #:when (memv g rotation-gates)
       (format "~a ~a ~a" (generate-qasm-name g) deg (number->string size)))))
    (`(,gate ,qids ...)
     (match (gate-name gate)
       (`hadamard (format "H ~a" (join (map number->string qids) " ")))
       (`neg (format "X ~a" (join (map number->string qids) " ")))
       (`,g #:when (memv g rotation-gates)
        (format "~a ~a ~a" (generate-qasm-name g) (car (gate-spec gate)) (join (map number->string qids) " ")))
       (`,g #:when (memv g qasm-builtin) (format "~a ~a" g (join (map number->string qids) " ")))
       (`,g (format "~a ~a" (generate-qasm-name g) (join (map number->string qids) " ")))))))

(define (generate-qasm-circ name size spec)
  (map (generate-qasm-circ-spec name size) spec))

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
    (`(,(unitary name _ _) ,qids ...)
     (generate-cirq-circ-append circ-name (format "~a().on" (generate-cirq-name name)) qids-name qids))
    (`(,gate ,qids ...)
     (match (gate-name gate)
       (`hadamard
        (generate-cirq-circ-append circ-name "cirq.H" qids-name qids))
       (`neg
        (generate-cirq-circ-append circ-name "cirq.X" qids-name qids))
       (`cx
        (generate-cirq-circ-append circ-name "cirq.CX" qids-name qids))
       (`swap
        (generate-cirq-circ-append circ-name "cirq.SWAP" qids-name qids))
       (`,g #:when (memv g rotation-gates)
        (generate-cirq-circ-append
         circ-name
         (format "cirq.~a~a" (generate-cirq-name g) (gate-spec gate))
         qids-name qids))
       (`,g #:when (memv g cirq-builtin)
        (generate-cirq-circ-append circ-name (format "cirq.~a" (generate-cirq-name g)) qids-name qids))
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

(define (generate-cirq-def gate)
  (match gate
    ((unitary _ _ _)
     (generate-cirq-unitary-def gate))
    ((circuit name 1 `(,deg))
     #:when (memv name rotation-gates)
     (format "~a = ~a(rads=~a)" (generate-qiskit-gate-name name deg) deg))
    ((circuit _ _ _) "")
    (_ (error 'generate-cirq-def "Unsupported circuit type: ~a" gate))))

(define (generate-cirq-unitary-def gate)
  (match gate
    ((unitary name size mapping)
     (let ((mat (gensym 'mat))
           (indices (gensym 'indices))
           (gate (generate-cirq-name name)))
       (generate-lines*
        (format "~a = np.zeros((~a, ~a))" mat (expt 2 size) (expt 2 size))
        (format "~a = [~a]" indices (join (map (λ (p) (format "(~a, ~a)" (car p) (cadr p))) mapping) ", "))
        (format "for i, j in ~a:\n~a~a[i, j] = 1" indices (new-python-indent) mat)
        ""
        (generate-cirq-class gate size mat))))))

(define (generate-cirq-defs circs)
  (join (map generate-cirq-def (collect-defs circs)) "\n\n"))

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
    ((circuit name 1 `(,deg))
     #:when (memv name rotation-gates)
     (let ((op-name (generate-qiskit-rotation-name name deg)))
       (generate-cirq-circ-append circ-name op-name qbits (range 1))) "")
    ((circuit name size spec)
     (join (map (generate-cirq-circ-spec circ-name qbits) spec) "\n"))
    ((unitary name size _)
     (generate-cirq-circ-append circ-name (format "~a().on" (generate-cirq-name name)) qbits (range size)))
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
     (generate-lines*
      (generate-cirq-defs `(,gate))
      ""
      (generate-cirq-main gate n)))))

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
