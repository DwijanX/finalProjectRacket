#lang play
(print-only-errors #t) ; Para ver solo los errores.

#|
<ZPKS> ::=   <num> | <bool> | <id> | <str>
            | (+ <ZPKS> <ZPKS>)
            | (- <ZPKS> <ZPKS>)
            | (if-tf <ZPKS> <ZPKS> <ZPKS>)
            | (with <id> <ZPKS> <ZPKS>)
            | (app <ZPKS> <ZPKS>) ; puedo aplicar una funcion a otra funcion / puedo usar una funcion como argumento. 
            | (fun <id> <ZPKS>) ; fun(que es una lambda) nombre-arg body
|#

; Ejemplos de uso de una funcion como valor
; {fun {x} {+ x 1}}
; {{fun {x} {+ x 1}} 10} --> 11
; {with {apply10 {fun {f} {f 10}}} {apply10 add1}}
; {{addN 10} 20}

(deftype Expr
  [num n]                                 ; <num>
  [bool b]                                ; <bool>
  [str s]                                 ; <str>
  [list1 f r]
  [Zcar l]
  [Zcdr l]
  [prim operation l r]                    ; (prim <procedure> <ZPKS> <ZPKS>)
  [1argPrim operation v]
  [if-tf c et ef]                         ; (if-tf <ZPKS> <ZPKS> <ZPKS>)
  [with id-name named-expr body-expr]     ; (with <id> <ZPKS> <ZPKS>)
  [id name]                               ; <id> 
  [app fname arg-expr]                    ; (app <ZPKS> <ZPKS>) ; ahora podemos aplicar una funcion a otra
  [fun arg body]                          ; (fun <id> <ZPKS>) ; mantenemos el <id> como el nombre del argumento
  [newbox b]
  [openbox b]
  [setbox b n]
  [seqn e1 e2]
)
(define empty-list '())

(deftype customList
  (mtList)
  (Zcons f r)
  )
#|
<env> ::= (mtEnv)
          | (aEnv <id> <val> <env>)
|#
(deftype Env
  (mtEnv)
  (aEnv id val env)
  )

; empty-env -> (mtEnv)
(define empty-env (mtEnv))

; extend-env:: <id> <val> <env> -> <env>
(define extend-env aEnv)
; env-lookup :: <id> <env> -> <val>
; buscar el valor de una variable dentro del ambiete
(define (env-lookup x env)
  (match env
    [(mtEnv) (error "undefined: " x)]
    [(aEnv id val tail)(if (eq? id x) val (env-lookup x tail))]
    )
  )
(deftype Sto
  (mtSto)
  (aSto loc val sto)
  )
(define empty-sto (mtSto))

(define extend-sto aSto)

(define (sto-lookup l sto)
  (match sto
    [(mtSto) (error "segmentation fault:" l)]
    [(aSto loc val tail)(if (eq? loc l) val (sto-lookup l tail))]
    )
  )

(define (parsePrimitiveArgs operation args)
  (if (empty? (cdr args))
               (parse (car args))
               (prim operation (parse (car args)) (parsePrimitiveArgs operation (cdr args)))))
(define (divisionParser args)
      (cond
        [(empty? (cdr args)) (parse (car args))]
        [(empty? (cdr (cdr args)))  (prim '/ (parse (car args)) (parse (cadr args)))]
        [else (prim '/ (prim '/ (parse (car args)) (parse (cadr args))) (divisionParser (cdr (cdr args))))]
          )
  )

(define (listHandler  args)
  (if (empty? (cdr args))
                        (list1 (parse (car args)) (mtList))
                        (list1 (parse (car args)) (listHandler  (cdr args)))))

; parse: Src -> Expr
; parsea codigo fuente
(define (parse src)
  (match src
    [(? number?) (num src)]
    [(? boolean?) (bool src)]
    [(? symbol?) (id src)]
    [(? string?) (str src)]
    [(list '/ args ...) (divisionParser args)]
    [(list '+ args ...) (parsePrimitiveArgs '+ args)]
    [(list '- args ...) (parsePrimitiveArgs '- args)]
    [(list '* args ...) (parsePrimitiveArgs '* args)]
    [(list '< args ...) (parsePrimitiveArgs '< args)]
    [(list '<= args ...)(parsePrimitiveArgs '<= args)]
    [(list '> args ...) (parsePrimitiveArgs '> args)]
    [(list '>= args ...) (parsePrimitiveArgs '>= args)]
    [(list '== args ...) (parsePrimitiveArgs 'eq? args)]
    [(list '!= args ...) (parsePrimitiveArgs '!= args)]
    [(list '&& args ...) (parsePrimitiveArgs '&& args)]
    [(list '|| args ...) (parsePrimitiveArgs '|| args)]
    [(list 'appendStr args ...) (parsePrimitiveArgs 'appendStr args)]
    [(list 'lenStr str) (1argPrim 'lenStr (parse str) )]
    [(list 'strRef args ...) (parsePrimitiveArgs 'strRef args)]
    [(list 'list args ...)
       (listHandler args)
     ]
    
    [(list 'car list) (Zcar (parse list))]
    [(list 'cdr list) (Zcdr (parse list))]
    [(list 'empty) (mtList)]
    [(list 'if-tf c et ef) (if-tf (parse c) (parse et) (parse ef))]
    [(list 'with (list x e) b) (app (fun x (parse b)) (parse e))]
    [(list 'newbox b) (newbox (parse b))]
    [(list 'openbox e) (openbox (parse e))]
    [(list 'setbox b v) (setbox (parse b) (parse v))]
    [(list 'seqn e1 e2) (seqn (parse e1) (parse e2))]
    [(list arg e) (app (parse arg) (parse e))]
    [(list 'fun (list arg) body) (fun arg (parse body))]
    )
  )

(deftype Val
  (valV v) ; numero, booleano, string, byte, etc.
  (closureV arg body env) ; closure = fun + env
  (v*s val sto)
  (boxV loc)
  )

(define (getPrimitive prim)
  (match prim
    ['+ +]
    ['- -]
    ['* *]
    ['/ (λ (a b)(/ a b))]
    ['< <]
    ['<= <=]
    ['> >]
    ['>= >=]
    ['eq? eq?]
    ['!= (λ (a b)(not (eq? a b)))]
    ['appendStr string-append]
    ['lenStr string-length]
    ['strRef string-ref]
    ['&& (λ (a b)(and a b))]
    ['|| (λ (a b)(or a b))]
    )
  )

; interp :: Expr  Env -> Val
; interpreta una expresion
(define (interp expr env sto)
  (match expr
    [(num n) (v*s (valV n) sto)]
    [(bool b) (v*s (valV b) sto)]
    [(str s) (v*s (valV s) sto)]
    [(mtList) (v*s (valV '()) sto)]
    [(list1 f r)
     (def (v*s f-val f-sto) (interp f env sto))
     (def (v*s r-val r-sto) (interp r env f-sto))
     (v*s (valV (Zcons f-val r-val)) sto)]
    [(Zcar l)
     (def (v*s (valV (Zcons f-val r-val)) l-sto) (interp l env sto)) 
     (v*s f-val sto)
     ]
    [(Zcdr l)
     (def (v*s (valV (Zcons f-val r-val)) l-sto) (interp l env sto)) 
     (v*s r-val sto)
     ]
    [(fun arg body) (v*s (closureV arg body env) sto)]
    [(id x) (v*s (sto-lookup (env-lookup x env) sto) sto)]
    
    [(prim operation l r)
     (def (v*s l-val l-sto) (interp l env sto))
     (def (v*s r-val r-sto) (interp r env l-sto))
     (v*s (valVOperation (getPrimitive operation) l-val r-val) r-sto)]
    
    [(1argPrim operation v)
     (def (v*s val v-sto) (interp v env sto))
     (v*s (valVOperation1Arg (getPrimitive operation) val ) v-sto)
     ]
    
    [(if-tf c et ef)
     (def (v*s cond-val cond-sto) (interp c env sto))
     (if (valV-v cond-val)
         (interp et env cond-sto) 
         (interp ef env cond-sto))]
     
    [(app f e)
     (def (v*s (closureV arg body fenv) fSto) (interp f env sto))
     (def (v*s exp-val exp-sto) (interp e env fSto))
     (def new-loc (malloc exp-sto))
     
     (interp body (extend-env arg new-loc fenv) (extend-sto new-loc exp-val exp-sto))]
    [(newbox b)
     
     (def (v*s exp-val exp-sto) (interp b env sto))
     (def new-loc (malloc exp-sto))
     (v*s (boxV new-loc) (extend-sto new-loc exp-val exp-sto))
     ]
    [(openbox b)
     (def (v*s (boxV loc) intSto) (interp b env sto))
     (v*s (sto-lookup loc intSto) intSto)
     ]
    [(setbox b n)
     (def (v*s (boxV loc) intSto) (interp b env sto))
     (def (v*s exp-val exp-sto) (interp n env intSto))
     
     (v*s (boxV loc) (extend-sto loc exp-val exp-sto))
     ]
    [(seqn e1 e2)
     (def (v*s e1val e1sto) (interp e1 env sto))
     (def ans (interp e2 env e1sto))
     ans
     ]

))
(define (malloc sto)
  (match sto
    [(mtSto) 0]
    [(aSto loc _ tail) (+ 1 (malloc tail))]
    )
  )

; valV+ : procedure,Val -> Val
(define (valVOperation op s1 s2)
  
  (valV (op (valV-v s1) (valV-v s2)))
  
  )
(define (valVOperation1Arg op s1)
  
  (valV (op (valV-v s1) ))
  
  )



; run: Src -> Src
; corre un programa
(define (run prog)
  
  (def (v*s res sto) (interp (parse prog) empty-env empty-sto))
    (match res
      [(valV v) v]
      [(closureV arg body env) res]
      [(boxV loc) res])
  
    )
;Pruebas If -----------------------------------------------
(test (run '(if-tf (== 3 2) "fue true" "fue false")) "fue false")
(test (run '(if-tf (== 3 3) "fue true" "fue false")) "fue true")
;Pruebas strings---------------------------------------------
(test (run '"soy un string") "soy un string")
(test (run '(appendStr "string 1 " "string 2") )"string 1 string 2")
(test (run '(appendStr "string 1 " "string 2 " "string 3") )"string 1 string 2 string 3")
(test (run '(lenStr (appendStr "string 1 " "string 2 " "string 3"))) 26)
(test (run '(strRef (appendStr "string 1 " "string 2 " "string 3") 1)) #\t)
(test (run '(strRef (appendStr "string 1 " "string 2 " "string 3") 0)) #\s)
(test (run '(strRef (appendStr "string 1 " "string 2 " "string 3") 7)) #\1)
;(parse '(lenStr (appendStr "string 1 " "string 2 " "string 3")))

(run '{list (+ 3 5) 1 3})
(run '(car {list (+ 68 1) 1 3}))
(run '(cdr {list (+ 68 1) 1 3}))
(run '(car (cdr {list (+ 68 1) 1 3})))
(run '(empty))



;-------------------------------------------------------Pruebas base

(test (run '{* -2 3 4}) -24)

(test (run '{+ 3 (- 5 3)}) 5)
(test (run '{+ 3 4}) 7)
(test (run '{- 5 1}) 4)
(test (run '{+ 3 4}) 7)
(test (run '{- 5 1}) 4)

(test (run '{+ 1 2 3 4}) 10)
(test (run '{* 2 3 4}) 24)
(test (run '{/ 12 2 2}) 3)
(test (run '{< 12 3}) #f)
(test (run '{<= 12 3}) #f)
(test (run '{< 12 12}) #f)
(test (run '{<= 12 12}) #t)
(test (run '{> 12 3}) #t)
(test (run '{>= 12 3}) #t)
(test (run '{> 12 12}) #f)
(test (run '{>= 12 12}) #t)
(test (run '{>= 12 12}) #t)
(test (run '{== 12 12}) #t)
(test (run '{== 12 11}) #f)
(test (run '{!= 12 12}) #f)
(test (run '{!= 12 11}) #t)
(test (run '{&& 12 11}) 11)
(test (run '{&& #f #t}) #f)
(test (run '{|| #f #t}) #t)
(test (run '{|| 12 11}) 12)

