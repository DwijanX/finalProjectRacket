#lang play
(print-only-errors #t) ; Para ver solo los errores.

#|
<ZPKS> ::=   <num> | <bool> | <str>
            | (+ <ZPKS> <ZPKS>)
            | (- <ZPKS> <ZPKS>)
            | (/ <ZPKS> <ZPKS>)
            | (* <ZPKS> <ZPKS>)
            | (< <ZPKS> <ZPKS>)
            | (<= <ZPKS> <ZPKS>)
            | (> <ZPKS> <ZPKS>)
            | (>= <ZPKS> <ZPKS>)
            | (== <ZPKS> <ZPKS>)
            | (!= <ZPKS> <ZPKS>)
            | (&& <ZPKS> <ZPKS>)
            | (|| <ZPKS> <ZPKS>)
            | (appendStr <ZPKS> <ZPKS>)
            | (lenStr <ZPKS>)
            | (strRef <ZPKS> <ZPKS>)
            | (list <ZPKS> ...)
            | (Zcar <ZPKS>) 
            |(Zcdr <ZPKS>) 
            |(take <ZPKS> <ZPKS>)
            | (empty)
            | (if-tf <ZPKS> <ZPKS> <ZPKS>)
            | (with <id> <ZPKS> <ZPKS>)
            | (newbox <ZPKS>)
            | (openbox <ZPKS>)
            | (setbox <ZPKS> <ZPKS>)
            | (seqn <ZPKS> ...)
            | (fun <id> <ZPKS>)
            | (appL <ZPKS> <ZPKS>)
|#


(deftype Expr
  [num n]                                 ; <num>
  [bool b]                                ; <bool>
  [str s]                                 ; <str>
  [list1 f r]                             ; (list1 <ZPKS> <ZPKS>) ->val
  [Zcar l]                                ; (Zcar <ZPKS>) -> val
  [Zcdr l]                                ; (Zcdr <ZPKS>) -> val
  [take l n]                              ; (take <ZPKS> <ZPKS>)
  [prim operation l r]                    ; (prim <procedureId> <ZPKS> <ZPKS>)
  [oneArgPrim operation v]                ; (oneArgPrim <procedureId> <ZPKS>)
  [if-tf c et ef]                         ; (if-tf <ZPKS> <ZPKS> <ZPKS>)
  [with id-name named-expr body-expr]     ; (with <id> <ZPKS> <ZPKS>)
  [id name]                               ; <id> 
  [app fname arg-expr]                    ; (app <ZPKS> <ZPKS>) ; ahora podemos aplicar una funcion a otra
  [fun arg body]                          ; (fun <id> <ZPKS>) ; mantenemos el <id> como el nombre del argumento
  [delay e]                               ; (delay <ZPKS>) -> promise
  [force p]                               ; (force promise) -> val
  [newbox b]                              ; (newbox <ZPKS>) ->loc
  [openbox b]                             ; (openbox <ZPKS>)
  [setbox b n]                            ; (setbox <ZPKS> <ZPKS>)
  [seqn e1 e2]                            ; (seqn <ZPKS> <ZPKS>)
  [appL f e]                              ; (appL <ZPKS> <ZPKS>)
  )
; lista vacia
(define empty-list '())

#|
<customList> ::= (mtList)
          | (Zcons <first> <right> )
|#
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
#|
<sto> ::= (mtSto)
          | (aSto <loc> <val> <sto>)
|#
(deftype Sto
  (mtSto)
  (aSto loc val sto)
  )
; empty-sto -> (mtSto)
; devuelve un storage vacio
(define empty-sto (mtSto))
; extend-sto <loc> <val> <sto> -> <sto>
; agrega una clave-valor al storage y devuelve el eactualizado
(define extend-sto aSto)
; sto-lookup :: <loc> <sto> -> <val>
; buscar el valor de una direccion de memoria dentro del storage
(define (sto-lookup l sto)
  (match sto
    [(mtSto) (error "undefined")]
    [(aSto loc val tail)(if (eq? loc l) val (sto-lookup l tail))]
    )
  )

; listHandler :'primitiveId:string,src  -> Expr
; se encarga de parsear funciones primitivas del lenguaje
(define (parsePrimitiveArgs operation args)
  (if (empty? (cdr args))
      (parse (car args))
      (prim operation (parse (car args)) (parsePrimitiveArgs operation (cdr args)))))
; listHandler :src -> Expr
; se encarga de parsear la operacion division
(define (divisionParser args)
  (cond
    [(empty? (cdr args)) (parse (car args))]
    [(empty? (cdr (cdr args)))  (prim '/ (parse (car args)) (parse (cadr args)))]
    [else (prim '/ (prim '/ (parse (car args)) (parse (cadr args))) (divisionParser (cdr (cdr args))))]
    )
  )
; listHandler :src -> Expr
; se encarga de parsear listas 
(define (listHandler  args)
  (if (empty? (cdr args))
      (list1 (parse (car args)) (mtList))
      (list1 (parse (car args)) (listHandler  (cdr args)))))
; appFunctionParser :src,src -> Expr
; se encarga de parsear porciones de codigo que incluyen una aplicacion de funcion 
(define (appFunctionParser arg exps)
  (if (empty? (cdr exps))
      (app (parse arg) (parse (car exps)))
      (appFunctionParser (list arg (car exps)) (cdr exps)  )
      )
  )
; appFunctionParserLazy :src,src -> Expr
; se encarga de parsear porciones de codigo que incluyen una aplicacion de funcion perezosa
(define (appFunctionParserLazy arg exps)
  
  (if (empty? (cdr exps))
      (let ([leftArg (match arg
                       [(list 'fun (cons arg1 tail) body) (parse arg)]
                       [(list arg1 exps1 ...) (appFunctionParserLazy arg1 exps1)]
                       [else (parse arg)]
                       )])
        (appL leftArg (parse (car exps)))
        )
      (appFunctionParserLazy (list arg (car exps)) (cdr exps))
      )
  )

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
    [(list 'lenStr str) (oneArgPrim 'lenStr (parse str) )]
    [(list 'strRef args ...) (parsePrimitiveArgs 'strRef args)]
    [(list 'list args ...) (listHandler args) ]
    [(list 'delay expr) (delay (parse expr)) ]
    [(list 'force promise) (force (parse promise))]
    [(list 'car list) (Zcar (parse list))]
    [(list 'cdr list) (Zcdr (parse list))]
    [(list 'take list n) (take (parse list) (parse n))]
    [(list 'empty) (mtList)]
    [(list 'if-tf c et ef) (if-tf (parse c) (parse et) (parse ef))]
    [(list 'with (cons (list x e) tail) b) (if (empty? tail)(app (fun x (parse b)) (parse e)) (app (fun x (parse (list 'with tail b))) (parse e)))]
    [(list 'with (list x e) b) (app (fun x (parse b)) (parse e))]
    
    [(list 'newbox b) (newbox (parse b))]
    [(list 'openbox e) (openbox (parse e))]
    [(list 'setbox b v) (setbox (parse b) (parse v))]
    [(list 'seqn e1 e2) (seqn (parse e1) (parse e2))]
    [(list 'fun (cons arg tail) body) (if (empty? tail) (fun  arg (parse body)) (fun  arg (parse (list 'fun tail body))))]
    [(list 'rec (list id function) b)
     (parse `{with {,id {Y (fun (,id) ,function)}} ,b})]
    [(list 'lazy arg exps ...) (appFunctionParserLazy arg exps)]
    [(list arg exps ...) (appFunctionParser arg exps)]
    
    
    )
  )

(deftype Val
  (valV v) ; numero, booleano, string, byte, etc.
  (promiseV expr env)
  (closureV arg body env) ; closure = fun + env
  (v*s val sto)
  (boxV loc)
  )
; strict :: v*s  -> v*s
; Fuerza la evaluacion de las promesas
(define (strict valSto )
  (match valSto
    [(v*s (promiseV e env) sto ) (strict (interp e env sto))]
    [else valSto]
    )
  )
; getPrimitive :: primitiveId  -> procedure
; Devuelve el procedimiento de la primitiva
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


; interp :: Expr  Env Sto -> Val
; interpreta una expresion
(define (interp expr env sto)
  (match expr
    [(num n) (v*s (valV n) sto)]
    [(bool b) (v*s (valV b) sto)]
    [(str s) (v*s (valV s) sto)]
    [(mtList) (v*s (valV '()) sto)]
    [(list1 f r)
     (def (v*s f-val f-sto) (strict (interp f env sto)))
     (def (v*s r-val r-sto) (strict (interp r env f-sto)))
     (v*s (valV (Zcons f-val r-val)) sto)]
    [(Zcar l)
     (def (v*s (valV (Zcons f-val r-val)) l-sto) (strict (interp l env sto))) 
     (v*s f-val sto)
     ]
    [(Zcdr l)
     (def (v*s (valV (Zcons f-val r-val)) l-sto) (interp l env sto)) 
     (v*s r-val sto)
     ]
    [(take l n)
     
     (def (v*s (valV (Zcons f-val r-val)) l-sto) (strict (interp l env sto)))
     (def (v*s (valV n-val) n-sto) (strict (interp n env l-sto)))
     (if (eq? n-val 0)
         (v*s f-val n-sto)
         (if (empty?(valV-v r-val))
             (error "Index not found")
             (interp (take r-val (valV (- n-val 1))) env n-sto)))
     ]
    [(fun arg body)(v*s (closureV arg body env) sto)]
    [(id x) (v*s (sto-lookup (env-lookup x env) sto) sto)]
    
    [(prim operation l r)
     
     (def (v*s l-val l-sto) (strict (interp l env sto)))
     (def (v*s r-val r-sto) (strict (interp r env l-sto)))
     (v*s (valVOperation (getPrimitive operation) l-val r-val) r-sto)]
    
    [(oneArgPrim operation v)
     (def (v*s val v-sto) (interp v env sto))
     (v*s (valVOperation1Arg (getPrimitive operation) val ) v-sto)
     ]
    
    [(if-tf c et ef)
     (def (v*s cond-val cond-sto) (interp c env sto))
     (if (valV-v cond-val)
         (interp et env cond-sto) 
         (interp ef env cond-sto))]
    [(appL f e)
     (def (v*s (closureV arg body fenv) fSto) (interp f env sto))
     (def new-loc (malloc fSto))
     (interp body (extend-env arg new-loc fenv) (extend-sto new-loc (promiseV e env) fSto))] 
    [(app f e)
     (def (v*s (closureV arg body fenv) fSto) (interp f env sto))
     (def (v*s exp-val exp-sto) (interp e env fSto))
     (def new-loc (malloc exp-sto))
     (interp body (extend-env arg new-loc fenv) (extend-sto new-loc exp-val exp-sto))]
    [(delay expr) (v*s (promiseV expr env) sto)]
    [(force promise)
     (def (v*s (promiseV expr-p env-p) exp-sto) (interp promise env sto))
     
     (interp expr-p env-p exp-sto)]
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
    [(valV exp) (v*s expr sto)]

    ))
; malloc : sto -> loc
; devuelve un loc de memoria en el storage
(define (malloc sto)
  (match sto
    [(mtSto) 0]
    [(aSto loc _ tail) (+ 1 (malloc tail))]
    )
  )

; valVOperation : procedure,Val,val -> Val
; ejecuta primitivas de 2 argumentos
(define (valVOperation op s1 s2)
  (valV (op (valV-v s1) (valV-v s2)))
  
  )
; valVOperation : procedure,Val -> Val
; ejecuta primitivas de 1 argumento
(define (valVOperation1Arg op s1)
  (valV (op (valV-v s1) ))
  )




; envWithY  -> env
; devuelve un env con el id Y apuntando al loc 0
(define envWithY (aEnv 'Y  0 (mtEnv)))
; stoWithY  -> sto
; devuelve un storage con el combinador Y
(define (stoWithY)
  
  (def (v*s val sto) (interp (parse '{fun {f}
                                          {with {h {fun {g}
                                                        {fun {n}
                                                             {{f {g g}} n}}}}
                                                {h h}}}) (mtEnv) (mtSto))) 
  (aSto 0 val (mtSto)))

; printArray (Zcons f l) -> void
; imprime el array de forma mas amigable
(define (printArray mainArray)
  (display "'(")
  (letrec ([iterateOverArray (λ (arr) (match (valV-v arr)
                                        [(Zcons first last) (if (empty? (valV-v last))
                                                                (display (valV-v first))
                                                                (begin (display (valV-v first)) (display " ") (iterateOverArray last))
                                                                )]
                                        ))])
    (iterateOverArray mainArray)
    )
  (display ")\n")
  )

#|
<Type> ::= (Num)
          | (Bool) | (Str)
|#
(deftype Type
  (Num)
  (Bool)
  (Str)
  )

;typeof: expr -> type/error
;se encarga de realizar el checkeo de tipos en el lenguaje
(define (typeof expr)
  (define (check-num-type l r)
    
    (if (and  (Num? (typeof l) )
              (Num? (typeof r) ))
        (Num)
        (error "type error")))
  (define (check-str-type l r)
    (if (and (Str? (typeof l)) 
             (Str? (typeof r)) )
        (Str)
        (error "type error")))

  (match expr
    [(num n) (Num)]
    [(bool b) (Bool)]
    [(str s) (Str)]
    [(prim '+ l r) (check-num-type l r)]
    [(prim '* l r) (check-num-type l r)]
    [(prim '/ l r) (check-num-type l r)]
    [(prim '- l r) (check-num-type l r)]
    [(prim '< l r) (check-num-type l r)]
    [(prim '<= l r) (check-num-type l r)]
    [(prim '> l r) (check-num-type l r)]
    [(prim '>= l r) (check-num-type l r)]
    [(prim 'appendStr l r) (check-str-type l r)]
    [(oneArgPrim 'lenStr l) (if  (Str? (typeof l))
                                 (Str)
                                 (error "type error"))]
    [(prim 'strRef s n)
     (if (and (Str? (typeof s)) (Num? (typeof n)))
         (Str)
         (error "type error"))]
    [(fun arg body) (typeof body)]
    
    [(app f e)
     (typeof f)
     ]
    [else "Type Checker not defined"]
    
    )
  )
; constantPropagationEnvLookUp :: <id> <env> -> <val>
; buscar el valor de una variable dentro del ambiete, a diferencia del env-lookup normal no tira error
(define (constantPropagationEnvLookUp x env)
  (match env
    [(mtEnv) (id x)]
    [(aEnv id val tail)(if (eq? id x) val (constantPropagationEnvLookUp x tail))]
    )
  )
; constant-propagation :: expr <env> <sto> -> expr
; Funcion que sirve para realizar el checkeo cuando existen constantes, si hay una constante la reemplaza en el lugar donde va la misma
; ex. (with {x 3} (+ x x))->(with {x 3} (+ 3 3))
(define (constant-propagation expr [env (mtEnv)] [sto (mtSto)])
  (match expr
    [(num n) (num n)]
    [(bool b) (bool b)]
    [(id x) (let ([envAns (constantPropagationEnvLookUp x env)])
              (if (id? envAns)
                  envAns
                  (sto-lookup (env-lookup x env) sto))
              )]
    [(prim prim-name l r)
     (prim prim-name (constant-propagation l env sto) (constant-propagation r env sto))]
    
    [(if-tf c et ef) (if-tf (constant-propagation c env sto)
                            (constant-propagation et env sto)
                            (constant-propagation ef env sto))]
    [(fun arg body) (fun arg body)]
    
    [(app f e)

     (letrec ([propagateApp (λ (f args env sto)
                              (match f
                                [(fun arg body)
                                 
                                 (match body
                                   [(fun arg2 body2)
                                    
                                    (def new-loc (malloc sto))
                                    (fun arg (propagateApp body (cdr args) (extend-env arg new-loc env) (extend-sto new-loc (car args) sto)))
                                    ]
                                   [else
                                    
                                    (def new-loc (malloc sto))
                                    (constant-propagation body (extend-env arg new-loc env) (extend-sto new-loc (car args) sto))])
                                   
                                 ]
                                [(app f2 e2)
                                 (app (propagateApp f2 (cons (constant-propagation e2 env sto) args) env sto) e2)]
                                [(id name)

                                 
                                 (propagateApp (sto-lookup (constantPropagationEnvLookUp name env) sto) args env sto)]

                                ))])
       (propagateApp f (list (constant-propagation e env sto)) env sto)
       )
     
     ]
    [else expr]
    )
  )

; run: Src -> Src
; corre un programa
(define (runWithTypeChecker prog)
  
  (let* ([expr (parse prog)]
         [constantProp (constant-propagation expr envWithY (stoWithY))]
         [t (typeof constantProp)])
    
    (def (v*s res sto) (interp expr envWithY (stoWithY)))
    (match res
      [(valV (Zcons first last)) (printArray res)]
      [(valV v) v]
      [(promiseV expr env) res]
      [(closureV arg body env) res]
      [(boxV loc) res])
    )
  
  )
; run: Src -> Src
; corre un programa
(define (runWithoutTypeChecker prog)
  
  (let* ([expr (parse prog)]
         )
    
    (def (v*s res sto) (interp expr envWithY (stoWithY)))
    (match res
      [(valV (Zcons first last)) (printArray res)]
      [(valV v) v]
      [(promiseV expr env) res]
      [(closureV arg body env) res]
      [(boxV loc) res])
    )
  
  )
; run: Src -> Src
; corre un programa pero muestra el storage
(define (runToCheckLazy prog)
  (let* ([expr (parse prog)]
         [t (typeof expr)])
    (def (v*s res sto) (interp expr envWithY (stoWithY)))
    (print sto)
    (match res
      [(valV (Zcons first last)) (printArray res)]
      [(valV v) v]
      [(promiseV expr env) res]
      [(closureV arg body env) res]
      [(boxV loc) res])
    )

  )
;Pruebas If -----------------------------------------------
(test (runWithTypeChecker '(if-tf (== 3 2) "fue true" "fue false")) "fue false")
(test (runWithTypeChecker '(if-tf (== 3 3) "fue true" "fue false")) "fue true")
;Pruebas strings---------------------------------------------
(test (runWithTypeChecker '"soy un string") "soy un string")
(test (runWithTypeChecker '(appendStr "string 1 " "string 2") )"string 1 string 2")
(test (runWithTypeChecker '(appendStr "string 1 " "string 2 " "string 3") )"string 1 string 2 string 3")
(test (runWithTypeChecker '(lenStr (appendStr "string 1 " "string 2 " "string 3"))) 26)
(test (runWithTypeChecker '(strRef (appendStr "string 1 " "string 2 " "string 3") 1)) #\t)
(test (runWithTypeChecker '(strRef (appendStr "string 1 " "string 2 " "string 3") 0)) #\s)
(test (runWithTypeChecker '(strRef (appendStr "string 1 " "string 2 " "string 3") 7)) #\1)
;(parse '(lenStr (appendStr "string 1 " "string 2 " "string 3")))

(runWithTypeChecker '{list (+ 3 5) 1 3})
(test (runWithTypeChecker '(car {list (+ 68 1) 1 3})) 69)
(runWithTypeChecker '(cdr {list (+ 68 1) 1 3}))
(test (runWithTypeChecker '(car (cdr {list (+ 68 1) 1 3}))) 1)

(test (runWithTypeChecker '(empty)) '())
(test (runWithTypeChecker '(take {list (+ 68 1) 1 3} 0)) 69)
(test (runWithTypeChecker '(take {list (+ 68 1) 1 3} 1)) 1)
(test (runWithTypeChecker '(take {list (+ 68 1) 1 3} 2)) 3)
(test/exn (runWithTypeChecker '(take {list (+ 68 1) 1 3} 3)) "Index not found")

;N argumentos en funciones --------------------------
(test (runWithoutTypeChecker '{{fun (a) {+ a 2}} 3}) 5)
(test (runWithoutTypeChecker '{{fun (a b) {+ a b}} 1 4}) 5)
(test (runWithoutTypeChecker '{{fun (a b c) {+ a {- b c}}} 3 2 1}) 4)

(test (runWithoutTypeChecker '{{fun (a b c d e f g) {+ a {- b c}}} 3 2 1 1 5 8 7}) 4)

; prueba funciones con N args dentro de with -----------------
(test (runWithoutTypeChecker '{with {add {fun {a b c} {+ a {+ b c}}}} {+ {add 2 3 5 } {add 4 5 6}}}) 25)

; Pruebas delay force ---------------------------------------
(test (runWithoutTypeChecker '{delay (+ 5 5)}) (promiseV (prim '+ (num 5) (num 5)) (aEnv 'Y 0 (mtEnv))))
(test (runWithoutTypeChecker'{force {delay (+ 5 5)}}) 10)
(test (runWithoutTypeChecker '(with {a (delay (* 5 5))} (force a))) 25)

;Pruebas rec  ---------------------------------------
(test (runWithoutTypeChecker '{rec {sum {fun {n}
                                             {if-tf {== 0 n} 0 {+ n {sum {- n 1}}}}}} {sum 5}}) 15)
(test (runWithoutTypeChecker '{rec {sum {fun {n}
                                             {if-tf {== 0 n} 0 {+ n {sum {- n 1}}}}}} {sum 3}}) 6)
(test (runWithoutTypeChecker '{rec {fact {fun {n}
                                              {if-tf {== 0 n} 1 {* n {fact {- n 1}}}}}} {fact 4}}) 24)


(test (runWithoutTypeChecker '{rec {mult0 {fun {n1 n2}
                             
                                               {if-tf {== n1 0} 0 {+ (* n1 n2) {mult0 (- n1 1) n2}}}}
                                          } {mult0 4 3}}) 30)
;Pruebas lazy  ---------------------------------------
;(display "Showing storage of lazy function\n")
;(test (runToCheckLazy '{lazy {fun (a b) {+ b 2}} (+ 1 5) (+ 2 3)}) 7)
;(display "\n")
(display "Showing storage of lazy function\n")
(test (runToCheckLazy '{lazy {fun (a c b) {+ b 2}} (+ 1 5) #f (+ 2 3) }) 7)
(display "\n")


;-------------------------------------------------------Pruebas base

(test (runWithTypeChecker '{* -2 3 4}) -24)
(test (runWithTypeChecker '{+ 3 4}) 7)
(test (runWithTypeChecker '{- 5 1}) 4)
(test (runWithTypeChecker '{+ 3 4}) 7)
(test (runWithTypeChecker '{- 5 1}) 4)
(test (runWithTypeChecker '{+ 1 2 3 4}) 10)
(test (runWithTypeChecker '{* 2 3 4}) 24)
(test (runWithTypeChecker '{/ 12 2 2}) 3)
(test (runWithTypeChecker '{< 12 3}) #f)
(test (runWithTypeChecker '{<= 12 3}) #f)
(test (runWithTypeChecker '{< 12 12}) #f)
(test (runWithTypeChecker '{<= 12 12}) #t)
(test (runWithTypeChecker '{> 12 3}) #t)
(test (runWithTypeChecker '{>= 12 3}) #t)
(test (runWithTypeChecker '{> 12 12}) #f)
(test (runWithTypeChecker '{>= 12 12}) #t)
(test (runWithTypeChecker '{>= 12 12}) #t)
(test (runWithTypeChecker '{== 12 12}) #t)
(test (runWithTypeChecker '{== 12 11}) #f)
(test (runWithTypeChecker '{!= 12 12}) #f)
(test (runWithTypeChecker '{!= 12 11}) #t)
(test (runWithTypeChecker '{&& 12 11}) 11)
(test (runWithTypeChecker '{&& #f #t}) #f)
(test (runWithTypeChecker '{|| #f #t}) #t)
(test (runWithTypeChecker '{|| 12 11}) 12)
(test (runWithTypeChecker '{with {x 3} 2}) 2)
(test (runWithTypeChecker '{with {x 3} x}) 3)
(test (runWithTypeChecker '{with {x 3} {with {y 4} x}}) 3)
(test (runWithTypeChecker '{with {x 3} {+ x 4}}) 7)
(test (runWithTypeChecker '{with {x 3} {with {x 10} {+ x x}}}) 20)
(test (runWithTypeChecker '{with {x 3} {with {x x} {+ x x}}}) 6)
(test (runWithTypeChecker '{with {x 3} {with {y 2} {+ x y}}}) 5)
(test (runWithTypeChecker '{with {x 3} {+ 1 {with {y 2} {+ x y}}}}) 6)
(test (runWithTypeChecker '{with {x 3} {with {y {+ 2 x}} {+ x y}}}) 8)
(test (runWithTypeChecker '{* 1 1 1 1}) 1)
(test/exn (runWithTypeChecker '{* 1 #t 1 1}) "type error")
(test/exn (runWithTypeChecker '{with {x #t} {* 1 x x x}}) "type error")
(test/exn (runWithTypeChecker '{with {x #t} {* x x x x}}) "type error")
(test/exn (runWithTypeChecker '(appendStr "string 1 " 2) )"type error")
(test/exn (runWithTypeChecker '(lenStr 5)) "type error")
(test (runWithTypeChecker '{with {x 3} {+ x x}}) 6)
(test (runWithTypeChecker '{with {x 3} {with {y 2} {+ x y}}}) 5)
(test (runWithTypeChecker '{with {{x 3} {y 2}} {+ x y}}) 5)
(test (runWithTypeChecker '{with {{x 3} {x 5}} {+ x x}}) 10)
(test (runWithTypeChecker '{with {{x 3} {y {+ x 3}}} {+ x y}}) 9)
(test (runWithTypeChecker '{with {{x 10} {y 2} {z 3}} {+ x {+ y z}}}) 15)
(test (runWithTypeChecker '{with {x 3} {if-tf {+ x 1} {+ x 3} {+ x 9}}}) 6)
(test/exn (runWithTypeChecker '{f 10}) "undefined")
(test (runWithTypeChecker '{with {f {fun {x} {+ x x}}}{f 10}}) 20)
(test (runWithTypeChecker '{{fun {x} {+ x x}} 10}) 20)
(test (runWithTypeChecker '{with {add1 {fun {x} {+ x 1}}}{add1 {add1 {add1 10}}}}) 13)
(test (runWithTypeChecker '{with {add1 {fun {x} {+ x 1}}}
                                 {with {foo {fun {x} {+ {add1 x} {add1 x}}}}
                                       {foo 10}}}) 22)
(test (runWithTypeChecker '{with {add1 {fun {x} {+ x 1}}}
                                 {with {foo {fun {f} {+ {f 10} {f 10}}}}
                                       {foo add1}}}) 22)
(test (runWithTypeChecker '{{fun {x}{+ x 1}} {+ 2 3}}) 6)
(test (runWithTypeChecker '{with {apply10 {fun {f} {f 10}}}
                                 {with {add1 {fun {x} {+ x 1}}}
                                       {apply10 add1}}}) 11)

(test (runWithTypeChecker '{with {addN {fun {n}
                                            {fun {x} {+ x n}}}}
                                 {{addN 10} 20}}) 30)


;Pregunta 6
;por defecto en la forma que esta nuestro lenguaje no da ya que usa el env con el que se guardo la promesa, si no fuera asi, si se podria

(test/exn (runWithTypeChecker '(with {ones (delay (list 1 ones))} (take ones 34))) "undefined:  'ones")
