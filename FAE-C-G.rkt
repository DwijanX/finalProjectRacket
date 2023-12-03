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
    [(mtSto) (error "segmentation fault:" l)]
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
    [(take l n)
     
     (def (v*s (valV (Zcons f-val r-val)) l-sto) (interp l env sto))
     (def (v*s (valV n-val) n-sto) (interp n env l-sto))
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
    [(force expr)
     (def (v*s (promiseV expr-p env-p) exp-sto) (interp expr env sto))
     
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

; run: Src -> Src
; corre un programa
(define (run prog)
  (def (v*s res sto) (interp (parse prog) envWithY (stoWithY)))
    (match res
      [(valV (Zcons first last)) (printArray res)]
      [(valV v) v]
      [(promiseV expr env) res]
      [(closureV arg body env) res]
      [(boxV loc) res])
  
    )
; run: Src -> Src
; corre un programa pero muestra el storage
(define (runToCheckLazy prog)
  
  (def (v*s res sto) (interp (parse prog) envWithY (stoWithY)))
   (display sto)
    (match res
      [(valV v) v]
      [(promiseV expr env) res]
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
(test (run '(car {list (+ 68 1) 1 3})) 69)
(run '(cdr {list (+ 68 1) 1 3}))
(test (run '(car (cdr {list (+ 68 1) 1 3}))) 1)

(test (run '(empty)) '())
(test (run '(take {list (+ 68 1) 1 3} 0)) 69)
(test (run '(take {list (+ 68 1) 1 3} 1)) 1)
(test (run '(take {list (+ 68 1) 1 3} 2)) 3)
(test/exn (run '(take {list (+ 68 1) 1 3} 3)) "Index not found")

;N argumentos en funciones --------------------------
(test (run '{{fun (a) {+ a 2}} 3}) 5)
(test (run '{{fun (a b) {+ a b}} 1 4}) 5)
(test (run '{{fun (a b c) {+ a {- b c}}} 3 2 1}) 4)

(test (run '{{fun (a b c d e f g) {+ a {- b c}}} 3 2 1 1 5 8 7}) 4)

; prueba funciones con N args dentro de with -----------------
(test (run '{with {add {fun {a b c} {+ a {+ b c}}}} {+ {add 2 3 5 } {add 4 5 6}}}) 25)

; Pruebas delay force ---------------------------------------
(test (run '{delay (+ 5 5)}) (promiseV (prim '+ (num 5) (num 5)) (aEnv 'Y 0 (mtEnv))))
(test (run'{force {delay (+ 5 5)}}) 10)
(test (run '(with {a (delay (* 5 5))} (force a))) 25)

;Pruebas rec  ---------------------------------------
(test (run '{rec {sum {fun {n}
                        {if-tf {== 0 n} 0 {+ n {sum {- n 1}}}}}} {sum 5}}) 15)
(test (run '{rec {sum {fun {n}
                        {if-tf {== 0 n} 0 {+ n {sum {- n 1}}}}}} {sum 3}}) 6)
(test (run '{rec {fact {fun {n}
                        {if-tf {== 0 n} 1 {* n {fact {- n 1}}}}}} {fact 4}}) 24)


(test (run '{rec {mult0 {fun {n1 n2}
                             
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



;Pregunta 6
;por defecto en la forma que esta nuestro lenguaje no da ya que usa el env con el que se guardo la promesa, si no fuera asi, si se podria

(test/exn (run '(with {ones (delay (list 1 ones))} (take ones 34))) "undefined:  'ones")
