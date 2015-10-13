;    Initialization file for TinySCHEME 1.41
;    注释者：xuegang (qq:308821698 blog: http://www.cppblog.com/flysnowxg)

; Per R5RS, up to four deep compositions should be defined
(define (caar x) (car (car x)))
(define (cadr x) (car (cdr x)))
(define (cdar x) (cdr (car x)))
(define (cddr x) (cdr (cdr x)))
(define (caaar x) (car (car (car x))))
(define (caadr x) (car (car (cdr x))))
(define (cadar x) (car (cdr (car x))))
(define (caddr x) (car (cdr (cdr x))))
(define (cdaar x) (cdr (car (car x))))
(define (cdadr x) (cdr (car (cdr x))))
(define (cddar x) (cdr (cdr (car x))))
(define (cdddr x) (cdr (cdr (cdr x))))
(define (caaaar x) (car (car (car (car x)))))
(define (caaadr x) (car (car (car (cdr x)))))
(define (caadar x) (car (car (cdr (car x)))))
(define (caaddr x) (car (car (cdr (cdr x)))))
(define (cadaar x) (car (cdr (car (car x)))))
(define (cadadr x) (car (cdr (car (cdr x)))))
(define (caddar x) (car (cdr (cdr (car x)))))
(define (cadddr x) (car (cdr (cdr (cdr x)))))
(define (cdaaar x) (cdr (car (car (car x)))))
(define (cdaadr x) (cdr (car (car (cdr x)))))
(define (cdadar x) (cdr (car (cdr (car x)))))
(define (cdaddr x) (cdr (car (cdr (cdr x)))))
(define (cddaar x) (cdr (cdr (car (car x)))))
(define (cddadr x) (cdr (cdr (car (cdr x)))))
(define (cdddar x) (cdr (cdr (cdr (car x)))))
(define (cddddr x) (cdr (cdr (cdr (cdr x)))))

;;;; Utility to ease macro creation
;例子 (macro m (lambda (arg) `(,(cadr arg) 1 2)))
;     (macro-expand '(m +))
(define (macro-expand form)
     ((eval (get-closure-code (eval (car form)))) form))

;用于宏的递归展开（当对一个列表调用的结果是宏调用时 需要用这个递归展开）
(define (macro-expand-all form)
   (if (macro? form)
      (macro-expand-all (macro-expand form))
      form))

(define *compile-hook* macro-expand-all)

(macro (unless form)
     `(if (not ,(cadr form)) (begin ,@(cddr form))))

(macro (when form)
     `(if ,(cadr form) (begin ,@(cddr form))))

; DEFINE-MACRO Contributed by Andy Gaynor
; macro除了接收macro的原始形式，还接收下面这种形式
; 例子 (define-macro (m f) `(,f 1 2))  
;      要变换成这样 (macro (m gensym-xxx) (apply (lambda (f) `(,f 1 2)) (cdr gensym-xxx)))
;      实际的调用会像是这样： （m +) ，这里的（m +)会传递给gensym-xxx
(macro (define-macro dform)
  (if (symbol? (cadr dform))
    `(macro ,@(cdr dform))
    (let ((form (gensym)))
      `(macro (,(caadr dform) ,form)
         (apply (lambda ,(cdadr dform) ,@(cddr dform)) (cdr ,form))))))

; Utilities for math. Notice that inexact->exact is primitive,
; but exact->inexact is not.
(define exact? integer?)
(define (inexact? x) (and (real? x) (not (integer? x))))
(define (even? n) (= (remainder n 2) 0))		;是否是偶数
(define (odd? n) (not (= (remainder n 2) 0)))	;是否是奇数
(define (zero? n) (= n 0))		;是否为0
(define (positive? n) (> n 0))	;是否为正
(define (negative? n) (< n 0))	;是否为负
(define complex? number?)
(define rational? real?)
(define (abs n) (if (>= n 0) n (- n)))	;求绝对值
(define (exact->inexact n) (* n 1.0))
(define (<> n1 n2) (not (= n1 n2)))

; min and max must return inexact if any arg is inexact; use (+ n 0.0)
(define (max . lst)	;求最大值 （foldr定义在后面）
  (foldr (lambda (a b)
           (if (> a b)
             (if (exact? b) a (+ a 0.0))
             (if (exact? a) b (+ b 0.0))))
         (car lst) (cdr lst)))
(define (min . lst)	;求最小值
  (foldr (lambda (a b)
           (if (< a b)
             (if (exact? b) a (+ a 0.0))
             (if (exact? a) b (+ b 0.0))))
         (car lst) (cdr lst)))

(define (succ x) (+ x 1))	;加1
(define (pred x) (- x 1))	;减1

(define gcd  ;求最大公约数 经典算法
  (lambda a
    (if (null? a)
      0
      (let ((aa (abs (car a)))
            (bb (abs (cadr a))))
         (if (= bb 0)
              aa
              (gcd bb (remainder aa bb)))))))
			  
(define lcm		;求最小公倍数 
;  假设 aa = kk * mm  , bb = kk *nn  其中 kk 是aa 和bb 的最大公约数，
;  那么mm和nn一定没有大于1的公因子，如果有，kk就不是最大公约数了
;  那么 rr = kk * mm * nn = aa * bb / kk 一定aa 和bb的公倍数
;  那么 kk * mm * nn是最小公倍数吗？ 
;  假设xx是kk的质因子 ，那么nn必须有质因子xx才能保证 rr/xx是aa的倍数 ，同时mm也必须有质因子xx才能保证 rr/xx是bb的倍数 ，
;      这导致mm 和nn有大于1的公因子 这与前面推出的结论矛盾
;  假设xx是mm的质因子，显然nn中没有质因子xx，那么 rr/xx就不是aa的倍数了 
;  假设xx是nn的质因子，显然mm中没有质因子xx，那么 rr/xx就不是bb的倍数了
;  所以rr是最小公倍数（大体思路如此，中间省略了一些推理步骤）
  (lambda a
    (if (null? a)
      1
      (let ((aa (abs (car a)))
            (bb (abs (cadr a))))
         (if (or (= aa 0) (= bb 0))
             0
             (abs (* (quotient aa (gcd aa bb)) bb)))))))

;将字符列表转化为字符串
(define (string . charlist)
     (list->string charlist))
;将字符列表转化为字符串
(define (list->string charlist)
     (let* ((len (length charlist))
            (newstr (make-string len))
            (fill-string!
               (lambda (str i len charlist)
                    (if (= i len)
                         str
                         (begin (string-set! str i (car charlist))
                         (fill-string! str (+ i 1) len (cdr charlist)))))))
          (fill-string! newstr 0 len charlist)))
;将字符列表转化为字符串（尾递归版本）
(define (string-fill! s e)
     (let ((n (string-length s)))
          (let loop ((i 0))
               (if (= i n)
                    s
                    (begin (string-set! s i e) (loop (succ i)))))))
;将字符串转换为字符列表（尾递归版本）
(define (string->list s)
     (let loop ((n (pred (string-length s))) (l '()))
          (if (= n -1)
               l
               (loop (pred n) (cons (string-ref s n) l)))))
;拷贝字符串
(define (string-copy str)
     (string-append str))

(define (string->anyatom str pred)
     (let* ((a (string->atom str)))
       (if (pred a) a
         (error "string->xxx: not a xxx" a))))
		 
(define (anyatom->string n pred)
  (if (pred n)
      (atom->string n)
      (error "xxx->string: not a xxx" n)))
	  
;将字符串转换为数字
(define (string->number str . base) ;base说明了str表示的数字的进制
    (let ((n (string->atom str (if (null? base) 10 (car base)))))
        (if (number? n) n #f)))
		
;将数字转换为字符串
(define (number->string n . base)
    (atom->string n (if (null? base) 10 (car base))))

;字符的比较 （cmp是比较函数）
(define (char-cmp? cmp a b)
     (cmp (char->integer a) (char->integer b)))
;字符的比较（cmp是比较函数 忽略大小写）
(define (char-ci-cmp? cmp a b)
     (cmp (char->integer (char-downcase a)) (char->integer (char-downcase b))))

(define (char=? a b) (char-cmp? = a b))
(define (char<? a b) (char-cmp? < a b))
(define (char>? a b) (char-cmp? > a b))
(define (char<=? a b) (char-cmp? <= a b))
(define (char>=? a b) (char-cmp? >= a b))

(define (char-ci=? a b) (char-ci-cmp? = a b))
(define (char-ci<? a b) (char-ci-cmp? < a b))
(define (char-ci>? a b) (char-ci-cmp? > a b))
(define (char-ci<=? a b) (char-ci-cmp? <= a b))
(define (char-ci>=? a b) (char-ci-cmp? >= a b))

;字符串比较
; Note the trick of returning (cmp x y)
(define (string-cmp? chcmp cmp a b)
     (let ((na (string-length a)) (nb (string-length b)))
          (let loop ((i 0))
               (cond
                    ((= i na)
                         (if (= i nb) (cmp 0 0) (cmp 0 1)))
                    ((= i nb)
                         (cmp 1 0))
                    ((chcmp = (string-ref a i) (string-ref b i))
                         (loop (succ i)))	;如果相等，继续比较下一个字符
                    (else      ;如果不等，返回这两个字符的比较结果
                         (chcmp cmp (string-ref a i) (string-ref b i)))))))	

(define (string=? a b) (string-cmp? char-cmp? = a b))
(define (string<? a b) (string-cmp? char-cmp? < a b))
(define (string>? a b) (string-cmp? char-cmp? > a b))
(define (string<=? a b) (string-cmp? char-cmp? <= a b))
(define (string>=? a b) (string-cmp? char-cmp? >= a b))

(define (string-ci=? a b) (string-cmp? char-ci-cmp? = a b))
(define (string-ci<? a b) (string-cmp? char-ci-cmp? < a b))
(define (string-ci>? a b) (string-cmp? char-ci-cmp? > a b))
(define (string-ci<=? a b) (string-cmp? char-ci-cmp? <= a b))
(define (string-ci>=? a b) (string-cmp? char-ci-cmp? >= a b))

(define (list . x) x)
;foldr是一个递归遍历参数并调用函数f的辅助函数
(define (foldr f x lst)
     (if (null? lst)
          x
          (foldr f (f x (car lst)) (cdr lst))))

;例子 (unzip1-with-cdr '(1 2 3) '(4 5 6) '(7 8 9))  => ((1 4 7) (2 3) (5 6) (8 9))
(define (unzip1-with-cdr . lists)
  (unzip1-with-cdr-iterative lists '() '()))

(define (unzip1-with-cdr-iterative lists cars cdrs)
  (if (null? lists)
      (cons cars cdrs)
      (let ((car1 (caar lists))
            (cdr1 (cdar lists)))
        (unzip1-with-cdr-iterative
          (cdr lists)
          (append cars (list car1))
          (append cdrs (list cdr1))))))

;例子 (map + '(1 2 3) '(4 5 6) '(7 8 9))  => (12 15 18)
(define (map proc . lists)
  (if (null? lists)
      (apply proc)
      (if (null? (car lists))
        '()
        (let* ((unz (apply unzip1-with-cdr lists))
               (cars (car unz))
               (cdrs (cdr unz)))
          (cons (apply proc cars) (apply map (cons proc cdrs)))))))
;for-each和map很相似，就是最后一句不同，map把所有返回值都组合到一个链表返回，而for-each都丢弃了
;例子
;(define displayx 
;	(lambda arg 
;		(display (car arg)) 
;		(if (null? (cdr arg)) 
;			(newline) 
;			(apply displayx (cdr arg)))))			
;(for-each displayx '(1 2 3 ) '(4 5 6) '(7 8 9))  
(define (for-each proc . lists)
  (if (null? lists)
      (apply proc)
      (if (null? (car lists))
        #t
        (let* ((unz (apply unzip1-with-cdr lists))
               (cars (car unz))
               (cdrs (cdr unz)))
          (apply proc cars) (apply map (cons proc cdrs))))))
;例子(list-tail '(1 2 3 4) 2)  => (3 4)
(define (list-tail x k)
    (if (zero? k)
        x
        (list-tail (cdr x) (- k 1))))
;例子(list-ref '(1 2 3 4) 2)  => 3
(define (list-ref x k)
    (car (list-tail x k)))
;例子(last-pair '(1 2 3 4 5)) => (5)
(define (last-pair x)
    (if (pair? (cdr x))
        (last-pair (cdr x))
        x))

(define (head stream) (car stream))

(define (tail stream) (force (cdr stream)))

(define (vector-equal? x y)
     (and (vector? x) (vector? y) (= (vector-length x) (vector-length y))
          (let ((n (vector-length x)))
               (let loop ((i 0))
                    (if (= i n)
                         #t
                         (and (equal? (vector-ref x i) (vector-ref y i))
                              (loop (succ i))))))))
;例子(list->vector '(1 2)) =>#(1 2)
(define (list->vector x)
     (apply vector x))
;填充数组
(define (vector-fill! v e)
     (let ((n (vector-length v)))
          (let loop ((i 0))
               (if (= i n)
                    v
                    (begin (vector-set! v i e) (loop (succ i)))))))
;例子(vector->list #(1 2)) =>(1 2)
(define (vector->list v)
     (let loop ((n (pred (vector-length v))) (l '()))
          (if (= n -1)
               l
               (loop (pred n) (cons (vector-ref v n) l)))))

;; The following quasiquote macro is due to Eric S. Tiedemann.
;;   Copyright 1988 by Eric S. Tiedemann; all rights reserved.
;; Subsequently modified to handle vectors: D. Souflis
;准引用求值
(macro
 quasiquote
 (lambda (l)
   (define (mcons f l r)
     (if (and (pair? r)
              (eq? (car r) 'quote)
              (eq? (car (cdr r)) (cdr f))
              (pair? l)
              (eq? (car l) 'quote)
              (eq? (car (cdr l)) (car f)))
         (if (or (procedure? f) (number? f) (string? f))
               f
               (list 'quote f))
         (if (eqv? l vector)	;有这个if表达式就够了，外层的的那个if表达式不是必需的
               (apply l (eval r))
               (list 'cons l r)
               )))
   (define (mappend f l r)		;合并两个列表，这个函数有(list 'append l r)这句代码就够了
     (if (or (null? (cdr f))
             (and (pair? r)
                  (eq? (car r) 'quote)
                  (eq? (car (cdr r)) '())))
         l		;这个分支只是用于优化
         (list 'append l r)))
	;因为这个函数在宏里面被调用，所以这个函数的返回值会被再次求值，所以将一个表达式直接返回后会被求值一次!!!
	;foo总是会返回一个可求值的表达式!!!
   (define (foo level form)
     (cond 	((vector? form)		 ;新增加处理数组的分支,例如 (quasiquote #(,(+ 1 2))) =>#(3)
				(mcons form vector (foo level (vector->list form))))
			((not (pair? form))	;如果是原子类型，直接输出就行
               (if (or (procedure? form) (number? form) (string? form))
                    form		;原子类型的输出，例子 (quasiquote 0) => 0
                    (list 'quote form)))		;原子类型的输出，例子 (quasiquote #(0)) => #(0)
           ((eq? 'quasiquote (car form))	;如果列表的第一元素是准引用符号
				(mcons form ''quasiquote (foo (+ level 1) (cdr form))))	;对quasiquote递归(level被递增），例子 (quasiquote `(0)) => ‘(0)
           (#t (if (zero? level)	;当level为0时
                   (cond ((eq? (car form) 'unquote) (car (cdr form)))  	;例子(quasiquote ,(list + 1 2))
																		;因为这是在一个宏里面，所以 (car (cdr form))的返回值会被再次求值
                         ((eq? (car form) 'unquote-splicing)
							(error "Unquote-splicing wasn't in a list:" form))	;例子(quasiquote ,@(list + 1 2))
                         ((and	(pair? (car form))
								(eq? (car (car form)) 'unquote-splicing))		;例子(quasiquote (,@(list + 1 2)))
							(mappend form (car (cdr (car form))) (foo level (cdr form))))
                         (#t (mcons form (foo level (car form))		;如果(car form)的返回值中还有quasiquote，会在本次quasiquote退出后递归求值
                                         (foo level (cdr form)))))	;递归求值剩余的部分
					;level大于1时
                   (cond ((eq? (car form) 'unquote)
                           (mcons form ''unquote (foo (- level 1) (cdr form))))
                         ((eq? (car form) 'unquote-splicing)
                           (mcons form ''unquote-splicing (foo (- level 1) (cdr form))))
                         (#t 
						   (mcons form (foo level (car form)) (foo level (cdr form)))))))))
   (foo 0 (car (cdr l)))))

;;;;;Helper for the dynamic-wind definition.  By Tom Breton (Tehom)
;返回两个链表中共享的部分
;共享链表尾部的例子
;(begin (define st '(3 4 5))
;	(define s1 (cons 1 (cons 2 st)))
;	(define s2 (cons 3 (cons 2 st)))
;	(shared-tail s1 s2))		=>(3 4 5)
;(shared-tail '(1 2 3 4 5) '(2 3 4 5)) => ()   虽然尾部的(3 4 5)对两个列表是相同的，但不是共享的
(define (shared-tail x y)
   (let ((len-x (length x))
         (len-y (length y)))
      (define (shared-tail-helper x y)
         (if
            (eq? x y)
            x
            (shared-tail-helper (cdr x) (cdr y))))
      (cond
         ((> len-x len-y)
            (shared-tail-helper
               (list-tail x (- len-x len-y))
               y))
         ((< len-x len-y)
            (shared-tail-helper
               x
               (list-tail y (- len-y len-x))))
         (#t (shared-tail-helper x y)))))

;;;;;Dynamic-wind by Tom Breton (Tehom)

;;Guarded because we must only eval this once, because doing so redefines call/cc in terms of old call/cc
(unless (defined? 'dynamic-wind)
   (let
      ;;These functions are defined in the context of a private list of pairs of before/after procs.
      (  (*active-windings* '())
         ;;We'll define some functions into the larger environment, so we need to know it.
         (outer-env (current-environment)))	;(current-environment)被调用时let的还没有建立新的环境，因此(current-environment)返回的是外层的环境

      ;;Poor-man's structure operations
      (define before-func car)
      (define after-func  cdr)
      (define make-winding cons)

      ;;Manage active windings
      (define (activate-winding! new) ;new是这样的形式 (fun1 . fun2)
         ((before-func new))	;这里就是为了调用fun1这个函数
         (set! *active-windings* (cons new *active-windings*))) ; 将new加入到*active-windings*形成的链表的表头
      (define (deactivate-top-winding!)
         (let ((old-top (car *active-windings*)))
            ;;Remove it from the list first so it's not active during its own exit.
            (set! *active-windings* (cdr *active-windings*))	;弹出*active-windings*首部的元素
            ((after-func old-top))))	;调用fun2

      (define (set-active-windings! new-ws)
		 ;new-ws和*active-windings*是相同性质的结构，这两个结构可能有相同的部分，
		 ;首先将吧*active-windings*中和new-us不同的部分弹出*active-windings*，然后将new-us中和*active-windings*不同的部分压入*active-windings*
         (unless (eq? new-ws *active-windings*)
            (let ((shared (shared-tail new-ws *active-windings*)))
               ;;Define the looping functions.
               ;;Exit the old list.  Do deeper ones last.  Don't do any shared ones.
               (define (pop-many)
                  (unless (eq? *active-windings* shared)
                     (deactivate-top-winding!)
                     (pop-many)))
               ;;Enter the new list.  Do deeper ones first so that the
               ;;deeper windings will already be active.  Don't do any shared ones.
               (define (push-many new-ws)
                  (unless (eq? new-ws shared)
                     (push-many (cdr new-ws))
                     (activate-winding! (car new-ws))))
               ;;Do it.
               (pop-many)
               (push-many new-ws))))

      ;;The definitions themselves. ;重新定义call-with-current-continuation
      (eval		;之所以用eval来求值是为了设定环境（最后的那个outer-env参数） ,
				;之所以用外部环境，是因为用当前环境定义的变量在当前环境退出后会被丢弃
         `(define call-with-current-continuation
             ;;It internally uses the built-in call/cc, so capture it.
             ,(let ((old-c/cc call-with-current-continuation))
                 (lambda (func)					;这个封装了call/cc
                    ;;Use old call/cc to get the continuation.
                    (old-c/cc
                       (lambda (continuation)	;这个封装了func
                          ;;Call func with not the continuation itself
                          ;;but a procedure that adjusts the active
                          ;;windings to what they were when we made
                          ;;this, and only then calls the continuation.
                          (func
                             (let ((current-ws *active-windings*))
                                (lambda (x)		;这个封装了延续
                                   (set-active-windings! current-ws)	;这句是什么用???
                                   (continuation x)))))))))
         outer-env)
      ;;We can't just say "define (dynamic-wind before thunk after)"
      ;;because the lambda it's defined to lives in this environment,
      ;;not in the global environment.
      (eval
         `(define dynamic-wind	;在thunk前后增加函数调用
             ,(lambda (before thunk after)
                 ;;Make a new winding
                 (activate-winding! (make-winding before after))
                 (let ((result (thunk)))
                    ;;Get rid of the new winding.
                    (deactivate-top-winding!)
                    ;;The return value is that of thunk.
                    result)))
         outer-env)))

(define call/cc call-with-current-continuation)


;;;;; atom? and equal? written by a.k

;;;; atom?
(define (atom? x)
  (not (pair? x)))

;;;;    equal?
(define (equal? x y)
     (cond
          ((pair? x)
               (and (pair? y)
                    (equal? (car x) (car y))
                    (equal? (cdr x) (cdr y))))
          ((vector? x)
               (and (vector? y) (vector-equal? x y)))
          ((string? x)
               (and (string? y) (string=? x y)))
          (else (eqv? x y))))

;;;; (do ((var init inc) ...) (endtest result ...) body ...)
;;
(macro do
  (lambda (do-macro)
    (apply (lambda (do vars endtest . body)
             (let ((do-loop (gensym)))
               `(letrec ((,do-loop
                           (lambda ,(map (lambda (x)
                                           (if (pair? x) (car x) x))
                                      `,vars)
                             (if ,(car endtest)
                               (begin ,@(cdr endtest))
                               (begin
                                 ,@body
                                 (,do-loop
                                   ,@(map (lambda (x)
                                            (cond
                                              ((not (pair? x)) x)
                                              ((< (length x) 3) (car x))
                                              (else (car (cdr (cdr x))))))
                                       `,vars)))))))
                  (,do-loop
                    ,@(map (lambda (x)
                             (if (and (pair? x) (cdr x))
                               (car (cdr x))
                               '()))
                        `,vars)))))
      do-macro)))

;;;; generic-member ;查找lst中查找和obj匹配的元素，并返回这个元素开始的列表
(define (generic-member cmp obj lst)
  (cond
    ((null? lst) #f)
    ((cmp obj (car lst)) lst)
    (else (generic-member cmp obj (cdr lst)))))

(define (memq obj lst)
     (generic-member eq? obj lst))
(define (memv obj lst)		;例子 (memv 3 '(2 4 3 4 5)) =>(3 4 5)
     (generic-member eqv? obj lst))
(define (member obj lst)	;例子 (member 3 '(2 4 3 4 5)) =>(3 4 5)
     (generic-member equal? obj lst))

;;;; generic-assoc ;查找lst中查找和obj匹配的元素，并返回这个元素（这个元素也是一个列表）
(define (generic-assoc cmp obj alst)
     (cond
          ((null? alst) #f)
          ((cmp obj (caar alst)) (car alst))
          (else (generic-assoc cmp obj (cdr alst)))))

(define (assq obj alst)
     (generic-assoc eq? obj alst))
(define (assv obj alst)		;例子 (assv  3 '((2) (3) (4))) =>(3)
     (generic-assoc eqv? obj alst))
(define (assoc obj alst)	;例子 (assoc  3 '((2) (3) (4))) =>(3)
     (generic-assoc equal? obj alst))

(define (acons x y z) (cons (cons x y) z))	

;;;; Handy for imperative programs
;;;; Used as: (define-with-return (foo x y) .... (return z) ...)
;类似其他语言里面的return语句的功能
(macro (define-with-return form)
     `(define ,(cadr form)
          (call/cc (lambda (return) ,@(cddr form)))))

;;;; Simple exception handling
;
;    Exceptions are caught as follows:
;
;         (catch (do-something to-recover and-return meaningful-value)
;              (if-something goes-wrong)
;              (with-these calls))
;
;    "Catch" establishes a scope spanning multiple call-frames
;    until another "catch" is encountered.
;
;    Exceptions are thrown with:
;
;         (throw "message")
;
;    If used outside a (catch ...), reverts to (error "message)

(define *handlers* (list))

(define (push-handler proc)
     (set! *handlers* (cons proc *handlers*)))

(define (pop-handler)
     (let ((h (car *handlers*)))
          (set! *handlers* (cdr *handlers*))
          h))

(define (more-handlers?)
     (pair? *handlers*))

(define (throw . x)
     (if (more-handlers?)
          (apply (pop-handler))
          (apply error x)))

;例子，没有异常时 (begin (display "a") (catch (display "b") (display "c")) (display "d"))	=> acd#t
;例子，有异常时 (begin (display "a") (catch (display "b") (displayx "c")) (display "d"))	=> abd#t
(macro (catch form)
     (let ((label (gensym)))
          `(call/cc (lambda (exit)
               (push-handler (lambda () (exit ,(cadr form)))) ;exit是一个延续 ，这里表示对异常处理代码进行调用以后返回到exit这个延续
               (let ((,label (begin ,@(cddr form))))
                    (pop-handler)
                    ,label)))))

(define *error-hook* throw)


;;;;; Definition of MAKE-ENVIRONMENT, to be used with two-argument EVAL
;创建一个环境，并在这个环境里面初始化一些变量，并返回这个新环境
(macro (make-environment form)
     `(apply (lambda ()
               ,@(cdr form)
               (current-environment))))

(define-macro (eval-polymorphic x . envl)
  (display envl)
  (let* ((env (if (null? envl) (current-environment) (eval (car envl))))
         (xval (eval x env)))
    (if (closure? xval)
      (make-closure (get-closure-code xval) env)  ;xval已经是一个closure了，为什么重新生成一个closure ？,难道是因为
												  ;xval可能没绑定到env，所以在这里把这个closure强制绑定到env这个环境上
      xval)))

; Redefine this if you install another package infrastructure
; Also redefine 'package'
(define *colon-hook* eval)

;;;;; I/O
;是不是一个端口？
(define (input-output-port? p)
     (and (input-port? p) (output-port? p)))
;关闭一个端口
(define (close-port p)
     (cond
          ((input-output-port? p) (close-input-port (close-output-port p)))
          ((input-port? p) (close-input-port p))
          ((output-port? p) (close-output-port p))
          (else (throw "Not a port" p))))
;打开s表示的输入端口，将端口做为参数调用p，关闭端口
(define (call-with-input-file s p)
     (let ((inport (open-input-file s)))
          (if (eq? inport #f)
               #f
               (let ((res (p inport)))
                    (close-input-port inport)
                    res))))
;打开s表示的输出端口，将端口做为参数调用p，关闭端口
(define (call-with-output-file s p)
     (let ((outport (open-output-file s)))
          (if (eq? outport #f)
               #f
               (let ((res (p outport)))
                    (close-output-port outport)
                    res))))

(define (with-input-from-file s p)
     (let ((inport (open-input-file s)))
          (if (eq? inport #f)
               #f
               (let ((prev-inport (current-input-port)))
                    (set-input-port inport)
                    (let ((res (p)))
                         (close-input-port inport)
                         (set-input-port prev-inport)
                         res)))))

(define (with-output-to-file s p)
     (let ((outport (open-output-file s)))
          (if (eq? outport #f)
               #f
               (let ((prev-outport (current-output-port)))
                    (set-output-port outport)
                    (let ((res (p)))
                         (close-output-port outport)
                         (set-output-port prev-outport)
                         res)))))

(define (with-input-output-from-to-files si so p)
     (let ((inport (open-input-file si))
           (outport (open-input-file so)))
          (if (not (and inport outport))
               (begin
                    (close-input-port inport)
                    (close-output-port outport)
                    #f)
               (let ((prev-inport (current-input-port))
                     (prev-outport (current-output-port)))
                    (set-input-port inport)
                    (set-output-port outport)
                    (let ((res (p)))
                         (close-input-port inport)
                         (close-output-port outport)
                         (set-input-port prev-inport)
                         (set-output-port prev-outport)
                         res)))))

; Random number generator (maximum cycle)
;生成一个随机数
(define *seed* 1)
(define (random-next)
     (let* ((a 16807) (m 2147483647) (q (quotient m a)) (r (modulo m a)))
          (set! *seed*
               (-   (* a (- *seed*
                         (* (quotient *seed* q) q)))
                    (* (quotient *seed* q) r)))
          (if (< *seed* 0) (set! *seed* (+ *seed* m)))
          *seed*))
;; SRFI-0
;; COND-EXPAND
;; Implemented as a macro
(define *features* '(srfi-0))

;类似cond 
;例子 (cond-expand (#f (+ 1)) (#t (+ 2))) => 2
(define-macro (cond-expand . cond-action-list)
  (cond-expand-runtime cond-action-list))

 ;cond-action-list结构和cond一样，这个函数会返回求值为#t的分支
 ;例子 (cond-expand-runtime '((#f (+ 1)) (#t (+ 2)))) => (begin (+ 2))
(define (cond-expand-runtime cond-action-list)
  (if (null? cond-action-list)
      #t
      (if (cond-eval (caar cond-action-list))
          `(begin ,@(cdar cond-action-list))
          (cond-expand-runtime (cdr cond-action-list)))))

(define (cond-eval-and cond-list)
  (foldr (lambda (x y) (and (cond-eval x) (cond-eval y))) #t cond-list))

(define (cond-eval-or cond-list)
  (foldr (lambda (x y) (or (cond-eval x) (cond-eval y))) #f cond-list))

(define (cond-eval condition)  ;???????
  (cond
    ((symbol? condition)
       (if (member condition *features*) #t #f))
    ((eq? condition #t) #t)
    ((eq? condition #f) #f)
    (else (case (car condition)
            ((and) (cond-eval-and (cdr condition)))
            ((or) (cond-eval-or (cdr condition)))
            ((not) (if (not (null? (cddr condition)))
                     (error "cond-expand : 'not' takes 1 argument")
                     (not (cond-eval (cadr condition)))))
            (else (error "cond-expand : unknown operator" (car condition)))))))

(gc-verbose #f)
