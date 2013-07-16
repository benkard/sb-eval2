(defpackage "SB-EVAL2"
  (:use "COMMON-LISP")
  (:shadow "EVAL" "LOAD")
  (:export "EVAL" "LOAD"))

(in-package "SB-EVAL2")

;;(declaim (optimize (debug 3) (space 0) (speed 0) (safety 3) (compilation-speed 0)))
(declaim (optimize (debug 0) (space 0) (speed 3) (safety 0) (compilation-speed 0)))

(defconstant +stack-max+ 1000)

(defmacro specialize (&environment env var value possible-values &body body)
  `(ecase ,value
     ,@(loop for x in (sb-int:eval-in-lexenv possible-values env)
             collect
                `((,x) ,(sb-int:eval-in-lexenv `(let ((,var ,x)) ,@body) env)))))

(declaim (inline %make-environment))
(defstruct (environment (:constructor %make-environment))
  (parent nil :type (or null environment))
  (data nil :type (or null simple-vector)))

(declaim (inline make-null-environment))
(defun make-null-environment () (make-environment nil 0))

(declaim (inline make-environment))
(defun make-environment (parent
                         &optional (size 0)
                         &aux (data
                               (unless (zerop (the fixnum size))
                                 (make-array
                                  (list size)))))
  (%make-environment :parent parent :data data))

(defmacro with-dynamic-extent-environment ((var parent size) &body body)
  (let ((data% (gensym))
        (size% (gensym)))
    `(let* ((,size% ,size)
            (,data% (make-array (list ,size%)))
            (,var (%make-environment :parent ,parent :data ,data%)))
       (declare (type (mod #.+stack-max+) ,size%)
                (dynamic-extent ,var)
                (dynamic-extent ,data%))
       ,@body)))

(defclass lexical ()
  ((name    :accessor lexical-name    :initarg :name    :type (or symbol list))))

(defclass env-lexical (lexical)
  ((offset  :accessor lexical-offset  :initarg :offset  :type fixnum)
   (nesting :accessor lexical-nesting :initarg :nesting :type fixnum)))

(defun make-env-lexical (name offset &optional (nesting -1))
  (make-instance 'env-lexical :name name :offset offset :nesting nesting))

(defgeneric lexical-with-nesting (lexical nesting))
(defmethod lexical-with-nesting ((lexical env-lexical) nesting)
  (make-env-lexical (lexical-name lexical) (lexical-offset lexical) nesting))

(defun maybe-references-p (form vars)
  ;; Use `(function ,name) for local functions.
  ;;
  ;; FIXME: This doesn't do macro expansion, so it's probably
  ;; incorrect.
  (typecase form
    (symbol
     (member form vars :test #'equal))
    (cons
     (destructuring-bind (a . b) form
       (or (maybe-references-p a vars)
           (maybe-references-p b vars))))
    (t
     nil)))

(defun maybe-closes-over-p (form vars)
  ;; Use `(function ,name) for local functions.
  ;;
  ;; NOTE: This is a *very* simplistic algorithm with a *lot* of false
  ;; positives.
  ;;
  ;; FIXME: This doesn't do macro expansion, so it's probably
  ;; incorrect.
  (typecase form
    (symbol
     nil)
    (cons
     (destructuring-bind (a . b) form
       (case a
         ((lambda)
          (maybe-references-p form vars))
         ((flet labels)
          (typecase b
            (cons
             (destructuring-bind (bindings . rest) form
               (or (maybe-references-p bindings vars)
                   (maybe-closes-over-p rest vars))))
            (t
             (maybe-closes-over-p b vars)))))))
    (t
     nil)))

(defstruct (context (:constructor make-context (&optional parent)))
  parent
  (env-hop nil :type boolean)
  (block-tags nil :type list)
  (go-tags nil :type list)
  (symbol-macros nil :type list)
  (macros nil :type list)
  (lexicals nil :type list))
(defun make-null-context ()
  (make-context nil))
(defun context-add-block-tag (context block tag)
  (let ((new-context (make-context context)))
    (with-slots (block-tags)
        new-context
      (setq block-tags (acons block tag block-tags)))
    new-context))
(defun context-block-tag (context block)
  (let ((parent (context-parent context)))
    (or (cdr (assoc (the symbol block) (context-block-tags context)))
        (and parent (context-block-tag parent block)))))
(defun context-add-go-tags (context new-go-tags catch-tag)
  (let ((new-context (make-context context)))
    (with-slots (go-tags)
        new-context
      (dolist (new-go-tag new-go-tags)
        (setq go-tags (acons new-go-tag catch-tag go-tags))))
    new-context))
(defun context-find-go-tag (context go-tag)
  (let ((parent (context-parent context)))
    (or (cdr (assoc (the symbol go-tag) (context-go-tags context)))
        (and parent (context-find-go-tag parent go-tag)))))
(defun context-find-symbol-macro (context symmac)
  (let ((parent (context-parent context)))
    (or (cdr (assoc (the symbol symmac) (context-symbol-macros context)))
        (and parent (context-find-symbol-macro parent symmac)))))
(defun context-find-macro (context mac)
  (let ((parent (context-parent context)))
    (or (cdr (assoc (the (or symbol list) mac) (context-macros context) :test #'equal))
        (and parent (context-find-macro parent mac)))))
(defun context-add-symbol-macros (context bindings)
  (let ((new-context (make-context context)))
    (with-slots (symbol-macros)
        new-context
      (setq symbol-macros (append bindings symbol-macros)))
    new-context))
(defun context-add-macros (context bindings)
  (let ((new-context (make-context context)))
    (with-slots (macros)
        new-context
      (setq macros (append bindings macros)))
    new-context))
(defun parse-tagbody-tags-and-bodies (forms)
  (let ((next-form (gensym))
        (finishp nil))
    (loop until finishp
          collect
             (let ((tag next-form)
                   (forms (loop until (symbolp (setq next-form (pop forms)))
                                collect next-form)))
               (unless forms
                 (setq finishp t))
               (cons tag forms)))))
(defun context-var-lexical-p (context var)
  (context-find-lexical context var))
(defun context-add-env-lexicals (context vars)
  ;; open a new variable context
    (let ((new-context (make-context context)))
    (with-slots (lexicals env-hop)
        new-context
      (setq env-hop t)
      (setq lexicals (loop for i fixnum from 0
                           for v in vars
                           collect (make-env-lexical v i))))
    new-context))
(defun context-add-env-lexical! (context var)
  ;; open a new variable context
  (with-slots (lexicals)
      context
    (push (make-env-lexical var (length lexicals)) lexicals))
  (values))
(defun context-add-env-functions (context fs)
  (context-add-env-lexicals context (mapcar (lambda (x) `(function ,x)) fs)))
(defun context-find-lexical (context var)
  (loop with env-level = 0
        until (null context)
        for record = (find var
                           (context-lexicals context)
                           :key #'lexical-name
                           :test #'equal)
        when record
          do (return
               (etypecase record
                 (env-lexical   (lexical-with-nesting record env-level))))
        when (context-env-hop context)
          do (incf env-level)
        do (setq context (context-parent context))))

(deftype eval-closure () `(function (environment) *))

(declaim (inline environment-value))
(defun environment-value (env nesting offset)
  (dotimes (i (the fixnum nesting))
    (setq env (environment-parent env)))
  (svref (environment-data env) offset))

(declaim (inline (setf environment-value)))
(defun (setf environment-value) (val env nesting offset)
  (dotimes (i (the fixnum nesting))
    (setq env (environment-parent env)))
  (setf (svref (environment-data env) offset) val))

(declaim (ftype (function (symbol context) eval-closure) prepare-ref))
(defun prepare-ref (var context)
  (if (context-var-lexical-p context var)
      (let* ((lexical (context-find-lexical context var))
             (nesting (lexical-nesting lexical))
             (offset (lexical-offset lexical)))
        (etypecase lexical
          (env-lexical
           (lambda (env)
             (environment-value env nesting offset)))))
      (lambda (env)
        (declare (ignore env))
        (symbol-value var))))

(declaim (ftype (function ((or symbol list) context) eval-closure) prepare-function-ref))
(defun prepare-function-ref (function-name context)
  (if (context-var-lexical-p context `(function ,function-name))
      (let* ((lexical (context-find-lexical context `(function ,function-name)))
             (nesting (lexical-nesting lexical))
             (offset  (lexical-offset lexical)))
        (lambda (env)
          (environment-value env nesting offset)))
      (lambda (env)
        (declare (ignore env))
        (fdefinition function-name))))



(declaim (ftype (function (context (or symbol list)) *) context-find-function))
(defun context-find-function (context f)
  (context-find-lexical context `(function ,f)))

(declaim (ftype (function (context (or symbol list)) *) local-function-p))
(defun local-function-p (context f)
  (context-find-function context f))

(declaim (ftype (function () eval-closure) prepare-nil))
(defun prepare-nil ()
  (lambda (env) (declare (ignore env))))

(declaim (ftype (function ((or symbol list) list context) eval-closure) prepare-local-call))
(defun prepare-local-call (f args context)
  (let* ((args* (mapcar (lambda (form) (prepare-form form context)) args))
         (flex (context-find-function context f))
         (offset (lexical-offset flex))
         (nesting (lexical-nesting flex)))
    (if (< (length args) 20)
        (specialize m% (length args) (loop for i from 0 below 20 collect i)
          (let ((argvars (loop for i from 0 below m%
                               collect (gensym (format nil "ARG~D-" i)))))
            `(let ,(loop for var in argvars
                         for i from 0 below m%
                         collect `(,var (nth ,i args*)))
               (lambda (env)
                 (funcall (the function (environment-value env nesting offset))
                          ,@(loop for var in argvars
                                  collect `(funcall (the eval-closure ,var) env)))))))
        (lambda (env)
          (apply (the function (environment-value env nesting offset))
                 (mapcar (lambda (x) (funcall (the eval-closure x) env)) args*))))))

(declaim (ftype (function ((or symbol list) list context) eval-closure) prepare-global-call))
(defun prepare-global-call (f args context)
  (let ((args* (mapcar (lambda (form) (prepare-form form context)) args))
        (f* (sb-c::fdefinition-object f t)))
    (if (< (length args) 20)
        (specialize m% (length args) (loop for i from 0 below 20 collect i)
          (let ((argvars (loop for i from 0 below m%
                               collect (gensym (format nil "ARG~D-" i)))))
            `(let ,(loop for var in argvars
                         for i from 0 below m%
                         collect `(,var (nth ,i args*)))
               (lambda (env)
                 (declare (ignorable env))
                 (funcall (or (sb-c::fdefn-fun f*)
                              (error 'undefined-function :name f))
                          ,@(loop for var in argvars
                                  collect `(funcall (the eval-closure ,var) env)))))))
        (lambda (env)
          (apply (or (sb-c::fdefn-fun f*)
                     (error 'undefined-function :name f))
                 (mapcar (lambda (x) (funcall (the eval-closure x) env)) args*))))))

(declaim (ftype (function (eval-closure list context) eval-closure) prepare-direct-call))
(defun prepare-direct-call (f args context)
  (let ((args* (mapcar (lambda (form) (prepare-form form context)) args)))
    (lambda (env)
      (apply (the (or symbol function) (funcall (the eval-closure f) env))
             (mapcar (lambda (x) (funcall (the eval-closure x) env)) args*)))))

(declaim (ftype (function (list context) eval-closure) prepare-progn))
(defun prepare-progn (forms context)
  (let ((body* (mapcar (lambda (form) (prepare-form form context)) forms)))
    (lambda (env)
      (let (result)
        (dolist (form* body* result)
          (setq result (funcall (the eval-closure form*) env)))))))

(defun lambda-binding-vars (entry)
  (etypecase entry
    (cons   (list (etypecase (first entry)
                    (cons   (second (first entry)))
                    (symbol (first entry)))
                  (if (cddr entry)
                      (third entry)
                      (gensym))))
    (symbol (list entry (gensym)))))

(defun lambda-binding-main-var (entry)
  (etypecase entry
    (cons   (etypecase (first entry)
              (cons   (second (first entry)))
              (symbol (first entry))))
    (symbol entry)))

(defun lambda-simple-binding-vars (entry)
  (etypecase entry
    (cons   (list (first entry)))
    (symbol (list entry))))

(defun lambda-binding-default (entry)
  (etypecase entry
    (cons   (second entry))
    (symbol nil)))

(defun lambda-key (entry)
  (flet ((keywordify (sym)
           (intern (symbol-name sym) "KEYWORD")))
    (etypecase entry
      (cons   (etypecase (first entry)
                (cons   (first (first entry)))
                (symbol (keywordify (first entry)))))
      (symbol (keywordify entry)))))

(declaim (ftype (function (list context) eval-closure) prepare-lambda))
(defun prepare-lambda (lambda-form context)
  (destructuring-bind (lambda-list &rest body) lambda-form
    ;; FIXME: SPECIAL declarations!
    (multiple-value-bind (required optional restp rest keyp keys allowp auxp aux
                          morep more-context more-count)
        (sb-int:parse-lambda-list lambda-list)
      (declare (ignore more-context more-count))
      (declare (ignorable allowp auxp))
      (when morep
        (error "The interpreter does not support the lambda-list keyword ~D"
               'sb-int:&more))
      (let* ((argvars (append required
                              (mapcan #'lambda-binding-vars optional)
                              (mapcan #'lambda-binding-vars keys)
                              (mapcan #'lambda-simple-binding-vars aux)
                              (and restp (list rest))))
             (keywords (mapcar #'lambda-key keys))
             #+(or) (simplep (not (or optional restp keyp allowp auxp)))
             (required-num (length required))
             (optional-num (length optional))
             (key-num (length keys))
             (aux-num (length aux))
             (varnum (length argvars))
             (envp (or (> varnum +stack-max+)
                       (maybe-closes-over-p `(progn ,@body) argvars)))
             (default-values (append (mapcar #'lambda-binding-default optional)
                                     (mapcar #'lambda-binding-default keys)
                                     (mapcar #'lambda-binding-default aux)))
             (new-context (context-add-env-lexicals context required))
             (default-values*
               (loop for default-value in default-values
                     for binding in (append optional keys aux)
                     for var = (lambda-binding-main-var binding)
                     collect (prepare-form default-value new-context)
                     do (context-add-env-lexical! context var)))
             (body* (prepare-progn body new-context))
             (unbound (gensym)))
        (macrolet ((handle-arguments (args env)
                     ;; All this ELT and LENGTH stuff is not as
                     ;; inefficient as it looks.  SBCL transforms
                     ;; &rest into &more here.
                     `(let ((rest
                              (when (or restp keyp)
                                (loop for i
                                      from (+ required-num optional-num)
                                      below (length ,args)
                                      collect (elt ,args i)))))
                        (prog ((argi 0)
                               (vari 0))
                           (declare (type fixnum argi vari))
                         positional
                           (when (>= argi (length ,args))
                             (go missing-optionals))
                           (when (>= argi (the fixnum (+ required-num optional-num)))
                             (go keys))
                           (setf (environment-value ,env 0 vari) (elt ,args argi))
                           (when (>= argi required-num)
                             (pop default-values*)
                             (incf vari)
                             (setf (environment-value ,env 0 vari) t))
                           (incf vari)
                           (incf argi)
                           (go positional)
                         missing-optionals
                           (assert (>= argi required-num))
                           (when (>= vari (the fixnum (+ required-num (the fixnum (* 2 optional-num)))))
                             (go keys))
                           (let ((val* (pop default-values*)))
                             (setf (environment-value ,env 0 vari)
                                   (funcall (the eval-closure val*) ,env)
                                   (environment-value ,env 0 (1+ vari))
                                   nil))
                           (incf vari 2)
                           (go missing-optionals)
                         keys
                           (when (>= vari
                                     (the fixnum
                                          (+ required-num (* 2 (+ optional-num key-num)))))
                             (go aux))
                           (let* ((key  (the keyword (pop keywords)))
                                  (val* (pop default-values*))
                                  (x    (getf rest key unbound)))
                             (if (eq unbound x)
                                 (setf (environment-value ,env 0 vari)
                                       (funcall (the eval-closure val*) ,env)
                                       (environment-value ,env 0 (1+ vari))
                                       nil)
                                 (setf (environment-value ,env 0 vari)
                                       x
                                       (environment-value ,env 0 (1+ vari))
                                       t)))
                           (incf vari 2)
                           (go keys)
                         aux
                           (when (>= vari
                                     (the fixnum
                                          (+ required-num
                                             (the fixnum (* 2 (+ optional-num key-num)))
                                             aux-num)))
                             (go rest))
                           (let ((val* (pop default-values*)))
                             (setf (environment-value ,env 0 vari)
                                   (funcall (the eval-closure val*) ,env)))
                           (incf vari)
                           (go aux)
                         rest
                           (assert (null default-values*))
                           (when restp
                             (setf (environment-value ,env 0 (1- varnum))
                                   rest))))))
          (if envp
              (lambda (env)
                (lambda (&rest args)
                  (declare (dynamic-extent args))
                  (let ((new-env (make-environment env varnum)))
                    (handle-arguments args new-env)
                    (funcall body* new-env))))
              (lambda (env)
                (lambda (&rest args)
                  (declare (dynamic-extent args))
                  (with-dynamic-extent-environment (new-env env varnum)
                    (handle-arguments args new-env)
                    (funcall body* new-env))))))))))

(defun context->native-environment (context)
  ;;FIXME
  (declare (ignore context))
  (sb-c::internal-make-lexenv nil nil nil nil nil nil nil nil nil nil nil))

(defun globally-special-p (var)
  (eq :special (sb-int:info :variable :kind var)))

(declaim (ftype (function (* &optional context) eval-closure) prepare-form))
(defun prepare-form (form &optional (context (make-null-context)))
  ;;(declare (optimize speed (safety 0) (space 1) (debug 0)))
  ;;(print form)
  (values
   (cond
     ((sb-int:self-evaluating-p form)
      (lambda (env) (declare (ignore env)) form))
     (t
      (etypecase form
        (symbol
         (let ((macro? (context-find-symbol-macro context form)))
                (if macro?
                    (funcall (the function (cdr macro?)))
                    (prepare-ref form context))))
        (cons
         (case (first form)
           ((if)
            (destructuring-bind (a b &optional c) (rest form)
              (let ((a* (prepare-form a context))
                    (b* (prepare-form b context))
                    (c* (prepare-form c context)))
                (lambda (env) (if (funcall a* env) (funcall b* env) (funcall c* env))))))
           ((function)
            (let ((fun-form (second form)))
              (etypecase fun-form
                (symbol
                 (prepare-function-ref fun-form context))
                (cons
                 (ecase (first fun-form)
                   ((lambda)
                    (prepare-lambda (rest fun-form) context))
                   ((sb-int:named-lambda)
                    (prepare-lambda (cddr fun-form) context))
                   ((setf)
                    (prepare-function-ref fun-form context)))))))
           ((lambda)
            (prepare-lambda (rest form) context))
           ((setq)
            (let ((binding-forms (rest form)))
              (let ((bindings
                      (loop for (var valform) on binding-forms by #'cddr
                            collect var
                            collect (context-find-lexical context var)
                            collect (prepare-form valform context))))
                (lambda (env)
                  (loop for (var lexical? val*) on bindings by #'cdddr
                        for value = (funcall (the eval-closure val*) env)
                        for result =
                           (progn
                             (check-type var symbol)
                             (etypecase lexical?  ; XXX could lift the
                                                  ; case distinction
                                                  ; out of the lambda
                               (env-lexical
                                (setf (environment-value env
                                                         (lexical-nesting lexical?)
                                                         (lexical-offset lexical?))
                                      value))
                               (null
                                (setf (symbol-value var) value))))
                        finally (return result))))))
           ((catch)
            (destructuring-bind (tag &body body) (rest form)
              (let ((tag* (prepare-form tag context))
                    (body* (prepare-progn body context)))
                (lambda (env)
                  (catch (funcall tag* env)
                    (funcall body* env))))))
           ((block)
            (destructuring-bind (name &body body) (rest form)
              (let* ((tag (gensym (concatenate 'string "BLOCK-" (symbol-name name))))
                     (body* (prepare-progn body (context-add-block-tag context name tag))))
                (lambda (env)
                  (catch tag
                    (funcall body* env))))))
           ((declare)
            ;;FIXME
            (prepare-nil))
           ((eval-when)
            (destructuring-bind ((&rest times) &body body) (rest form)
              (if (or (member :load-toplevel times)
                      (member :execute times)
                      (member 'load times)
                      (member 'eval times))
                  (prepare-progn body context)
                  (prepare-nil))))
           ((flet)
            (destructuring-bind (bindings &rest body) (rest form)
              (let* ((bindings* (mapcar (lambda (form)
                                          (if (listp form)
                                              (cons (first form)
                                                    (prepare-lambda (rest form) context))
                                              (cons form (prepare-nil))))
                                        bindings))
                     (new-context (context-add-env-functions context (mapcar #'first bindings*)))
                     (functions (mapcar #'cdr bindings*))
                     (n (length functions))
                     (body* (prepare-progn body new-context)))
                (lambda (env)
                  (let ((new-env (make-environment env n)))
                    (loop for i from 0 to n
                          for f in functions
                          do (setf (environment-value new-env 0 i)
                                   (funcall (the eval-closure f) env)))
                    (funcall body* new-env))))))
           ((labels)
            (destructuring-bind (bindings &rest body) (rest form)
              (let* ((new-context (context-add-env-functions context (mapcar #'first bindings)))
                     (bindings* (mapcar (lambda (form)
                                          (if (listp form)
                                              (cons (first form)
                                                    (prepare-lambda (rest form) new-context))
                                              (cons form (prepare-nil))))
                                        bindings))
                     (functions (mapcar #'cdr bindings*))
                     (n (length functions))
                     (body* (prepare-progn body new-context)))
                (lambda (env)
                  (let ((new-env (make-environment env n)))
                    (loop for i from 0 to n
                          for f in functions
                          do (setf (environment-value new-env 0 i)
                                   (funcall (the eval-closure f) new-env)))
                    (funcall body* new-env))))))
           ((let)
            ;; FIXME: SPECIAL declarations!
            (destructuring-bind (bindings &rest body) (rest form)
              (let* ((real-bindings (mapcar (lambda (form)
                                              (if (listp form)
                                                  (cons (first form) (second form))
                                                  (cons form nil)))
                                            bindings))
                     (vars (mapcar #'car real-bindings))
                     (varnum (length vars))
                     (envp (or (> varnum +stack-max+)
                               (maybe-closes-over-p `(progn ,@body) vars)))
                     (new-context
                       (context-add-env-lexicals context (list)))
                     lexical-values*
                     special-bindings*)
                (loop for (var . value-form) in real-bindings
                      for val* = (prepare-form value-form context)
                      if (globally-special-p var)
                        collect (cons var val*) into specials 
                      else
                        collect val* into lexicals
                        and do (context-add-env-lexical! new-context var)
                      finally
                         (setq lexical-values* lexicals
                               special-bindings* specials))
                (let ((body* (prepare-progn body new-context))
                      (special-vars  (mapcar #'car special-bindings*))
                      (special-vals* (mapcar #'cdr special-bindings*))
                      (n (length (the list lexical-values*))))
                  (if envp
                      (lambda (env)
                        (let ((new-env (make-environment env n)))
                          (loop for i from 0 below n
                                for val* in lexical-values*
                                do (setf (environment-value new-env 0 i)
                                         (funcall (the eval-closure val*) env)))
                          (progv
                              special-vars
                              (loop for val* in special-vals*
                                    collect (funcall (the eval-closure val*) env))
                           (funcall body* new-env))))
                      (lambda (env)
                        (with-dynamic-extent-environment (new-env env n)
                          (loop for i from 0 below n
                                for val* in lexical-values*
                                do (setf (environment-value new-env 0 i)
                                         (funcall (the eval-closure val*) env)))
                          (progv
                              special-vars
                              (loop for val* in special-vals*
                                    collect (funcall (the eval-closure val*) env))
                            (funcall body* new-env)))))))))
           ((let*)
            ;; FIXME: SPECIAL declarations!
            (destructuring-bind (bindings &rest body) (rest form)
              (let* ((real-bindings (mapcar (lambda (form)
                                              (if (listp form)
                                                  (cons (first form) (second form))
                                                  (cons form nil)))
                                            bindings))
                     (vars (mapcar #'car real-bindings))
                     (varnum (length vars))
                     (envp (or (> varnum +stack-max+)
                               (maybe-closes-over-p `(progn ,@body) vars)))
                     (new-context
                       (context-add-env-lexicals context (list)))
                     lexical-values*
                     special-bindings*)
                (loop for (var . value-form) in real-bindings
                      for val* = (prepare-form value-form new-context)
                      if (globally-special-p var)
                        collect (cons var val*) into specials 
                      else
                        collect val* into lexicals
                        and do (context-add-env-lexical! new-context var)
                      finally
                         (setq lexical-values* lexicals
                               special-bindings* specials))
                (let ((body* (prepare-progn body new-context))
                      (special-vars  (mapcar #'car special-bindings*))
                      (special-vals* (mapcar #'cdr special-bindings*))
                      (n (length (the list lexical-values*))))
                  (if envp
                      (lambda (env)
                        (let ((new-env (make-environment env n)))
                          (loop for i from 0 below n
                                for val* in lexical-values*
                                do (setf (environment-value new-env 0 i)
                                         (funcall (the eval-closure val*) new-env)))
                          (progv
                              special-vars
                              (loop for val* in special-vals*
                                    collect (funcall (the eval-closure val*) new-env))
                            (funcall body* new-env))))
                      (lambda (env)
                        (with-dynamic-extent-environment (new-env env n)
                          (loop for i from 0 below n
                                for val* in lexical-values*
                                do (setf (environment-value new-env 0 i)
                                         (funcall (the eval-closure val*) new-env)))
                          (progv
                              special-vars
                              (loop for val* in special-vals*
                                    collect (funcall (the eval-closure val*) new-env))
                            (funcall body* new-env)))))))))
           ((load-time-value)
            (let ((load-form (cadr form)))
              ;; FIXME
              (prepare-form load-form)))
           ((locally)
            (prepare-nil))
           ((multiple-value-call)
            (destructuring-bind (f &rest argforms) (rest form)
              (let ((f* (prepare-form f context))
                    (argforms* (mapcar (lambda (x) (prepare-form x context)) argforms)))
                (lambda (env)
                  (apply f* (mapcan (lambda (arg) (multiple-value-list (funcall (the eval-closure arg) env))) argforms*))))))
           ((multiple-value-prog1)
            (destructuring-bind (values-form &body body) (rest form)
              (let ((values-form* (prepare-form values-form context))
                    (body*        (prepare-progn body context)))
                (lambda (env)
                  (multiple-value-prog1
                      (funcall values-form* env)
                    (funcall body* env))))))
           ((multiple-value-setq)
            (destructuring-bind (vars values-form) (rest form)
              (let ((values-form* (prepare-form values-form context))
                    (lexicals     (mapcar (lambda (v)
                                            (context-find-lexical context v))
                                          vars)))
                (lambda (env)
                  (let* ((values        (multiple-value-list (funcall values-form* env)))
                         (primary-value (first values)))
                    (loop for lexical? in lexicals
                          for value in values
                          for var in vars
                          do (if lexical?
                                 (setf (environment-value env
                                                          (lexical-nesting lexical?)
                                                          (lexical-offset lexical?))
                                       value)
                                 (setf (symbol-value var) value)))
                    primary-value)))))
           ((multiple-value-bind)
            ;; FIXME: SPECIAL declarations!
            (destructuring-bind (vars value-form &body body) (rest form)
              (let* ((value-form* (prepare-form value-form context))
                     (n           (length (the list vars)))
                     (new-context (context-add-env-lexicals context vars))
                     (body*       (prepare-progn body new-context)))
                (lambda (env)
                  (let* ((new-env (make-environment env n))
                         (values  (multiple-value-list (funcall value-form* env))))
                    (dotimes (i n)
                      (setf (environment-value new-env 0 i) (pop values)))
                    (funcall body* new-env))))))
           ((progn)
            (prepare-progn (rest form) context))
           ((progv)
            (destructuring-bind (vals vars &body body) (rest form)
              (let ((vals* (prepare-form vals context))
                    (vars* (prepare-form vars context))
                    (body* (prepare-progn body context)))
                (lambda (env)
                  (progv (funcall vals* env) (funcall vars* env)
                    (funcall body* env))))))
           ((quote)
            (let ((quoted-object (cadr form)))
              (lambda (env)
                (declare (ignore env))
                quoted-object)))
           ((return-from)
            (destructuring-bind (name &optional value) (rest form)
              (let ((value* (prepare-form value context))
                    (tag    (context-block-tag context name)))
                (lambda (env)
                  (throw tag (funcall value* env))))))
           ((the)
            (prepare-form (third form) context))
           ((throw)
            (destructuring-bind (tag result) (rest form)
              (let ((tag*    (prepare-form tag    context))
                    (result* (prepare-form result context)))
                (lambda (env)
                  (throw (funcall tag* env) (funcall result* env))))))
           ((unwind-protect)
            (destructuring-bind (protected &body body) (rest form)
              (let ((protected* (prepare-form  protected context))
                    (body*      (prepare-progn body      context)))
                (lambda (env)
                  (unwind-protect (funcall protected* env)
                    (funcall body* env))))))
           ((sb-ext:truly-the)
            (prepare-form (third form) context))
           ((sb-int:named-lambda)
            (prepare-lambda (cddr form) context))
           ((symbol-macrolet)
            (destructuring-bind (bindings &rest body) (rest form)
              (let ((bindings (mapcar (lambda (form)
                                        (cons (first form) (second form)))
                                      bindings)))
                (prepare-progn body (context-add-symbol-macros context bindings)))))
           ((macrolet)
            ;; FIXME: This doesn't actually work because we disregard
            ;; the lambda list when calling the macro.
            (destructuring-bind (bindings &rest body) (rest form)
              (let ((bindings (mapcar (lambda (form)
                                        (cons (first form)
                                              (funcall
                                               (prepare-lambda (rest form) context)
                                               (make-null-environment))))
                                      bindings)))
                (prepare-progn body (context-add-macros context bindings)))))
           ((go)
            (let* ((go-tag    (second form))
                   (catch-tag (context-find-go-tag context go-tag)))
              (lambda (env)
                (declare (ignore env))
                (throw catch-tag go-tag))))
           ((tagbody)
            ;; 1. set up catch handler
            ;; 2. save go-tag -> tagbody-catch-tag mapping
            (let* ((jump (gensym "JUMP"))
                   (tags-and-bodies (parse-tagbody-tags-and-bodies (rest form)))
                   (new-context (context-add-go-tags context (mapcar #'car tags-and-bodies) jump))
                   (tags-and-bodies* (mapcar (lambda (x)
                                               (destructuring-bind (tag . body) x
                                                 (cons tag (prepare-progn body new-context))))
                                             tags-and-bodies)))
              (lambda (env)
                (block tagbody-loop
                  (let ((code tags-and-bodies*))
                    (loop
                      (setq code
                            (member (catch jump
                                      (dolist (tag-and-body* code)
                                        (funcall (the eval-closure (cdr tag-and-body*))
                                                 env))
                                      (return-from tagbody-loop))
                                    tags-and-bodies*
                                    :key #'car))
                      (unless code
                        (return-from tagbody-loop)))))
                nil)))
           (otherwise
            ;; FIXME: Handle SETF expanders?
            (destructuring-bind (f . args) form
              (check-type f (or list symbol))
              (let ((local-macro? (context-find-macro context f))
                    (global-macro? (macro-function f)))
                (cond
                  (local-macro?
                   (let ((macro-function (cdr local-macro?)))
                     (prepare-form (funcall (the function macro-function)
                                            form
                                            (context->native-environment context))
                                   context)))
                  (global-macro?
                   (prepare-form (funcall global-macro? form (context->native-environment context)) context))
                  ((and (listp f)
                        (listp (first f))
                        (eq 'lambda (first (first f))))
                   (let ((lambda-fn (prepare-lambda (rest (first f)) context)))
                     (prepare-direct-call lambda-fn args context)))
                  (t
                   (if (local-function-p context f)
                       (prepare-local-call f args context)
                       (prepare-global-call f args context))))))))))))
   t))

(defun eval (form)
  (funcall (prepare-form form) (make-null-environment)))


(defun load (filename)
  ;;FIXME: set :LOAD-TOPLEVEL time.
  (let ((eof (gensym)))
    (with-open-file (in filename)
      (loop for form = (read in nil eof nil)
            until (eq form eof)
            do (eval form)))))


#+(or)
(funcall (prepare-form '(funcall
                         (funcall
                          (lambda (x)
                            (lambda (y z)
                              (setq x (+ x (* y z)))
                              x))
                          3)
                         5 7)
                       (make-null-context))
         (make-null-environment))

#+(or)
(funcall (funcall
          (prepare-form
           '(lambda (a b &optional c (d 10 dp) &rest r &key e (f 12 fp) (g 12 gp) &aux (h 1) (i 2))
             (list a b c d dp e f fp g gp r h i)))
          (make-null-environment))
         1 2 3 4 :f 5 :e 6)
;; => (1 2 3 4 T 6 5 T 12 NIL (:F 5 :E 6) 1 2)
